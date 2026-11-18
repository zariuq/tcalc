#!/usr/bin/env python3
"""Compare the native ABS plan with its HOL data and independent walk models."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--proof-dir", type=Path,
                        help="HOL audit directory containing the complete ABS plan data")
    parser.add_argument("--guard-proof-dir", type=Path,
                        help="Cold qualification directory for ABS_GUARD_DRIVER_X86")
    args = parser.parse_args()
    if not args.proof_dir and not args.guard_proof_dir:
        parser.error("supply a full-plan or admission-prefix proof directory")
    repo = Path(__file__).resolve().parents[2]
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    proved_plan = None
    program_source = repo / "native/hol/tables_abs_program.ml"
    if args.proof_dir:
        proof = args.proof_dir.resolve()
        receipt = json.loads((proof / "result.json").read_text())
        assert receipt["passed"] and receipt["actual_exit"] == 0
        log = re.sub(r"\x1b\[[0-9;]*m", "", (proof / "hol.log").read_text())
        declaration = log.split("val pl_plan_abs : thm =",1)[1].split("val ABS_PLAN_LENGTH",1)[0]
        proved_plan = list(map(int, re.findall(r"\bword (\d+)", declaration)))
        assert len(proved_plan) == 16 * 18
        source_md5 = hashlib.md5(program_source.read_bytes()).hexdigest()
        assert re.search(r" INPUT " + source_md5 + r" (?:[^\n]*/)?tables_abs_program\.ml$", log, re.M)

    def run(label: str, command: list[str | Path], expected: int = 0) -> str:
        result = subprocess.run(list(map(str, command)), cwd=repo, capture_output=True, text=True)
        output = result.stdout + result.stderr
        (work / (label + ".log")).write_text(output)
        assert result.returncode == expected, (label, result.returncode, output[-2000:])
        return output

    images = {}
    image_files = {
        "abs_intern16": "native/intern/intern16.hol",
        "abs_pack": "native/leaves/pack/pack.hol",
        "abs_eqw": "native/leaves/eqw/eqw.hol",
        "abs_row_word": "native/leaves/row_word/row_word.hol",
        "abs_live": "native/leaves/live/live.hol",
        "abs_append_row": "native/leaves/append_row/append_row.hol",
        "abs_bind_walk": "native/walks/bind_walk.hol",
    }
    assembly = []
    for symbol, relative in image_files.items():
        encoded = re.findall(r'"([0-9a-f]{64,})"', (repo / relative).read_text())
        assert len(encoded) == 1, relative
        data = bytes.fromhex(encoded[0])
        images[symbol] = data
        binary = work / (symbol + ".bin")
        binary.write_bytes(data)
        assembly += [".text", ".p2align 4", ".globl " + symbol,
            ".type " + symbol + ", @function", symbol + ":",
            '.incbin "' + str(binary) + '"', ".size " + symbol + ", .-" + symbol]
    assembly += ['.section .note.GNU-stack,"",@progbits']
    asm = work / "images.S"
    asm.write_text("\n".join(assembly) + "\n")
    source = repo / "native/checker/test_abs_plan.c"
    options = ["gcc", "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror",
        "-I", repo / "native/abi/generated", "-I", repo / "native/driver", "-I", repo / "tisa"]
    executable = work / "abs-plan"
    run("build", options + [source, repo / "native/driver/driver.S", asm, "-o", executable])
    actual_plan = list(map(int, run("plan-data", [executable, "--dump-plan"]).split()))
    if proved_plan is not None:
        assert actual_plan == proved_plan, "native plan differs from HOL term"
    guard_inputs = []
    if args.guard_proof_dir:
        guard_receipt = json.loads((args.guard_proof_dir / "result.json").read_text())
        assert guard_receipt["passed"] and not guard_receipt["actual_exit"]
        assert guard_receipt["source_unchanged"] and guard_receipt["loaded_inputs_checked"]
        assert "ABS_GUARD_DRIVER_X86" in guard_receipt["required_theorems"]
        raw_log = (args.guard_proof_dir / "hol.log").read_bytes()
        assert hashlib.sha256(raw_log).hexdigest() == guard_receipt["log_sha256"]
        guard_inputs = [repo / file for file in ["native/hol/tables_abs_guard_native.ml",
            "native/hol/tables_abs_guards.ml", "native/driver/driver.ml",
            image_files["abs_eqw"], image_files["abs_row_word"], image_files["abs_live"]]]
        pins = {Path(path): digest for digest, path in
            (line.split("  ",1) for line in (args.guard_proof_dir / "loaded.sha256").read_text().splitlines())}
        for path in guard_inputs:
            assert pins[path] == hashlib.sha256(path.read_bytes()).hexdigest(), path.name
        guard_log = re.sub(r"\x1b\[[0-9;]*m", "", raw_log.decode(errors="replace"))
        guard_decl = guard_log.split("val pl_abs_guard_plan : thm =",1)[1].split(
            "val PL_ABS_GUARD_RUN",1)[0]
        guard_plan = list(map(int, re.findall(r"\bword (\d+)", guard_decl)))
        assert len(guard_plan) == 4 * 18 and guard_plan == actual_plan[:4 * 18]

    driver = (repo / "native/driver/driver.ml").read_text().split("let drv_mc =", 1)[1]
    literal = driver.split("[", 1)[1].split("];;", 1)[0]
    images["tisa_drive"] = bytes(int(s, 16) for s in re.findall(r"\b0x([0-9a-fA-F]{2})\b", literal))
    symbols = run("symbols", ["nm", "-S", "-n", executable])
    ranges = {}
    for line in symbols.splitlines():
        match = re.fullmatch(r"([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+[A-Za-z]\s+(\w+)", line)
        if match:
            ranges[match[3]] = int(match[1], 16), int(match[2], 16)
    sections = run("sections", ["objdump", "-h", executable])
    section = re.search(r"(?m)^\s*\d+\s+\.text\s+[0-9a-fA-F]+\s+([0-9a-fA-F]+)\s", sections)
    assert section is not None
    base = int(section[1], 16)
    linked = work / "linked-text.bin"
    run("extract", ["objcopy", "--dump-section", ".text=" + str(linked), executable])
    text = linked.read_bytes()
    def check_image_bytes(payload: bytes) -> None:
        for symbol, expected in images.items():
            address, size = ranges[symbol]
            if size != len(expected) or payload[address-base:address-base+size] != expected:
                raise ValueError(symbol)

    check_image_bytes(text)
    changed_byte_controls = {}
    for symbol in ["tisa_drive", "abs_eqw", "abs_row_word", "abs_live", "abs_bind_walk"]:
        damaged = bytearray(text)
        damaged[ranges[symbol][0]-base] ^= 1
        try:
            check_image_bytes(bytes(damaged))
        except ValueError as mismatch:
            assert mismatch.args == (symbol,)
            changed_byte_controls[symbol] = "refused by linked image check"
        else:
            raise AssertionError("changed linked range accepted: " + symbol)

    native = run("native", [executable])
    guard = run("admission", [executable, "--guard-only"])
    mutations = {}
    for mutation, name in enumerate(["binder_guard", "body_binding", "type_constructor",
            "result_type", "publication_order", "work_binding", "row_count_binding"], 1):
        mutant = work / ("mutation-" + name)
        run(name + "-build", options + ["-DABS_MUTATION=" + str(mutation), source,
            repo / "native/driver/driver.S", asm, "-o", mutant])
        mutations[name] = run(name, [mutant], 1).splitlines()[-1]
    guard_mutations = {}
    for mutation, name in enumerate(["binder_live", "body_live", "binder_var"], 1):
        mutant = work / ("guard-mutation-" + name)
        run("guard-" + name + "-build", options + ["-DABS_GUARD_MUTATION=" + str(mutation),
            source, repo / "native/driver/driver.S", asm, "-o", mutant])
        guard_mutations[name] = run("guard-" + name, [mutant,"--guard-only"], 1).strip()

    watched = [source, Path(__file__).resolve(), repo / "native/walks/bind_walk_tests.c",
        repo / "native/driver/driver.S", repo / "native/driver/driver.ml",
        repo / "native/abi/generated/native_abi.h",
        *[repo / f for f in image_files.values()]]
    if proved_plan is not None:
        watched.append(program_source)
    watched.extend(guard_inputs)
    result = {"passed": True, "native": native.strip(), "plan_matches_hol": proved_plan is not None,
        "admission": guard.strip(), "admission_controls": guard_mutations,
        "admission_matches_cold_hol": args.guard_proof_dir is not None,
        "linked_images": {s: {"bytes": len(b), "sha256": hashlib.sha256(b).hexdigest()}
            for s, b in images.items()}, "mutations_caught": mutations,
        "changed_byte_caught": True, "changed_byte_controls": changed_byte_controls,
        "inputs": {str(p.relative_to(repo)): hashlib.sha256(p.read_bytes()).hexdigest() for p in watched},
        "scope": "native integration and negative controls; full ABS record proof remains separate"}
    (work / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(native.strip())
    print(guard.strip())
    print("ABS: eight linked images match; seven plan, three guard and five linked-byte controls caught")


if __name__ == "__main__":
    main()
