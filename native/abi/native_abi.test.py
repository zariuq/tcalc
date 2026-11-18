#!/usr/bin/env python3
"""Qualify module-derived ABI artifacts against real layouts and consumers."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import struct
import subprocess


def nat(value: int) -> str:
    return "(NatZero)" if not value else f"(NatBit (Bit{value & 1}) {nat(value >> 1)})"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--cetta", default="cetta")
    parser.add_argument("--cesta", type=Path, required=True)
    parser.add_argument("--scalars", type=Path, required=True)
    parser.add_argument("--lean-project", type=Path)
    args = parser.parse_args()
    args.cesta = args.cesta.resolve()
    args.scalars = args.scalars.resolve()
    here = Path(__file__).resolve().parent
    repo = here.parents[1]
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    source = here / "NativeInterface.module"
    compiler = here / "native_abi.metta"
    suffixes = [".data", ".h", ".inc", ".ml", ".lean"]

    def run(label: str, command: list[str | Path], ok: bool = True, cwd: Path = repo) -> str:
        result = subprocess.run(list(map(str, command)), cwd=cwd, text=True, capture_output=True)
        output = result.stdout + result.stderr
        (work / (label + ".log")).write_text(output)
        if (result.returncode == 0) != ok:
            raise AssertionError(f"{label}: unexpected exit {result.returncode}\n{output[-3000:]}")
        return output

    def generate(label: str, module: Path, prefix: Path, accepted: bool) -> None:
        # A compiler invocation must return one result. Detect an accidental
        # superposition before it can amplify repeated output effects.
        with (work / (label + ".log")).open("w") as log:
            process = subprocess.Popen([args.cetta, "--no-results", str(compiler), str(module),
                str(args.scalars.resolve()), str(args.cesta.resolve()), str(prefix)], cwd=repo,
                stdout=subprocess.PIPE, stderr=log, text=True)
            lines: list[str] = []
            depth, roots = 0, 0
            quoted, escaped = False, False
            try:
                assert process.stdout is not None
                for line in process.stdout:
                    log.write(line)
                    lines.append(line)
                    for char in line:
                        if quoted:
                            if escaped:
                                escaped = False
                            elif char == "\\":
                                escaped = True
                            elif char == '"':
                                quoted = False
                        elif char == '"':
                            quoted = True
                        elif char == "(":
                            if depth == 0:
                                roots += 1
                            depth += 1
                        elif char == ")":
                            depth -= 1
                        if roots > 1:
                            raise AssertionError(label + ": generator returned multiple results")
                status = process.wait()
            finally:
                if process.poll() is None:
                    process.terminate()
                    process.wait()
            output = "".join(lines).strip()
            assert status == 0 and roots == 1 and depth == 0 and not quoted, label
            expected = "(ABIGenerated " if accepted else "(ABIRefused "
            assert output.startswith(expected), (label, output[:1000])

    prefix = work / "native_abi"
    generate("generate", source, prefix, True)
    snapshots = {suffix: prefix.with_suffix(suffix).read_bytes() for suffix in suffixes}
    generate("regenerate", source, prefix, True)
    assert all(prefix.with_suffix(suffix).read_bytes() == data for suffix, data in snapshots.items())
    assert not prefix.with_suffix(".pending.data").exists()
    run("tables", [args.cesta, "tables", "check", prefix.with_suffix(".data")])

    probe = work / "layout.c"
    probe.write_text('#include <native_abi.h>\nint main(void) { return 0; }\n')
    for cc in ["gcc", "clang"]:
        binary = work / ("layout-" + cc)
        run(cc, [cc, "-std=c11", "-Wall", "-Wextra", "-Werror", "-I", repo / "tisa",
                 "-I", work, probe, "-o", binary])
        run(cc + "-run", [binary])

    table = prefix.with_suffix(".data").read_text()
    constants = {key: int(value) for key, value in re.findall(r"\(Row ([A-Za-z_][A-Za-z_0-9]*) ([0-9]+)\)", table)}
    fields = [(record, key, int(slot)) for record, key, slot in
              re.findall(r"\(Row ([A-Za-z_][A-Za-z_0-9]*) ([A-Za-z_][A-Za-z_0-9]*) ([0-9]+)\)", table)]
    symbols = [("TISA_ABI_" + key, value) for key, value in constants.items()]
    symbols += [("TISA_ABI_" + record + "_" + key + "_OFFSET", constants["WordBytes"] * slot)
                for record, key, slot in fields]
    assembly = work / "constants.S"
    include = str(prefix.with_suffix(".inc")).replace("\\", "\\\\").replace('"', '\\"')
    assembly.write_text(f'.include "{include}"\n.section .rodata\n' +
                        "".join(".quad " + name + "\n" for name, _ in symbols))
    run("assemble", ["gcc", "-c", assembly, "-o", work / "constants.o"])
    run("extract", ["objcopy", "-O", "binary", "--only-section=.rodata", work / "constants.o", work / "constants.bin"])
    assert (work / "constants.bin").read_bytes() == b"".join(struct.pack("<Q", value) for _, value in symbols)

    text = source.read_text()
    old = f"(ABIConstant (Name_FrameBytes) {nat(192)})"
    assert text.count(old) == 1
    refusals = {
        "overflow": text.replace(old, f"(ABIConstant (Name_FrameBytes) {nat(2**32)})"),
        "noncanonical": text.replace(old, '(ABIConstant (Name_FrameBytes) (NatBit (Bit0) (NatZero)))'),
        "duplicate_field": text.replace('(ABIField (Record_RuntimeFrame) (Name_ret_val)',
                                         '(ABIField (Record_RuntimeFrame) (Name_status)'),
    }
    for name, mutated in refusals.items():
        module = work / (name + ".module")
        module.write_text(mutated)
        generate(name, module, prefix, False)
        assert all(prefix.with_suffix(suffix).read_bytes() == data for suffix, data in snapshots.items()), name

    wrong = text.replace(f"(ABIField (Record_RuntimeFrame) (Name_status) {nat(18)})",
                         f"(ABIField (Record_RuntimeFrame) (Name_status) {nat(19)})")
    wrong = wrong.replace(f"(ABIField (Record_RuntimeFrame) (Name_ret_val) {nat(19)})",
                          f"(ABIField (Record_RuntimeFrame) (Name_ret_val) {nat(18)})")
    assert wrong != text
    bad = work / "wrong_layout"
    bad.mkdir()
    module = bad / "NativeInterface.module"
    module.write_text(wrong)
    generate("wrong_layout_generate", module, bad / "native_abi", True)
    run("wrong_layout_c", ["gcc", "-std=c11", "-I", repo / "tisa", "-I", bad,
        probe, "-o", bad / "should_not_build"], ok=False)

    lean_status = "not-requested"
    if args.lean_project:
        proof = '''
namespace NativeABIQualification
open Mettapedia.Machines.TIsa
 theorem runtimeFrame_exact : TIsa.NativeABI.RuntimeFrameLayout = frameLayout := by decide
 theorem runtimeFrame_admitted : TIsa.NativeABI.RuntimeFrameLayout.admitted := by
  rw [runtimeFrame_exact]
  exact frameLayout.check_iff.mp frameLayout_checked
#print axioms runtimeFrame_exact
#print axioms runtimeFrame_admitted
end NativeABIQualification
'''
        consumer = work / "ABIConsumer.lean"
        consumer.write_text(prefix.with_suffix(".lean").read_text() + proof)
        good_log = run("lean", ["lake", "env", "lean", consumer], cwd=args.lean_project.resolve())
        assert "sorryAx" not in good_log and "warning:" not in good_log.lower()
        wrong_consumer = bad / "ABIConsumer.lean"
        wrong_consumer.write_text((bad / "native_abi.lean").read_text() + proof)
        run("wrong_layout_lean", ["lake", "env", "lean", wrong_consumer], ok=False,
            cwd=args.lean_project.resolve())
        lean_status = "passed; wrong-layout declaration rejected"

    watched = [source, compiler, here / "native_abi.test.py", args.scalars.resolve(), args.cesta.resolve()]
    result = {"passed": True, "entries": len(constants) + len(fields), "runtime_fields": sum(record == "RuntimeFrame" for record, _, _ in fields),
              "assembler_values": len(symbols), "refusals_preserving_outputs": list(refusals),
              "wrong_layout_caught": True, "lean": lean_status,
              "inputs": {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in watched},
              "artifacts": {suffix: hashlib.sha256(data).hexdigest() for suffix, data in snapshots.items()}}
    (work / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"native ABI: {result['entries']} entries; GCC, Clang, assembler; {len(refusals)} refusals; wrong-layout control")


if __name__ == "__main__":
    main()
