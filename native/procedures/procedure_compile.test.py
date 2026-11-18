#!/usr/bin/env python3
"""Qualify MeTTa step outputs, HOL fixture equalities, and exact native images."""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import re
import subprocess


WORD_LIMIT = 2**64
MARKER = "ProcedureCallMarker"


def sequence(xs: list[object], hol: bool = False) -> str:
    return ("[" + ";".join(map(str, xs)) + "]") if hol else ("(" + " ".join(map(str, xs)) + ")")


def operation(op: str, hol: bool = False) -> str:
    return op if op == MARKER else (op if hol else "(" + op + ")")


def operations(xs: list[str], hol: bool = False) -> str:
    return sequence([operation(x, hol) for x in xs], hol)


def reference(cat: list[str], table: list[str], original: int, count: int, st: list[int]) -> list[int] | None:
    if (len(set(cat)) != len(cat) or MARKER in cat or len(set(table)) != len(table)
            or len(st) != 18 or any(not 0 <= x < WORD_LIMIT for x in st)):
        return None
    code = st[0]
    if code > len(cat):
        return None
    op = MARKER if code == len(cat) else cat[code]
    if op not in table:
        return None
    index = table.index(op)
    if op == MARKER:
        if st[1] >= count or original + 4 + 2 * count > WORD_LIMIT:
            return None
        return [index, original] + [original + 2] * 7 + [original + 4 + 2 * st[1]] + st[10:]
    if any(x + 1 >= original for x in st[1:10]):
        return None
    return [index] + st[1:]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--cetta", default="cetta")
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    repo = here.parents[1]
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    watched = [here / name for name in ["procedure_compile.metta", "procedure_compile.test.py",
        "test_procedure_compile.c", "procedure_step_compile.ml", "procedure_call_syntax.ml",
        "procedure_step_compile_controls.ml", "procedure_compile_math_load.ml",
        "procedure_bindings.ml", "procedure_catalog.ml",
        "procedure_operation_names.ml"]]
    watched += [repo / path for path in ["native/driver/driver.S", "native/driver/driver.ml",
        "native/leaves/procedure_call/procedure_call.hol", "native/leaves/relw/relw.hol",
        "native/abi/generated/native_abi.h", "native/driver/cet_profile.h", "tisa/tisa.h"]]
    before = {str(p.relative_to(repo)): hashlib.sha256(p.read_bytes()).hexdigest() for p in watched}

    def run(label: str, command: list[str | Path]) -> str:
        result = subprocess.run(list(map(str, command)), cwd=repo, text=True, capture_output=True)
        output = result.stdout + result.stderr
        (work / (label + ".log")).write_text(output)
        if result.returncode:
            raise AssertionError(f"{label}: exit {result.returncode}\n{output[-3000:]}")
        return output

    catalog = ["ReaderOperation 32", "KernelOperation 32"]
    cases: list[tuple[list[str], list[str], int, int, list[int]]] = []
    native: list[tuple[int, int, int, int]] = []
    for table in itertools.permutations([MARKER, *catalog]):
        for code, target in [(0, 0), (1, 0), (2, 0), (2, 1), (2, 9)]:
            cases.append((catalog, list(table), 18, 10,
                          [code, target] + [0] * 8 + list(range(8, 15)) + [8]))
    base = [0, 0] + [0] * 8 + list(range(8, 15)) + [8]
    table = [MARKER, *catalog]
    for cat, tab, original, count, change in [
        (catalog, table, 18, 10, {0: 3}),
        (catalog, table, 18, 10, {0: 2, 1: 10}),
        (catalog, table, 18, 10, {1: 18}),
        (catalog, table, 18, 10, {1: 17}),
        (catalog, table, 0, 10, {}),
        (catalog, table, WORD_LIMIT, 1, {0: 2}),
        (catalog, table, 18, 0, {0: 2}),
        ([catalog[0], catalog[0]], table, 18, 10, {}),
        ([MARKER], table, 18, 10, {}),
        (catalog, [catalog[0], catalog[0], MARKER], 18, 10, {}),
        (catalog, [MARKER], 18, 10, {}),
        (catalog, catalog, 18, 10, {0: 2}),
        ([], [MARKER], 18, 10, {0: 0, 1: 9}),
    ]:
        st = base.copy()
        for index, value in change.items():
            st[index] = value
        cases.append((cat, tab, original, count, st))
    cases.append((catalog, table, 18, 10, base[:-1]))
    for marker in range(2):
        tab = [MARKER, "KernelOperation 32"] if marker == 0 else ["KernelOperation 32", MARKER]
        for dst in range(8, 15):
            for call in range(2):
                st = [call, 7 if call else 0] + [0] * 8 + list(range(8, 15)) + [dst]
                native.append((len(cases), call, marker, 7 if call else 0))
                cases.append((["KernelOperation 32"], tab, 18, 10, st))

    queries = []
    for cat, tab, original, count, st in cases:
        queries.append(f"(pc:compile-step {operations(cat)} {operations(tab)} {original} {count} {sequence(st)})")
    extra = [
        "(pc:compile-step () (ProcedureCallMarker) 18 1 (0 0 0 0 0 0 0 0 0 0 8 9 10 11 12 13 14 1.0))",
        "(pc:compile-step () (ProcedureCallMarker) 18 1 (0 0 0 0 0 0 0 0 0 0 8 9 10 11 12 13 14 -1))",
        f"(pc:compile-step () (ProcedureCallMarker) 18 1 (0 0 0 0 0 0 0 0 0 0 8 9 10 11 12 13 14 {WORD_LIMIT}))",
        "(pc:compile-step ((KernelOperation 1.0)) (ProcedureCallMarker) 18 1 (0 0 0 0 0 0 0 0 0 0 8 9 10 11 12 13 14 8))",
        "(pc:compile-step unknown (ProcedureCallMarker) 18 1 ())",
        "(pc:compile-step () (ProcedureCallMarker) 18.0 1 ())",
        "(pc:compile-step () (ProcedureCallMarker) 18 1 unknown)",
    ]

    def author(label: str, library: Path) -> list[str]:
        script = work / (label + ".metta")
        script.write_text('!(import! &self "' + str(library) + '")\n' +
            "\n".join(f"!(println! (pc:hol-result {q}))" for q in queries + extra) + "\n")
        output = run(label, [args.cetta, "--no-results", script])
        lines = output.splitlines()
        assert len(lines) == len(queries) + len(extra), (label, len(lines))
        return [json.loads(line) for line in lines]

    emitted = author("author", here / "procedure_compile.metta")
    outputs: list[list[int] | None] = []
    proofs = ['needs "native/procedures/procedure_compile_math_load.ml";;']
    names = []
    for i, ((cat, tab, original, count, st), text) in enumerate(zip(cases, emitted)):
        expected = reference(cat, tab, original, count, st)
        expected_text = "(NONE:(int64 list)option)" if expected is None else (
            "SOME ([" + ";".join("word " + str(n) for n in expected) + "]:int64 list)")
        assert text == expected_text, (i, text, expected_text)
        outputs.append(expected)
        name = f"PROCEDURE_METTA_COMPILE_{i:03}"
        names.append(name)
        proofs.append(f'let {name} = prove\n (`procedure_compile_step {operations(cat, True)} '
            f'{operations(tab, True)} {original} {count} '
            f'(MAP (word:num->int64) {sequence(st, True)}) = {text}`,\n'
            '  PROCEDURE_COMPILE_EXAMPLE_TAC);;')
    assert all(text == "(NONE:(int64 list)option)" for text in emitted[len(cases):])
    (work / "author_equalities.ml").write_text("\n\n".join(proofs) + "\n")
    (work / "required_theorems.json").write_text(json.dumps(names, indent=2) + "\n")

    source = (here / "procedure_compile.metta").read_text()
    mutations = {
        "source_opcode_as_runtime": ("(cons-atom (pc:offset $table $op)", "(cons-atom $opcode"),
        "target_pair_shift": ("($metadata (+ $original (+ 4 (* 2 $target))))",
                              "($metadata (+ $original (+ 6 (* 2 $target))))"),
        "binding_boundary": ("(< (+ 1 (pc:nth $st (+ 1 $r))) $original)",
                              "(<= (+ 1 (pc:nth $st (+ 1 $r))) $original)"),
    }
    caught = {}
    for label, (old, new) in mutations.items():
        assert source.count(old) == 1, label
        mutant = work / (label + "-library.metta")
        mutant.write_text(source.replace(old, new))
        changed = author(label, mutant)
        mismatches = [i for i, (a, b) in enumerate(zip(changed, emitted)) if a != b]
        assert mismatches, label
        caught[label] = mismatches

    rows = []
    for index, call, marker, target in native:
        words = outputs[index]
        assert words is not None
        rows.append("    {{" + ",".join(f"UINT64_C({w})" for w in words)
                    + f"}}, {call}, {marker}, UINT64_C({target})" + "}")
    (work / "compiled_cases.h").write_text("static const CompiledCase compiled_cases[] = {\n"
        + ",\n".join(rows) + "\n};\n")
    images = {}
    assembly = []
    for symbol, path in [("procedure_call_image", repo / "native/leaves/procedure_call/procedure_call.hol"),
                         ("relw_image", repo / "native/leaves/relw/relw.hol")]:
        strings = re.findall(r'"([0-9a-f]{64,})"', path.read_text())
        assert len(strings) == 1
        images[symbol] = bytes.fromhex(strings[0])
        binary = work / (symbol + ".bin")
        binary.write_bytes(images[symbol])
        assembly += [".text", ".p2align 4", ".globl " + symbol, symbol + ":",
                     '.incbin "' + str(binary) + '"', ".globl " + symbol + "_end", symbol + "_end:"]
    assembly += ['.section .note.GNU-stack,"",@progbits']
    image_assembly = work / "images.S"
    image_assembly.write_text("\n".join(assembly) + "\n")
    executable = work / "compiled-steps"
    run("build", ["gcc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2",
        "-I", work, "-I", repo / "tisa", "-I", repo / "native/driver", "-I", repo / "native/abi/generated",
        here / "test_procedure_compile.c", repo / "native/driver/driver.S", image_assembly, "-o", executable])
    symbols = run("symbols", ["nm", "-S", "-n", executable])
    locations = {}
    sizes = {}
    for line in symbols.splitlines():
        match = re.fullmatch(r"([0-9a-fA-F]+)\s+(?:([0-9a-fA-F]+)\s+)?[A-Za-z]\s+(\w+)", line)
        if match:
            locations[match[3]] = int(match[1], 16)
            if match[2]:
                sizes[match[3]] = int(match[2], 16)
    sections = run("sections", ["objdump", "-h", executable])
    section = re.search(r"(?m)^\s*\d+\s+\.text\s+[0-9a-fA-F]+\s+([0-9a-fA-F]+)\s", sections)
    assert section is not None
    base_address = int(section[1], 16)
    linked = work / "linked-text.bin"
    run("extract", ["objcopy", "--dump-section", ".text=" + str(linked), executable])
    driver_text = (repo / "native/driver/driver.ml").read_text()
    driver_literal = driver_text.split('let drv_mc =', 1)[1].split("[", 1)[1].split("];;", 1)[0]
    images["tisa_drive"] = bytes(int(byte, 16) for byte in re.findall(r"\b0x([0-9a-fA-F]{2})\b", driver_literal))
    byte_receipts = {}
    for symbol, image in images.items():
        start = locations[symbol] - base_address
        size = sizes[symbol] if symbol == "tisa_drive" else locations[symbol + "_end"] - locations[symbol]
        assert size == len(image) and linked.read_bytes()[start:start + size] == image, symbol
        byte_receipts[symbol] = {"bytes": size, "sha256": hashlib.sha256(image).hexdigest()}
    native_output = run("native", [executable])
    after = {str(p.relative_to(repo)): hashlib.sha256(p.read_bytes()).hexdigest() for p in watched}
    assert before == after, "sources changed during qualification"
    receipt = {"passed": True, "metta_hol_fixtures": len(cases), "ill_typed_controls": len(extra),
        "native_plans": len(native), "native_runs": len(native) * 64, "native": native_output.strip(),
        "author_mutations_caught": caught, "linked_images": byte_receipts, "inputs": before,
        "proof_status": "author_equalities.ml emitted; a separate cold HOL run is required"}
    (work / "result.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"procedure compiler: {len(cases)} emitted HOL fixtures, {len(extra)} ill-typed controls, "
          f"{len(native)*64} native runs, {len(caught)} author mutations caught; HOL replay required")


if __name__ == "__main__":
    main()
