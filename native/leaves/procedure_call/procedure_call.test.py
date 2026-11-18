#!/usr/bin/env python3
"""Check call capture through emitted bytes, the real driver and mutations."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--cetta", default="cetta")
    parser.add_argument("--p1run", type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    repo = here.parents[2]
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    runner = (args.p1run or repo / "native/p1/build/p1run").resolve()

    def run(label: str, command: list[str | Path], status: int = 0) -> str:
        result = subprocess.run(list(map(str, command)), cwd=repo, text=True, capture_output=True)
        output = result.stdout + result.stderr
        (work / (label + ".log")).write_text(output)
        if result.returncode != status:
            raise AssertionError(f"{label}: exit {result.returncode}, expected {status}\n{output[-3000:]}")
        return output

    program = work / "procedure_call_prog.txt"
    declaration = work / "procedure_call_program.ml"
    run("author", [args.cetta, "--no-results", here / "procedure_call.metta", program,
                   work / "notes", declaration])
    assert program.read_bytes() == (here / program.name).read_bytes()
    assert declaration.read_bytes() == (here / declaration.name).read_bytes()

    lines: list[str] = []
    edges = [0, 1, 2**32, 2**63, 2**64-1]
    count = 0
    for length in [0, 7, 56, 63, 64, 72, 128]:
        for i in range(5):
            values = [edges[(i + j) % 5] for j in range(7)]
            for target in [0, 1, 7, 31]:
                lines += [f"case capture_{count}", f"region 0 {length}", f"region 8 {target}",
                          f"arg0 {values[0]}", f"arg1 {values[1]}", "budget 0", "used 0"]
                lines += [f"reg {j-1} {values[j]}" for j in range(2, 7)]
                if length >= 64:
                    lines += ["expect UNSUPPORTED 0"]
                    lines += [f"want 0 {8*j} {value}" for j, value in enumerate(values + [target])]
                else:
                    lines += ["expect INVALID 3"]
                lines += ["run"]
                count += 1
    fixtures = work / "capture.p1t"
    fixtures.write_text("\n".join(lines) + "\n")
    image = work / "procedure_call.hol"
    differential = run("differential", [runner, "--quiet", "--image", image, "procedure_call_marker",
                                       program, fixtures])
    assert image.read_bytes() == (here / image.name).read_bytes()

    def native(label: str, image_file: Path, status: int) -> str:
        text = image_file.read_text()
        encoded = re.findall(r'"([0-9a-f]{64,})"', text)
        assert len(encoded) == 1
        blob = work / (label + ".bin")
        blob.write_bytes(bytes.fromhex(encoded[0]))
        assembly = work / (label + ".S")
        path = str(blob).replace("\\", "\\\\").replace('"', '\\"')
        assembly.write_text('.text\n.globl procedure_call_image, procedure_call_image_end\n'
            'procedure_call_image:\n.incbin "' + path + '"\nprocedure_call_image_end:\n'
            '.section .note.GNU-stack,"",@progbits\n')
        binary = work / (label + "-driver")
        run(label + "-build", ["gcc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2",
            "-I", repo / "tisa", "-I", repo / "native/driver", "-I", repo / "native/abi/generated",
            here / "test_call_capture.c", repo / "native/driver/driver.S", assembly, "-o", binary])
        symbols = run(label + "-symbols", ["nm", "-n", binary])
        locations = {name: int(address, 16) for address, name in
            re.findall(r"(?m)^([0-9a-fA-F]+)\s+[A-Za-z]\s+(procedure_call_image(?:_end)?)$", symbols)}
        sections = run(label + "-sections", ["objdump", "-h", binary])
        section = re.search(r"(?m)^\s*\d+\s+\.text\s+[0-9a-fA-F]+\s+([0-9a-fA-F]+)\s", sections)
        assert section is not None
        base = int(section[1], 16)
        linked = work / (label + "-text.bin")
        run(label + "-extract", ["objcopy", "--dump-section", ".text=" + str(linked), binary])
        start, stop = locations["procedure_call_image"], locations["procedure_call_image_end"]
        assert linked.read_bytes()[start-base:stop-base] == blob.read_bytes(), label + ": linked bytes changed"
        return run(label, [binary], status)

    driver = native("capture", image, 0)
    source = program.read_text()
    mutations = {
        "omitted_first_argument": ("(TInstr (TStore 8 0 6 (&0:int) 7))", "TSkip"),
        "wrong_hot_argument": ("TStore 8 0 6 (&16:int) 1", "TStore 8 0 6 (&16:int) 2"),
        "wrong_target_word": ("TLoadFrame TyU64 8 17", "TLoadFrame TyU64 8 16"),
        "yield_as_guard": ("TReturn 2 7", "TReturn 0 7"),
    }
    caught = {}
    for name, (old, new) in mutations.items():
        assert source.count(old) == 1, (name, old)
        mutant = work / (name + ".txt")
        mutant.write_text(source.replace(old, new))
        mutant_image = work / (name + ".hol")
        run(name + "-image", [runner, "--quiet", "--image", mutant_image, "procedure_call_marker", mutant])
        output = native(name, mutant_image, 1)
        assert "failures" in output
        caught[name] = output.splitlines()[-1]

    watched = [here / name for name in ["procedure_call.metta", "procedure_call_prog.txt",
        "procedure_call_program.ml", "procedure_call.hol", "procedure_call.test.py", "test_call_capture.c"]]
    result = {"passed": True, "differential_runs": count, "driver_runs": 512*7,
        "image_bytes": len(bytes.fromhex(re.findall(r'"([0-9a-f]{64,})"', image.read_text())[0])),
        "differential": differential.splitlines()[-1], "driver": driver.splitlines()[-1],
        "mutations_caught": caught,
        "inputs": {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in watched}}
    (work / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"call marker: {count} differential runs; {512*7} driver runs; {len(caught)} mutations caught")


if __name__ == "__main__":
    main()
