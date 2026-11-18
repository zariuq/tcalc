#!/usr/bin/env python3
"""Exercise unsigned relation masks and executed source mutations."""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import subprocess


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--cetta", default="cetta")
    parser.add_argument("--p1run", type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    repo = here.parents[2]
    runner = (args.p1run or repo / "native/p1/build/p1run").resolve()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)

    def run(label: str, command: list[str | Path], status: int = 0) -> str:
        result = subprocess.run(list(map(str, command)), cwd=repo, text=True, capture_output=True)
        output = result.stdout + result.stderr
        (work / (label + ".log")).write_text(output)
        if result.returncode != status:
            raise AssertionError(f"{label}: exit {result.returncode}, expected {status}\n{output[-2000:]}")
        return output

    program = work / "relw_prog.txt"
    declaration = work / "relw_program.ml"
    run("author", [args.cetta, "--no-results", here / "relw.metta", program, work / "notes", declaration])
    assert program.read_bytes() == (here / program.name).read_bytes()
    assert declaration.read_bytes() == (here / declaration.name).read_bytes()
    edges = [0, 1, 2, 3, 2**32-1, 2**32, 2**63, 2**64-1]
    masks = list(range(32)) + [2**32, 2**63, 2**64-1]
    lines: list[str] = []
    count = 0
    for a, b, mask in itertools.product(edges, edges, masks):
        bit = 1 if a < b else 2 if a == b else 4
        fired = bool(mask & bit)
        lines += [f"case mask_{count}", f"arg0 {a}", f"arg1 {b}", f"reg 1 {mask}",
                  "budget 0", "used 0", f"expect {'FIRED' if fired else 'REFUSED'} {a if fired else 0}", "run"]
        count += 1
    fixtures = work / "masks.p1t"
    fixtures.write_text("\n".join(lines) + "\n")
    image = work / "relw.hol"
    baseline = run("native", [runner, "--quiet", "--image", image, "relw", program, fixtures])
    assert image.read_bytes() == (here / image.name).read_bytes()
    source = program.read_text()
    mutations = {
        "strictness": ("TCmp CondUlt", "TCmp CondUle"),
        "less_bit": ("TImm TyU64 5 (word 1)", "TImm TyU64 5 (word 2)"),
        "wrong_payload": ("TReturn 1 2", "TReturn 1 3"),
        "guard_as_resource": ("TReturn 0 4", "TReturn 2 4"),
    }
    caught = {}
    for name, (old, new) in mutations.items():
        assert source.count(old) == 1, (name, old)
        mutant = work / (name + ".txt")
        mutant.write_text(source.replace(old, new))
        output = run(name, [runner, "--quiet", mutant, fixtures], 1)
        assert "missed" in output
        caught[name] = output.splitlines()[-1]
    watched = [here / name for name in ["relw.metta", "relw_prog.txt", "relw_program.ml", "relw.hol", "relw.test.py"]]
    result = {"passed": True, "runs": count, "baseline": baseline.splitlines()[-1],
        "mutations_caught": caught,
        "inputs": {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in watched}}
    (work / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"relw: {count} native/reference runs; {len(caught)} mutations caught")


if __name__ == "__main__":
    main()
