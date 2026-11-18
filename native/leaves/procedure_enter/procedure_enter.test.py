#!/usr/bin/env python3
"""Exercise procedure activation boundaries and executed source mutations."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import subprocess


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--cetta", default="cetta")
    parser.add_argument("--p1run", type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    repo = here.parents[2]
    runner = (args.p1run or repo / "native/p1/build/p1run").resolve()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)

    def execute(label: str, command: list[str | Path], expected: int = 0) -> str:
        result = subprocess.run(list(map(str, command)), cwd=repo,
                                text=True, capture_output=True)
        text = result.stdout + result.stderr
        (work / (label + ".log")).write_text(text)
        if result.returncode != expected:
            raise AssertionError(f"{label}: exit {result.returncode}, expected {expected}\n{text[-3000:]}")
        return text

    generated = work / "procedure_enter_prog.txt"
    declaration = work / "procedure_enter_program.ml"
    execute("author", [args.cetta, "--no-results", here / "procedure_enter.metta",
                       generated, work / "notes", declaration])
    assert generated.read_bytes() == (here / generated.name).read_bytes()
    assert declaration.read_bytes() == (here / declaration.name).read_bytes()

    edge = [0, 1, 2, 3, 2**32 - 1, 2**63, 2**64 - 2, 2**64 - 1]
    lines: list[str] = []
    counts = {name: 0 for name in ["FIRED", "UNSUPPORTED", "INVALID", "EXHAUSTED"]}
    for number, (depth, capacity, budget, used) in enumerate(itertools.product(edge, repeat=4)):
        if used > budget:
            outcome, value = "INVALID", 3
        elif depth >= capacity:
            outcome, value = "UNSUPPORTED", 0
        elif used == budget:
            outcome, value = "EXHAUSTED", 4
        else:
            outcome, value = "FIRED", depth + 1
        counts[outcome] += 1
        lines.extend([f"case edge_{number}", f"arg0 {depth}", f"arg1 {capacity}",
                      f"budget {budget}", f"used {used}", f"expect {outcome} {value}", "run"])

    # Each second call observes the receipt left by the first. These controls
    # distinguish a missing charge and a charge made before a stack refusal.
    lines.extend([
        "case charged_once chain", "budget 1", "used 0", "arg0 0", "arg1 1",
        "expect FIRED 1", "run", "expect EXHAUSTED 4", "run",
        "case full_stack_keeps_fuel chain", "budget 1", "used 0", "arg0 1", "arg1 1",
        "expect UNSUPPORTED 0", "run", "arg0 0", "expect FIRED 1", "run",
        "expect EXHAUSTED 4", "run",
        "case last_receipt chain", f"budget {2**64-1}", f"used {2**64-2}",
        f"arg0 {2**64-2}", f"arg1 {2**64-1}", f"expect FIRED {2**64-1}", "run",
        "expect EXHAUSTED 4", "run",
    ])
    fixtures = work / "boundaries.p1t"
    fixtures.write_text("\n".join(lines) + "\n")
    image = work / "procedure_enter.hol"
    baseline = execute("native", [runner, "--quiet", "--image", image, "procedure_enter",
                                  generated, fixtures])
    assert image.read_bytes() == (here / image.name).read_bytes()

    source = generated.read_text()
    mutations = {
        "omitted_charge": ("(TFund 1)", "TSkip"),
        "double_charge": ("(TFund 1)", "(TFund 2)"),
        "full_stack_admitted": ("TCmp CondUlt", "TCmp CondUle"),
        "wrong_next_depth": ("TBin BinAdd", "TBin BinSub"),
        "resource_as_guard": ("TReturn 2 3", "TReturn 0 3"),
    }
    caught = {}
    for name, (old, new) in mutations.items():
        assert source.count(old) == 1, (name, old)
        program = work / (name + ".txt")
        program.write_text(source.replace(old, new))
        output = execute(name, [runner, "--quiet", program, fixtures], expected=1)
        assert "missed" in output
        caught[name] = output.splitlines()[-1]

    prefix = "(TProg [] [] "
    compact = source.strip()
    assert compact.startswith(prefix) and compact.endswith(")")
    body = compact[len(prefix):-1].replace("(TFund 1)", "TSkip")
    early = work / "charge_before_capacity.txt"
    early.write_text(prefix + "(TSeq (TFund 1) " + body + "))\n")
    output = execute("charge_before_capacity", [runner, "--quiet", early, fixtures], expected=1)
    assert "missed" in output
    caught["charge_before_capacity"] = output.splitlines()[-1]

    watched = [here / name for name in ["procedure_enter.metta", "procedure_enter_prog.txt",
                                       "procedure_enter_program.ml", "procedure_enter.hol",
                                       "procedure_enter.test.py"]]
    result = {
        "passed": True, "edge_runs": len(edge)**4, "chained_runs": 7,
        "edge_outcomes": counts, "baseline": baseline.splitlines()[-1],
        "mutations_caught": caught,
        "inputs": {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in watched},
        "boundary": "Invalid-receipt cases exercise the entry validator; the assembly theorem assumes admitted entry.",
    }
    (work / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"procedure_enter: {len(edge)**4 + 7} native/reference runs; {len(caught)} executed mutations caught")


if __name__ == "__main__":
    main()
