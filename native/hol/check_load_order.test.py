#!/usr/bin/env python3
"""Exercise the actual Model/ISA graph and planted order/unknown-load faults."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument("--root", action="append", type=Path, default=[])
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    repo = here.parents[1]
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    spec = importlib.util.spec_from_file_location("load_order", here / "check_load_order.py")
    assert spec and spec.loader
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    roots = [repo, *args.root]
    source = repo / "native/hol/kernel_library_load.ml"
    good = checker.inspect(source, roots)
    assert good["passed"] and good["model_required"] and not good["unknown_before_marker"]
    abi_source = repo / "native/abi/native_abi_load.ml"
    abi = checker.inspect(abi_source, roots)
    assert abi["passed"] and abi["model_required"]
    basis = repo / "native/abi/native_abi_core_basis.ml"
    text = basis.read_text()
    first = 'needs "native/hol/kernel_source_load.ml";;\n'
    second = 'needs "native/abi/native_abi_contract.ml";;\n'
    assert text.count(first + second) == 1
    wrong = checker.inspect(abi_source, roots, {basis: text.replace(first + second, second + first)})
    assert not wrong["passed"] and not wrong["literal_order_correct"]
    unknown = checker.inspect(abi_source, roots, {basis: "needs (configured_dependency());;\n" + text})
    assert not unknown["passed"] and unknown["literal_order_correct"] and unknown["unknown_before_marker"]
    missing = checker.inspect(abi_source, roots, {basis: text + '\nneeds "missing-load-order-control.ml";;\n'})
    assert not missing["passed"] and missing["literal_order_correct"] and missing["unresolved_literals"]
    native = checker.inspect(repo / "native/driver/component_driver_load.ml", roots)
    assert native["passed"] and not native["model_required"]
    lexical = '''
(* needs "ignored.ml";; (* loadt "nested.ml";; *) *)
let message = "needs \\"string.ml\\";;";;
let term = `needs "term.ml"`;;
needs "a.ml";; loadt "b.ml";; needs (chosen_file());;
'''
    assert checker.load_calls(lexical) == [("needs", "a.ml"), ("loadt", "b.ml"), ("needs", None)]
    result = {"passed": True, "positive": good, "abi_entrypoint": abi, "wrong_order": wrong,
        "unknown_before_marker": unknown, "missing_file": missing, "native_only": native, "lexical_control": True,
        "inputs": {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [here / "check_load_order.py", Path(__file__).resolve(), source, abi_source, basis]}}
    (work / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"load order: {good['files']} files; wrong order, unknown early load and missing file rejected; native-only and lexer controls pass")


if __name__ == "__main__":
    main()
