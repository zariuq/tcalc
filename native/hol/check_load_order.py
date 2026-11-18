#!/usr/bin/env python3
"""Check literal HOL dependencies for the Model-before-ISA loading barrier.

This checks dependency order, not OCaml names, tactic validity or proof results.
Computed loads are reported separately. Acceptance still requires a cold HOL run.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re


def load_calls(source: str) -> list[tuple[str, str | None]]:
    """Find needs/loadt tokens outside comments, strings and HOL quotations."""
    tokens: list[tuple[str, str | None]] = []
    i, n = 0, len(source)
    while i < n:
        if source.startswith("(*", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if source.startswith("(*", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("*)", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        elif source[i] == '"':
            start, i = i, i + 1
            escaped = False
            while i < n:
                char, i = source[i], i + 1
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    break
            raw = source[start:i]
            try:
                value = json.loads(raw)
            except ValueError:
                value = None
            tokens.append(("string", value))
        elif source[i] == "`":
            i += 1
            while i < n and source[i] != "`":
                i += 1
            i += i < n
        elif source[i].isalpha() or source[i] == "_":
            match = re.match(r"[A-Za-z_][A-Za-z_0-9']*", source[i:])
            assert match is not None
            tokens.append(("name", match[0]))
            i += len(match[0])
        elif not source[i].isspace():
            tokens.append(("punctuation", source[i]))
            i += 1
        else:
            i += 1
    calls = []
    for index, (kind, value) in enumerate(tokens):
        if kind != "name" or value not in {"needs", "loadt"}:
            continue
        following = tokens[index + 1] if index + 1 < len(tokens) else None
        literal = following[1] if following and following[0] == "string" else None
        calls.append((value, literal))
    return calls


def inspect(source: Path, roots: list[Path], overrides: dict[Path, str] | None = None) -> dict:
    source = source.resolve()
    roots = [root.resolve() for root in roots]
    overrides = {path.resolve(): text for path, text in (overrides or {}).items()}
    entered: list[Path] = []
    seen: set[Path] = set()
    dynamic: list[str] = []
    missing: list[dict] = []
    unresolved_before_marker: list[str] = []
    marker, first_isa = None, None

    def visit(path: Path) -> None:
        nonlocal marker, first_isa
        if path in seen:
            return
        seen.add(path)
        entered.append(path)
        if path.name == "model_on_s2n.ml" and marker is None:
            marker = len(entered) - 1
        if ("tisa/hol/" in path.as_posix() or "x86/proofs/" in path.as_posix()) and first_isa is None:
            first_isa = len(entered) - 1
        text = overrides[path] if path in overrides else path.read_text()
        for _, dependency in load_calls(text):
            if dependency is None:
                dynamic.append(str(path))
                if marker is None:
                    unresolved_before_marker.append(str(path))
                continue
            candidates = [Path(dependency)] if Path(dependency).is_absolute() else [root / dependency for root in roots]
            found = next((candidate.resolve() for candidate in candidates if candidate.is_file()), None)
            if found is None:
                missing.append({"source": str(path), "dependency": dependency})
                if marker is None:
                    unresolved_before_marker.append(str(path))
            else:
                visit(found)

    visit(source)
    model_required = any(path.name in {"kernel_source_load.ml", "model_world_load.ml", "model_on_s2n.ml"}
                         for path in entered)
    ordered = not model_required or (marker is not None and (first_isa is None or marker < first_isa))
    # Unknown earlier edges may introduce ISA constants, so do not report a
    # checked Model barrier for them. Unknown dependencies after the marker
    # cannot reverse an ordering already established by the literal graph.
    complete_barrier = not model_required or not unresolved_before_marker
    return {"passed": bool(ordered and complete_barrier and not missing), "literal_order_correct": bool(ordered),
        "model_required": model_required, "files": len(entered),
        "model_marker": str(entered[marker]) if marker is not None else None,
        "first_isa": str(entered[first_isa]) if first_isa is not None else None,
        "unknown_before_marker": sorted(set(unresolved_before_marker)),
        "computed_loads": sorted(set(dynamic)), "unresolved_literals": missing,
        "scope": "Model-before-ISA barrier and literal file existence; not a proof qualification"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--root", action="append", type=Path, default=[])
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[2]
    source = args.source if args.source.is_absolute() else repo / args.source
    result = inspect(source, [repo, *args.root])
    print(json.dumps(result, indent=2))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
