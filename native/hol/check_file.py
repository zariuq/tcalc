#!/usr/bin/env python3
"""Check one HOL file through its real dependencies in a fresh process.

Example: check_file.py native/hol/put_word_frame.ml --theorem PUT_WORD_FRAME_RUN
         --hol HOL_LIGHT_CHECKOUT --s2n S2N_CHECKOUT --out RESULT_DIRECTORY

The result directory must be new. Process completion alone is insufficient:
required theorem values must be closed, the axiom set must be the standard
three, and every loader-recorded input must still match its initial content.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import uuid


def digest(path: Path, algorithm: str = "sha256") -> str:
    return hashlib.new(algorithm, path.read_bytes()).hexdigest()


def source_index(roots: list[Path]) -> dict[str, list[tuple[Path, str, str]]]:
    result: dict[str, list[tuple[Path, str, str]]] = {}
    seen: set[Path] = set()
    for root in roots:
        for directory, folders, files in os.walk(root):
            folders[:] = [name for name in folders if not (
                name.startswith("evidence") or name in {
                    ".git", ".lake", "_opam", "_build", "sources", "Archive", "_archive"
                })]
            for name in files:
                if not name.endswith((".ml", ".hol")):
                    continue
                path = (Path(directory) / name).resolve()
                if path in seen:
                    continue
                seen.add(path)
                result.setdefault(name, []).append((path, digest(path, "md5"), digest(path)))
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--theorem", action="append", required=True)
    parser.add_argument("--hol", type=Path, default=os.environ.get("HOLDIR"))
    parser.add_argument("--s2n", type=Path, default=os.environ.get("S2N"))
    parser.add_argument("--source-root", action="append", type=Path, default=[])
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[2]
    source = (repo / args.source).resolve()
    if not source.is_file():
        parser.error("source file does not exist")
    if not args.hol or not args.s2n:
        parser.error("--hol and --s2n, or HOLDIR and S2N, are required")
    hol, s2n = args.hol.resolve(), args.s2n.resolve()
    if not (hol / "hol.sh").is_file() or not (s2n / "x86/proofs/base.ml").is_file():
        parser.error("invalid HOL Light or s2n checkout")
    names = list(dict.fromkeys(args.theorem))
    if any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", name) for name in names):
        parser.error("theorem names must be OCaml identifiers")
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    roots = [repo, hol, s2n, *[path.resolve() for path in args.source_root]]
    mettapedia = os.environ.get("METTAPEDIA_HOL_LIGHT")
    if mettapedia:
        roots.append(Path(mettapedia).resolve())
    if not any(source.is_relative_to(root) for root in roots):
        roots.append(source.parent)
    inputs = source_index(roots)
    nonce = "HOL_FILE_" + uuid.uuid4().hex
    quote = lambda text: json.dumps(str(text), ensure_ascii=False)
    named = ";".join("(" + quote(name) + "," + name + ")" for name in names)
    driver = (
        "loadt (Sys.getenv \"TCALC_DIR\" ^ \"/native/hol/roots.ml\");;\n"
        + "needs " + quote(source) + ";;\n"
        + "List.iter (fun (name,th) -> if hyp th <> [] then failwith (\"OPEN \" ^ name) "
          "else Printf.printf " + quote(nonce + " THM %s HYPS0\n%!") + " name) [" + named + "];;\n"
        + "if not (set_eq (map concl (axioms())) (map concl [ETA_AX;SELECT_AX;INFINITY_AX])) "
          "then failwith \"unexpected axiom set\";;\n"
        + "print_endline " + quote(nonce + " STANDARD3") + ";;\n"
        + "List.iter (fun (file,hash) -> Printf.printf " + quote(nonce + " INPUT %s %s\n%!")
          + " (Digest.to_hex hash) file) !loaded_files;;\n"
        + "print_endline " + quote(nonce + " DONE") + ";;\n"
    )
    (out / "check.ml").write_text(driver)
    env = dict(os.environ, TCALC_DIR=str(repo), S2N_BIGNUM_DIR=str(s2n), LINE_EDITOR="env")
    started = time.monotonic()
    with (out / "check.ml").open("rb") as command, (out / "hol.log").open("wb") as log:
        process = subprocess.Popen([str(hol / "hol.sh")], cwd=s2n, env=env,
                                   stdin=command, stdout=log, stderr=subprocess.STDOUT)
        (out / "process.json").write_text(json.dumps({"pid": process.pid, "source": str(source)}) + "\n")
        status = process.wait()
    text = re.sub(r"\x1b\[[0-9;]*m", "", (out / "hol.log").read_text(errors="replace"))
    errors = re.findall(r"(?m)^\s*(?:#\s*)?(?:Exception:|Error(?: in included file|:)|Parse error|IMAGE .* FAILED).*", text)
    missing = [name for name in names if nonce + " THM " + name + " HYPS0" not in text]
    stale: list[str] = []
    loaded: list[tuple[str, str]] = []
    for recorded, raw in re.findall(re.escape(nonce) + r" INPUT ([0-9a-f]{32}) (.+)", text):
        path = Path(raw)
        candidates = inputs.get(path.name, [])
        if path.is_absolute():
            candidates = [entry for entry in candidates if entry[0] == path]
        matches = [(p, sha) for p, md5, sha in candidates
                   if md5 == recorded and p.is_file() and digest(p) == sha]
        if not matches:
            stale.append(raw)
        else:
            loaded.append((str(matches[0][0]), matches[0][1]))
    source_unchanged = any(p == source and digest(source) == sha
                           for p, _md5, sha in inputs.get(source.name, []))
    passed = (status == 0 and not errors and not missing and not stale and loaded
              and source_unchanged and nonce + " STANDARD3" in text and nonce + " DONE" in text)
    result = {
        "passed": bool(passed), "actual_exit": status, "required_theorems": names,
        "missing_theorems": missing, "errors": errors, "stale_or_missing_inputs": stale,
        "loaded_inputs_checked": len(loaded), "source_unchanged": source_unchanged,
        "seconds": round(time.monotonic() - started, 3), "log_sha256": digest(out / "hol.log"),
    }
    (out / "loaded.sha256").write_text("".join(sha + "  " + path + "\n" for path, sha in loaded))
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2), flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
