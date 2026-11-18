#!/bin/sh
# Native/reference, layout, compiler-output and mutation checks for procedures.
set -eu

if [ "$#" -lt 4 ] || [ "$#" -gt 5 ]; then
    echo "usage: check.sh WORKDIR CESTA BYTE_SCALARS_MODULE LEAN_PROJECT [P1RUN]" >&2
    exit 2
fi
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$here/../.." && pwd)
work=$1
cesta=$2
scalars=$3
lean=$4
runner=${5:-"$root/native/p1/build/p1run"}
cetta=${TISA_CETTA:-cetta}
mkdir "$work"
work=$(CDPATH= cd -- "$work" && pwd)

python3 "$root/native/leaves/procedure_enter/procedure_enter.test.py" \
    --work "$work/activation" --cetta "$cetta" --p1run "$runner"
python3 "$root/native/leaves/procedure_call/procedure_call.test.py" \
    --work "$work/capture" --cetta "$cetta" --p1run "$runner"
python3 "$root/native/leaves/relw/relw.test.py" \
    --work "$work/comparison" --cetta "$cetta" --p1run "$runner"
python3 "$here/procedure_compile.test.py" --work "$work/compiler" --cetta "$cetta"
python3 "$root/native/abi/native_abi.test.py" --work "$work/abi" \
    --cetta "$cetta" --cesta "$cesta" --scalars "$scalars" --lean-project "$lean"

python3 - "$work" "$runner" "$cesta" "$cetta" "$here/check.sh" <<'PY'
from pathlib import Path
import hashlib
import json
import shutil
import sys

work = Path(sys.argv[1])
results = {name: json.loads((work / name / "result.json").read_text())
           for name in ["activation", "capture", "comparison", "compiler", "abi"]}
assert all(result["passed"] for result in results.values())
programs = [Path(sys.argv[2]).resolve(), Path(sys.argv[3]).resolve(),
            Path(shutil.which(sys.argv[4]) or sys.argv[4]).resolve(), Path(sys.argv[5]).resolve()]
summary = {"passed": True, "checks": results,
           "tools": {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in programs},
           "scope": "Native/reference, linked bytes, generated layouts and controls; HOL qualification is separate."}
(work / "result.json").write_text(json.dumps(summary, indent=2) + "\n")
print("procedure native gate: five suites passed; independent HOL qualification remains required")
PY
