#!/bin/bash
# evidence.sh LEAF OUTDIR
#
# The x86 evidence of a plan leaf: tcalc/tisa/hol/run_x86_evidence.sh (the
# shared image prover, in a fresh HOL Light process) on LEAF/LEAF.hol with
# LEAF/LEAF_join.ml as its driver, which joins the image theorem with the
# leaf's run theorem (LEAF_X86), proves the driver's premise LEAF_LEAF_SPEC,
# audits the leaf's theorems and runs the evidence gate. From the log, into
# OUTDIR/leaf.txt: the join and audit lines, the axioms, the evidence check
# (every loaded file current on disk) and a scan of the leaf's sources.
# OUTDIR must not exist (run_x86_evidence.sh makes it).
set -u
here=$(cd "$(dirname "$0")" && pwd)
nhol=$(cd "$here/../hol" && pwd)
leaf=${1:?usage: evidence.sh LEAF OUTDIR}
out=${2:?usage: evidence.sh LEAF OUTDIR}
[ -f "$here/$leaf/${leaf}_join.ml" ] || { echo "evidence.sh: no leaf $leaf"; exit 2; }
"$here/../../tisa/hol/run_x86_evidence.sh" "$here/$leaf/$leaf.hol" "$out" "$here/$leaf/${leaf}_join.ml"
out=$(realpath "$out")
{
  echo "leaf: $leaf"
  grep -a -o 'JOIN [a-z_]*: .*' "$out/hol.log" || true
  grep -a -o 'AUDIT [A-Za-z_0-9]*: [0-9]* hyps' "$out/hol.log" || true
  grep -a -o 'AUDIT theorems .*' "$out/hol.log" || true
  grep -a -A4 -o 'AXIOMS .*' "$out/hol.log" | head -5 || true
  echo "new_axiom, mk_thm, CHEAT_TAC in the leaf's sources: $(cat "$here/common/leaf_lib.ml" "$here/common/leaf_join_lib.ml" "$here/$leaf/$leaf.ml" "$here/$leaf/${leaf}_join.ml" | grep -c 'new_axiom\|mk_thm\|CHEAT_TAC' || true)"
  python3 -I "$nhol/evidence_check.py" "$out/hol.log" > "$out/evidence-check.txt" 2>&1 && ev=ok || ev=FAILED
  echo "evidence check: $ev; $(tail -1 "$out/evidence-check.txt")"
} > "$out/leaf.txt"
grep -a 'THEOREM ' "$out/hol.log" > "$out/theorems.txt" || true
cat "$out/leaf.txt"
