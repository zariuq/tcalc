#!/bin/sh
# Regression fixtures for conversion profiles and complete proof articles.
#
# usage: admission_controls.sh DK_TCALC MG_TCALC DEDUKTI KONTROLI
#
# Conversion profiles (dk-controls/profiles): each file is checked with and without
# eta by dk_tcalc, by Dedukti (`dk check --type-lhs`) and by Kontroli, and the three
# must give the expected verdict.  Proof articles (mg-controls/admission): mg_tcalc
# must accept the complete ones and refuse the others with a diagnostic.
set -u
DK=$1; MG=$2; DEDUKTI=$3; KONTROLI=$4
cd "$(dirname "$0")"
checks=0

check() { # EXPECTED-STATUS DIAGNOSTIC-OR-EMPTY COMMAND...
  want=$1; diag=$2; shift 2
  out=$("$@" 2>&1); rc=$?
  if [ "$rc" -ne "$want" ]; then
    echo "Unexpected result: $*"; echo "exit=$rc"; printf '%s\n' "$out"; exit 1
  fi
  if [ -n "$diag" ]; then
    case "$out" in *"$diag"*) ;; *) echo "Missing diagnostic '$diag': $*"; printf '%s\n' "$out"; exit 1 ;; esac
  fi
  checks=$((checks + 1))
}

# NAME:ACCEPTED-WITHOUT-ETA:ACCEPTED-WITH-ETA
for row in beta_only:yes:yes eta_required:no:yes eta_wrong:no:no; do
  name=${row%%:*}; rest=${row#*:}; plain=${rest%%:*}; eta=${rest#*:}
  src=dk-controls/profiles/$name.dk
  for mode in plain eta; do
    if [ "$mode" = eta ]; then flag=--eta; accepted=$eta; else flag=; accepted=$plain; fi
    if [ "$accepted" = yes ]; then
      check 0 "" "$DK" $flag "$src"
      check 0 "" "$DEDUKTI" check --type-lhs $flag "$src"
      ( cd dk-controls/profiles && check 0 "" "$KONTROLI" $flag "$name.dk" && exit 42 ); [ $? -eq 42 ] || exit 1
    else
      check 1 "" "$DK" $flag "$src"
      check 255 "ERROR CODE:101" "$DEDUKTI" check --type-lhs $flag "$src"
      ( cd dk-controls/profiles && check 1 "" "$KONTROLI" $flag "$name.dk" && exit 42 ); [ $? -eq 42 ] || exit 1
    fi
    checks=$((checks + 1))   # the Kontroli check ran in a subshell
  done
done

# A conversion profile cannot be switched inside one run.
check 1 "" "$DK" --eta --no-eta dk-controls/profiles/eta_required.dk
check 1 "" "$DK" --chain --eta dk-controls/profiles/eta_required.dk --no-eta dk-controls/profiles/eta_required.dk

for row in checked_proof:yes repeated_definition:yes missing_proof:no unpaired_qed:no redefined:no duplicate_proof:no; do
  name=${row%%:*}; accepted=${row#*:}
  if [ "$accepted" = yes ]; then
    check 0 "" "$MG" "mg-controls/admission/$name.sexpr"
  else
    check 1 "mg_tcalc:" "$MG" "mg-controls/admission/$name.sexpr"
  fi
done

echo "admission controls: $checks/$checks checks passed (conversion: tcalc, Dedukti, Kontroli; article structure: tcalc)"
