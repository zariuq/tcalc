#!/usr/bin/env bash
# test_p1_rejects.sh -- p1.metta stops loudly on programs outside its forms.
#
#   test_p1_rejects.sh WORKDIR
#
# Each case is one program body; the run must exit with status 3 and print
# the given words on stderr, and write no text. WORKDIR receives the case
# files. Exit status 0 iff every case is refused as expected.
set -u
here=$(cd "$(dirname "$0")" && pwd)
lib=$here/../p1.metta
cetta=${CETTA:-cetta}
work=${1:?usage: test_p1_rejects.sh WORKDIR}
mkdir -p "$work"

pass=0 fail=0
check() {   # NAME WORDS BODY [INIT]
    local name=$1 words=$2 body=$3 init=${4:-(Init)}
    local file=$work/$name.metta out=$work/$name.txt
    rm -f "$out"
    cat > "$file" <<EOF
!(import! &self "$lib")
(= (case:program)
   (p1:program $name
     (Regions (Region rows RW 16 8))
     (Registers (As k0 v1) (As t8 v8))
     $init
     $body))
!(p1:write case:program "$out" "$work/$name.notes")
EOF
    local err status
    err=$("$cetta" --no-results "$file" 2>&1 >/dev/null); status=$?
    if [ "$status" = 3 ] && [[ "$err" == *"$words"* ]] && [ ! -e "$out" ]; then
        pass=$((pass + 1))
    else
        fail=$((fail + 1)); echo "FAIL $name: status $status, stderr: $err"
    fi
}

check unbound_register   "(unbound register nosuch)"            "(Seq (Imm nosuch 1) (Return FIRED k0))"
check register_12        "(register 12 out-of-range)"            "(Seq (Imm 12 1) (Return FIRED k0))"
check unknown_form       "(statement (Frobnicate 1))"            "(Seq (Frobnicate 1) (Return FIRED k0))"
check word_too_big       "(word 18446744073709551616 out-of-range)" "(Seq (Imm k0 18446744073709551616) (Return FIRED k0))"
check displacement       "(displacement 2147483648 out-of-range)" "(Seq (Base t8 rows) (Load rows k0 t8 2147483648) (Return FIRED k0))"
check outcome            "(return-outcome DONE)"                 "(Return DONE k0)"
check unbound_region     "(unbound region nosuch)"               "(Seq (Base t8 nosuch) (Return FIRED k0))"
check pair_binding       "(statement (x v1))"                    "(With (x v1) (Imm x 1) (Return FIRED k0))"
check entry_register     "(entry-register 8 out-of-range)"       "(Return FIRED k0)" "(Init (Entry t8 TyU64))"
check entry_pointer      "(pointer-needs-a-region k0)"           "(Return FIRED k0)" "(Init (Entry k0 TyPtr))"
check entry_twice        "(entry-register-twice 1)"              "(Return FIRED k0)" "(Init (Entry k0 TyU64) (Entry v1 TyU64))"
check shift_type         "(type TyU128)"                         "(Seq (Shift ShiftLeft TyU128 k0 k0 1) (Return FIRED k0))"
check comparison         "(comparison Ugt)"                      "(Seq (Cmp Ugt k0 k0 k0) (Return FIRED k0))"
check no_result          "(program case:program resolved-to 0 results)" "(Seq (Imm k0 1) (empty))"
check fund_zero          "(fund-units 0 out-of-range)"           "(Seq (TFund 0) (Return FIRED k0))"

echo "test_p1_rejects: $((pass + fail)) cases, $pass refused as expected, $fail failures"
[ "$fail" = 0 ]
