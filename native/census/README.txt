x86 census: what machine code actually uses
==========================================

  cetta FILE.metta, where FILE.metta imports x86_census.metta and calls
    !(census:report ("BINARY-OR-IMAGE.hol" ...))      mnemonic classes + comparison
    !(census:hot "NAME" "PERF.data")                  mnemonic classes weighted by cycles
    !(census:xed-report ("BINARY-OR-IMAGE.hol" ...))  XED's classes, differential, s2n forms
    !(census:xed-hot "NAME" "PERF.data")              the same weighted by cycles
    !(census:gate "IMAGE.hol")                        instructions outside s2n's decoded forms
    !(census:gate-exit "IMAGE.hol")                   the gate as a verdict line and exit status
  (record PERF.data with: perf record -e cycles:u -F 15000 -o PERF.data BINARY ARGS)

x86_census.metta is the tool; s2n_allowlist.metta is its generated table of
the forms s2n-bignum's decoder accepts. x86_census.py is an independent
version of the mnemonic mode, kept as its differential reference. The tool
is read-only: it runs objdump, xxd, perf and xed and reads files; an image,
and the encodings handed to xed, go to a directory made by `mktemp -d`
(under $TMPDIR) and removed afterwards. xed is Intel XED v2026.08.23, built
with its examples (obj/wkit/bin/xed); `census:xed` takes the binary from
XED when it is set, else runs `xed` from PATH.

Mnemonic classes: indirect branches (FF /2, FF /4), jump tables, push/pop of
memory, bit scans, BMI2, ADX, SIMD, string operations, endbr64, privileged;
base is an instruction in none of them. They are heuristics on objdump's text.

XED mode
--------
The same instruction stream (objdump's), each distinct encoding decoded once
by `xed -64 -cet -v 4 -isa-set -ih`, which gives its iclass, iform (the
iclass with its operand forms), category, ISA extension and ISA set. Every
encoding must come back as one record with the same bytes (the census
reports xed-records, xed-errors and missing). The classes, decided by xed:
  indirect-branch  iform CALL_NEAR_GPRv/MEMv, JMP_GPRv/MEMv, CALL/JMP_FAR_MEMp2
  jump-table       JMP_MEMv through a scaled index
  push-pop-rm      PUSH_MEMv, POP_MEMv
  string           the REP_, REPE_ and REPNE_ iclasses
  endbr            ENDBR64, ENDBR32
  simd             an iform operand that is a vector or mask register (XMM,
                   YMM, ZMM, MMX, MASK), or VZEROUPPER/VZEROALL
  bitscan          BSF BSR LZCNT TZCNT POPCNT
  bmi2, adx        xed's extensions BMI2, ADOX_ADCX
  privileged       SYSCALL INT INT3 CPUID RDTSC RDTSCP HLT UD2
The differential compares the two modes instruction by instruction on the
classes they share (simd, bmi2, bitscan, string, indirect = indirect-branch
or jump-table) and lists every disagreement as (CLASS MNEMONIC IFORM SIDE N).

Static census, 2026-11-13
-------------------------
GCC-built tcalc (-O3 -march=native -fno-tree-vectorize -flto; host with
AVX-512, BMI1/2, ABM, ADX, SHA):
  hol_tcalc  30,102 instructions, 13,916 encodings, 82 iclasses, 190 iforms.
             Mnemonic classes: base 29,500, simd 458, endbr 58,
             indirect-branch 43, bmi2 26, push-pop-rm 9, bitscan 4, string 3,
             privileged 1. XED gives the same counts in every class.
             Extensions: BASE 29,467, AVX 398, LONGMODE 79, AVX512EVEX 59,
             CET 58, BMI2 26, BMI1 14, FMA 1.
  dk_tcalc   29,187 instructions, 13,460 encodings, 92 iclasses, 203 iforms.
             Mnemonic classes: base 28,204, simd 876, indirect-branch 42,
             endbr 32, bmi2 18, push-pop-rm 9, bitscan 3, string 2,
             privileged 1; XED the same.
             Extensions: BASE 28,105, AVX 630, AVX512EVEX 242, LONGMODE 129,
             CET 32, BMI1 27, BMI2 18, FMA 3, AVX512VEX 1.
  Indirect branches in the code section: one jump table (the opcode switch
  of hol_replay_bytes, "notrack jmp *%rax"); the rest is libc glue.
Proved p1 images (intern16b, leb128, fnv, intern_name, bind_walk): 2,755
instructions, all extension BASE, 39 forms (iform, size, prefixes) in all.
The emitter puts a REX prefix on every byte-register operation (objdump
prints "rex sete %al"; xed: SETZ_GPR8): uniform, one byte each.
Differential: the modes agree on all five shared classes on all seven
targets, with no disagreement. On a probe image of borderline encodings
(native/census/coverage/probes/differential.hol) the one disagreement is
"repz ret" (F3 C3): the mnemonic mode counts any REP-prefixed line as a
string operation; xed decodes RET_NEAR, which is right.
A Python check (native/census/coverage/check_xed_census.py: libxed directly,
not the xed command) gives the same counts, extensions, ISA sets,
categories, classes and s2n split on all seven targets.

Cycles, 2026-11-13 (hol_tcalc on an 817,115-record HOLR stream, 2,775 samples)
-------------------------------------------------------------------------------
  Mnemonic and XED classes alike: base 97.9%, simd 1.4%, endbr 0.7%,
  indirect-branch 0.1%; BMI2, bit scans and string operations below the
  sampling resolution. Extensions: BASE 97.3, AVX512EVEX 0.8, CET 0.7,
  AVX 0.6, BMI1 0.5, LONGMODE 0.1.
  Top mnemonics: test 20.7, mov 17.0, jne 12.5, cmp 9.8, je 7.4, lea 4.4,
  add 3.6, xor 2.8 (sampling skid moves a load's stall onto the next
  instruction, so test/jne carry load latency).
  Top functions (perf annotate's per-symbol sample counts): app_intern 22.5%,
  hol_replay_bytes 17.5%, fire_ex 12.8%, mk 9.1%, vs_rec 4.0%, inst 3.6%:
  interning, decoding, transform firing, term construction. libc 3.6%
  (malloc and free 2.2%, memset 0.9%, memcpy 0.04%).
  In forms s2n decodes: 97.5% of cycles. The other 2.5%: ANDN 0.5, an
  AVX-512 VPMAXUQ (GCC's unsigned max) 0.5, the stack protector's
  FS-prefixed SUB and MOV 0.6, libc memset's AVX-512 store 0.3, 16-bit TEST
  0.2, indirect JMP 0.1, VPMAXUD 0.1.
  `census:xed-hot` reads `perf annotate --asm-raw`, joining the bytes of an
  instruction longer than perf's byte column (continued on the next lines)
  before decoding it.
So GCC's speed here is base-ISA code quality and memory behaviour (register
allocation, branch layout, table probing), not special instructions.

s2n-bignum's x86 decoder (upstream 76604c2)
--------------------------------------------
The table native/census/coverage/s2n-coverage.tsv (by iform) and
s2n-keys.tsv (by form) give, for every instruction in the seven targets and
the fast-path families, whether s2n's decoder decodes it, with the decode.ml
clause. It is a textual reading of decode.ml, made mechanical
(native/census/coverage/s2n_decode_reading.py) and checked against upstream's
own cosimulation encodings (simulator.ml, simulator_forms.ml: 3,586 encodings,
all accepted, every constructor as upstream names it). The authoritative
check is s2n's decoder run in HOL Light on the same encodings, a later pass;
s2n-verdicts.tsv lists them with the predicted verdict.
  Decoded with a caveat: LZCNT and TZCNT (decoded whatever CPUID says; on a
  CPU without ABM or BMI1 the bytes run as BSR or BSF), F2 A4 (decoded as
  REP MOVSB; the manuals define REPNE only for CMPS and SCAS, though
  upstream's MOVSB harness cosimulates it).
  Every decoded iform has an encoding that upstream cosimulates against
  hardware (lists or harnesses; MOVSB and REP MOVSB only with counts 0-7).
  Not decoded, among others: AVX-512 (any EVEX), VPCMPEQB/W/D/Q, VPMINU*/
  VPMAXU*, VPMOVMSKB on XMM (only the YMM form), SHLX/SHRX/SARX/RORX/BZHI/
  PDEP, ANDN/BLSR/BLSI/BLSMSK/BEXTR, REP STOS and MOVSW/D/Q, CMPS/SCAS/LODS,
  CRC32, legacy PCMPEQ/PTEST/PCLMULQDQ, CDQE/CQO, DIV/IDIV, LOCK, FS/GS and
  0x67 prefixes, 16-bit TEST/CMOV/INC (66 prefix), indirect CALL/JMP and
  PUSH/POP of memory (rejected since 9fc44ba5; CALL_ABSOLUTE exists in the
  semantics with a constant target, but nothing decodes to it).
  Provable today: copy (REP MOVSB, VMOVDQU), equality (VPXOR + VPTEST, or
  VPCMPGTD and VPMOVMSKB on YMM), zeroing (VPXOR + VMOVDQU), bit scans (with
  the CPUID caveat for LZCNT/TZCNT).

The s2n gate
------------
`census:gate` disassembles the image with addresses (an image's addresses
are byte offsets), decodes each distinct encoding with xed, and returns
  (census-gate IMAGE (instructions N) (encodings D) (xed-records R)
               (xed-errors E) (outside (ENTRY ...)))
where each ENTRY is (outside ADDRESS HEX KEY STATUS REASON) for an
instruction whose form is not in s2n_allowlist.metta: rejected, caveat, or
not-in-table (a form the table never saw). A form's KEY is IFORM|SHAPE|
PREFIXES: SHAPE is oN (xed's effective operand size, oNr2 after an APX REX2
prefix) or vVlLwW (VEXVALID, VL, REXW) for VEX and EVEX; PREFIXES is the set
of legacy prefix bytes before REX or VEX (".dup" when a byte other than 66
repeats). s2n's decoder sees prefixes only as that set, so the key decides
its verdict; across 22,655 keys seen (863,369 generated and real buffers) no
key has encodings with different verdicts. A pass is an empty outside list
with R = D and E = 0. An allowlist that did not load gives an Error, never
a pass.
2026-11-13: intern16b, leb128, fnv, intern_name and bind_walk pass (39 forms;
every one also has an encoding in upstream's cosimulation lists or harnesses).
A negative probe (native/census/coverage/probes/gate-negative.hol) fails with 7
outside: TZCNT (caveat), mov to %fs:, call *%rax, call *%r15, VPCMPEQB, UD2,
MOVSQ; ADD, POPCNT, VPXOR ymm and RET pass.

In an evidence script, after an image record is written (TMPDIR is where
mktemp puts the temporary files):
    printf '!(import! &self "%s")\n!(census:gate-exit "%s")\n' \
      native/census/x86_census.metta "$IMAGE" > "$WORK/gate.metta"
    TMPDIR="$WORK" cetta "$WORK/gate.metta" > "$WORK/gate.out" 2>&1; status=$?
    grep -q "^gate pass $IMAGE:" "$WORK/gate.out" && [ "$status" -eq 0 ] || exit 1
`census:gate-exit` prints "gate pass IMAGE: N instructions, ..." and exits 0,
or "gate FAIL IMAGE: ..." with each outside entry and exits 1. Check the line
as well as the status: on 2026-11-13, while the shared CeTTa build was being
rebuilt, the status of a failing gate came back 0 in some runs.

Regenerating the allowlist (after an s2n-bignum update or a new decoder form):
read the new decode.ml into native/census/coverage/s2n_decode_reading.py, then
    python3 -I native/census/coverage/build_coverage.py native/census/coverage \
      native/census
which rewrites s2n_allowlist.metta and the coverage tables, reports keys
with mixed verdicts (there must be none), and needs tools/xedkey (a libxed
client in native/census/coverage/tools, the same decoder state as xed -64 -cet).

Next
----
  - The same weighting on our own kernel once D assembles (it decides which
    leaves deserve SIMD), and on dk_tcalc.
  - The decoder pass in HOL: run s2n's decode on s2n-verdicts.tsv and compare
    with the predicted verdicts; any difference corrects the reading, then
    the allowlist.
