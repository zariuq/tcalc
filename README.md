# tcalc

tcalc is a small kernel, written in C, for one step of rule-based rewriting over a store of
facts. A rule takes some facts (they are consumed), keeps others (they are only read), adds
equations to a store of bindings, checks that given facts are absent or present a given number
of times, may mint a fresh name, and makes new facts. After `tc_seal`, facts in a protected
space can only come from firing the sealed rules. The kernel is `tcalc.c` and `tcalc.h`; the
contract it keeps is written at the top of `tcalc.h`.

## Status: work in progress

tcalc is a moving target. The name covers a family, a web, of transform steps that differ in a few
choices, and this kernel implements one point of that family. The family is studied in the Lean
development `ConstraintMultisetRewriting` in Mettapedia (`RuleSyntax/Core.lean` for the one-match
step, `RuleSyntax/JointFirings/` for steps that commit several matches at once), where each choice
is named and compared:

- whether a store is a bag or a set;
- what one step commits: one match, or a bag of matches under one of several disciplines;
- whether a firing's checks see the equations the firing itself tells;
- whether rules sit beside the store or are held in it;
- whether knowledge lives in one store or at several worlds;
- how the matches of a rule are counted when identical patterns can select the same rows.

The kernel here fixes its own answers: it fires one match at a time, the one its caller names, and
asks a firing's checks after the firing's own tells. Interfaces, file layout and results change
without notice. The measurements below are dated, and nothing here is proved to implement the Lean
definition (see "Not covered").

Around the kernel this repository holds proof checkers and language runtimes that call it.
They differ a great deal in how much of their behaviour is tcalc rules and how much is C. The
table says, for each piece, what it is, what independent program it is checked against, and
what was measured on 2026-11-11. "Checked against" means differential testing on the corpora
named; it is evidence, not a proof.

## The pieces

| Piece | What it is | Checked against | Measured | Rules or C |
|---|---|---|---|---|
| Kernel (`tcalc.c`, `tcalc.h`) | the rewriting step, sealing, protected spaces, names minted before use | 33 control programs (`kernel-controls/`), six random differentials against naive reference implementations written from the stated meaning, `test_tcalc` | all controls hold; 0 disagreements over 20,000 seeds per differential; 496 unit checks | the kernel itself |
| `mm0_tcalc`, `mmb_tcalc` | Metamath Zero checkers: each axiom is a tcalc rule, each theorem a proof script that the kernel checks and installs as a rule | the MM0 test suites' expected verdicts; mm0-c for `.mmb` | 17 positive and 79 negative `.mmu` controls, 4 and 25 `.mmb`, 190 specification controls; 44,260 single-bit mutants of `.mmb` files, none accepted that mm0-c refuses | every proof step is a kernel step; the `.mm0` reader and notation are C |
| Micromath (`micromath_tcalc.c`, `diff_micromath`) | Micromath's logic as a six-rule tcalc theory, run by the kernel, by two generated routes and by a t-ISA x86 leaf | Micromath's own kernel (`ref/`) | 30,486,537 operations with identical verdicts; three operations on unallocated symbols differ by design (tcalc requires a name to be minted before use) | derivations are rule firings; decoding and scheduling are C |
| `hol_tcalc` | a HOL Light proof-stream replayer: theorems are made only by firing rules for HOL Light's ten primitive inferences and three theory extensions | the HOL Light export's own lists of checked sequents; CeTTa's replay of the same streams | 10 streams accepted; 4,554 mutated and 1,736 truncated streams, none accepted that the reference refuses | the inferences are rules; substitution, alpha-equivalence, hypothesis union, freeness and type-definition side conditions are named C certificates |
| `mg_tcalc` | a Megalodon proof checker (Egal, HF, Mizar, HOAS profiles); its translator `--emit-dk` writes Dedukti | OCaml Megalodon; `dk check` on the translation | the 15 Egal parts (1,430 theorems); 4,591 mutants, none accepted that Megalodon refuses | typing and proof judgments are made by 30 rules; conversion, context lookup, shifts and instantiation are C helpers |
| `dk_tcalc` | a Dedukti (lambda-Pi modulo rewriting) checker | `dk check --type-lhs`; Kontroli | 13 Dedukti theories, 7 examples, 26 Megalodon bridge fixtures, the tower; 9,079 mutants, 5,800 random rule programs and 14,150 file prefixes, none accepted that `dk` refuses | the 8 typing rules are rules; matching, reduction, conversion and rule typing are C |
| `lean_tcalc` | a Lean 4 checker written in C that records each admitted declaration as a tcalc fact through 23 rules | the official Lean 4 kernel (Lean kernel arena) and nanoda | arena: 240 tests agree, 1 declined (its expression store is full), 0 wrong; 7,686 mutants judged by the official kernel, none accepted that it refuses; `Init` in 6.35 s and `Std` in 12.77 s (nanoda on 4 threads: 7.39 s and 12.94 s) | type inference, reduction, definitional equality, universes and inductive, recursor and quotient admission are C; 12 of the 23 rules publish what C decided, 11 combine those facts |
| `dl_tcalc` | Datalog by set saturation and CHR (constraint handling rules) by linear consumption, each source rule lowered to a tcalc rule | Souffle 2.5 (Datalog); SWI-Prolog `library(chr)` (CHR) | 2,400 random Datalog programs and 6 test programs identical to Souffle; 14 ground and 16 first-order CHR programs end with SWI-Prolog's status and store, and 6 review counterexamples as expected; its self-test passes under the address, undefined-behaviour and thread sanitizers; past its fixed tables (65,536 facts, 4,095 symbols, a store of 8,192 constraints) it stops and says so instead of answering short | Datalog clauses and CHR rules are rules; parsing, scheduling, first-order unification and arithmetic are C |
| PeTTa evaluator (`petta_tcalc_eval.h`) | a C evaluator for a core of PeTTa; adding and removing atoms go through tcalc rules | CeTTa's PeTTa on the PeTTa examples, judged by the examples' own `test` directives | 585 of 687 tests pass; 120 of the files pass all their tests | evaluation is C; only atom-space effects are rules |
| Gold languages (`gold_langs_tcalc.h`) | C interpreters for a subset of Erlang and of OCaml, a Maude subset, and Datalog explanations, each run on a few example files | native Erlang, OCaml, Maude, Souffle and SWI-Prolog, through the same expected results | the example files give the expected results; outside them the OCaml interpreter evaluates multiplication wrongly and does not type-check its input, and the Erlang interpreter crashes on a run-time type error | each language's semantics is C; sends, receives and a few commits are rules |
| GSLT packed-forest reader (`gslt_packed_bridge.h`) | a C reader of authored grammar modules and packed parse forests | none | used only by its own tests | C |
| t-ISA (`tisa/`) | a small instruction set with a reference evaluator and an x86-64 emitter, used for tcalc rule leaves | a second emitter written in MeTTa (byte parity); an x86 formal model in Lean, in progress | 17,477 checks; all 15 programs are pending a formal proof | n/a |
| `compiled/` | the `flat_fire` leaf as x86 machine code and the linked bytes every binary carries | HOL Light with s2n-bignum | `flat_fire` is proved correct (`FLAT_FIRE_CORRECT`); the packing adapter around it is not proved; every binary is checked to carry the exact proved bytes | n/a |
| `cesta/` | scanner, commit bridge, event view, cursor and Lean guard written in Cesta and exported to C | the C baselines they replace (differential) | 80 positive and 129 negative pairs agree | n/a |

`dk_tcalc` matches every instance of a left-hand side, as the matching relation of lambda-Pi
modulo rewriting defines. Dedukti (0b67dab, and master f3c0eba, whose matching code is the same)
mishandles a pattern variable used twice under the pattern's binders. A missing binder-index
adjustment makes it leave some valid instances unmatched (an instance that mentions a variable
bound outside the redex). It also makes it match some invalid ones: `g (u => c u q)` against
`[F] g (x => c F F)`. So Dedukti accepts invalid conversions; in one otherwise consistent
theory this gives a term of type `Z : Prop -> prf Z`. `dk_tcalc` refuses those in every mode.

`--dk-matching` reproduces only the first effect, and only for pattern variables applied to no
bound variable; it never reproduces Dedukti's invalid matches. With `--eta`, Dedukti also does
not match a target that is not an abstraction. `dk-controls/known-differences/` shows each case.

Known gap of `dk_tcalc`: it checks that an instance avoids the pattern's binders before
normalizing the instance. So it refuses an instance that mentions a binder only inside a redex
whose normal form drops it, for example `g (u => c ((v : A => ok) u) ok)`.
Other profiles: `--eta`, `--pts cc` (or `--coc`), `--allow-static-rules`.

What "on tcalc" does not mean: except for the Metamath Zero and Micromath checkers, the
semantics of each checker is C code beside the kernel. Sealing guarantees that protected facts
come only from firing the declared rules; it does not check the C that decides when to fire.

## Parts not yet in the table

These are younger than the measurements above and have no dated results here yet.

| Part | What it is |
|---|---|
| `reference/` | a second implementation of one step, written from the Lean definitions and deciding every guard at every solution of a firing's information; beside it, studies of binders (`binders/`), Dedukti (`dedukti/`), Metamath Zero (`mm0/`), and rules compiled to C by partial evaluation (`specialize/`) |
| `core/` | `tc0`, a prototype of the tier-0 fragment (rules that read up to four facts, mint at most one name and make one fact), with Micromath on it |
| `native/` | a HOL Light checker written as a t-ISA p1 program, with its proof obligations: decoding, interning, record plans, walks and the leaves they call (`NATIVE-CHECKER.txt`, `PLANS.txt`) |
| `tisa/hol/` | HOL Light models of t-ISA p1 (evaluation, memory, frames, non-interference) and of its x86-64 emission |
| `bridge/` | a C interface between a host's transform step and the kernel that keeps preparing an effect apart from admitting it; its refinement to the calculus is not proved |

## Build and test

    make          # every program
    ./run.sh      # the whole gate (also: make check)

`run.sh` builds with `make`, runs every suite above that has its oracle available, checks the
proved leaf bytes in every binary, and ends with `adversarial_controls.sh`. It needs, next to
this repository, the MM0 repository, the HOL Light streams, Megalodon's fixtures and the Egal
corpus, the Dedukti and Kontroli example directories, Dedukti's theories and the GSLT test
programs; the reference programs are found on `PATH` or given by `MG_BIN` (Megalodon),
`DK_BIN` (Dedukti), `KO_BIN` (Kontroli), `SOUFFLE_BIN`, `SWIPL_BIN`, `LEAN_ORACLE` (the
official Lean kernel replay) and `LEAN_SAN` (a sanitizer build of `lean_tcalc`). A missing optional oracle is
reported as NOT RUN. `KERNEL_SEEDS` sets the size of the kernel differentials (default 20,000).
The Cesta targets need the Cesta compiler (`CESTA`). The PeTTa evaluator resolves imports
against the importing file's directory and its sibling `lib/`; `PETTA_ROOT` (a PeTTa checkout)
adds that checkout's `examples/` and `lib/`.

Exit status of the checkers: 0 accepted, 1 refused, 2 no verdict (a fixed table, the stack or
memory ran out).

## Not covered

- No checker here is proved correct; the evidence is differential.
- `lean_tcalc` refuses `unsafe` and `partial` definitions and does not compute with natural
  number literals above 2^128.
- Termination and confluence of Dedukti rewrite rules are not checked (Dedukti does not check
  them either).
- The translator `mg_tcalc --emit-dk` is checked on its corpora, not proved.
