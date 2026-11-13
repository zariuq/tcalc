; hyps_find.metta -- the record plans' leaf 8 (tcalc/native/PLANS.txt,
; sections 2, 5 and 6, EXPECT_ALPHA): the hypothesis list of a theorem as it
; is expected, found in the de Bruijn table without adding a row. Authored
; with p1.metta as one standalone t-ISA p1 program; its specification is
; pl_hyps_find_spec (tcalc/native/hol/plans_leaves.ml).
;
;   cetta --no-results hyps_find.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; Regions:
;   0 rows    RO  de Bruijn rows, 16 bytes (k0 = tag + 8a, k1 = b), intern16's
;   1 table   RO  its slots (0 empty, id + 1 used)
;   2 header  RO  word 0 the row count
;   3 terms   RO  named term rows, 40 bytes: tag, a, b, type, image
;   4 tcount  RO  word 0 the term count
;   5 marks   RO  the terms' dropped marks, one word per term
;   6 stack   RO  the operand stack
;   7 work    RW  this leaf's own words (below), at least 256 bytes
; Arguments: arg0 the first operand's index s in the stack, arg1 their
; number n.
;
; The listed terms must be live (below the count, mark 0) and of type bool
; (type row 1); their images (word 4 of their rows) form a set S, and the
; answer is the list row of S's elements in increasing order, when the table
; has it. Outcomes:
;   FIRED    ret_val = that row
;   REFUSED  a listed term not live or not of type bool, an image not below
;            2^61 (no cell holds it), or a list cell (or the nil row) the
;            list needs not in the table
; There is no UNSUPPORTED: no loop stops short of the work it has to do.
;
; The list is found from its tail, one round per row: the nil row (5, 0, 0)
; first, then, for the elements of S from the largest down, the cell
; (6, e, cur). A round after the first scans the operands for the largest
; image below the last one taken (prev, 2^61 at first) and looks its cell up;
; a round that finds no image ends the walk (at most n + 2 rounds). The
; scan's own big-while leaves k at 0, so a round that goes on sets k to 1. A look-up is intern16's probe sequence, read only: from the key's
; hash, slot after slot, until a slot names a row that is the key (found), an
; empty slot (absent: REFUSED), or every slot has been probed (absent:
; REFUSED). Only the work region is written.
;
; Loops past 2^32 - 1 iterations: big-while runs a body for j = 0, 1, ...
; while j < N and the flag k is 1 (N up to 2^62), as an early-exit loop of
; (N >> 31) + 1 chunks around an early-exit loop of 2^31 steps; j and N live
; in the work region. Admission locks a loop's index and bound registers in
; its body, and the rounds' big-while holds the scan's and the look-up's:
; eight registers are loop registers (level A the rounds', level B the
; others'), so every body works in t and u alone, k the flag.
;
; Work region words (byte offsets): 0 s, 8 n, 16 cur, 24 prev, 32 best,
; 40 found, 48 k0, 56 k1 (the key looked up), 64 the row found, 72 the
; found flag, 80 hash, 88 the row count, 96 104 the rounds' N and j, 112 120
; the scan's, 128 136 the probes', 144 the term count, 152 the slot mask,
; 160 168 saved words, 176 the nil row looked up (0 before the first round).

!(import! &self "../../p1/p1.metta")

(= (hf:cap) 4294967295)
(= (hf:chunk) 2147483648)
(= (hf:gold) 11400714819323198485)
(= (hf:top) 2305843009213693952)

; BODY for j = 0 .. N - 1 (N the work word at WN; j counted in the work word
; at WJ) while k is 1; BODY may clear k to stop early. Q NQ R NR the loop
; registers of one level.
(= (hf:big-while $q $nq $r $nr $wN $wJ $body)
   (Seq (Base u work) (Load work t u $wN) (Shr $nq t 31) (Imm t 1) (Add $nq $nq t)
        (Imm t 0) (Store work u $wJ t) (Imm TyBool k 1)
        (EarlyLoop $q $nq k (hf:cap)
          (Imm $nr (hf:chunk))
          (EarlyLoop $r $nr k (hf:cap)
            (Base u work) (Load work t u $wJ) (Load work u u $wN) (Cmp Ult t t u)
            (If t
                (Seq $body
                     (Base u work) (Load work t u $wJ) (Imm u 1) (Add t t u)
                     (Base u work) (Store work u $wJ t))
                (Imm TyBool k 0))))))

; The key (work 48, 56) looked up: its row to work 64, or REFUSED.
(= (hf:lookup)
   (Block hf_lookup
     (Base u work) (Load work t u 48) (Load work u u 56) (Xor t t u)
     (Imm u (hf:gold)) (Mul t t u) (Shr u t 29) (Xor t t u)
     (Base u work) (Store work u 80 t)
     (Len t table) (Shr t t 3) (Store work u 128 t)
     (Imm u 1) (Sub t t u) (Base u work) (Store work u 152 t)
     (Imm t 0) (Store work u 72 t)
     (hf:big-while q2 nq2 r2 nr2 128 136
       (Seq (Base u work) (Load work t u 136) (Load work u u 80) (Add t t u)
            (Base u work) (Load work u u 152) (And t t u)
            (Base u table) (Addr table u u t 3 0) (Load table t u 0)
            (CmpI Eq u t 0) (If u (Return REFUSED u))
            (Imm u 1) (Sub t t u)
            (Base u work) (Store work u 160 t) (Load work u u 88) (Cmp Ult u t u)
            (If u
                (Seq (Shl t t 1) (Base u rows) (Addr rows u u t 3 0) (Load rows t u 0)
                     (Base u work) (Store work u 168 t) (Load work t u 48) (Load work u u 168)
                     (Cmp Eq t t u)
                     (If t
                         (Seq (Base u work) (Load work t u 160) (Shl t t 1)
                              (Base u rows) (Addr rows u u t 3 0) (Load rows t u 8)
                              (Base u work) (Store work u 168 t) (Load work t u 56) (Load work u u 168)
                              (Cmp Eq t t u)
                              (If t
                                  (Seq (Base u work) (Load work t u 160) (Store work u 64 t)
                                       (Imm t 1) (Store work u 72 t) (Imm TyBool k 0)))))))))
     (Base u work) (Load work t u 72) (CmpI Eq t t 0) (If t (Return REFUSED t))))

; One scan of the operands: each must be live and of type bool, its image
; below 2^61; best (work 32) the largest image below prev, found (work 40).
(= (hf:scan)
   (Block hf_scan
     (Base u work) (Imm t 0) (Store work u 40 t)
     (Load work t u 8) (Store work u 112 t)
     (hf:big-while q2 nq2 r2 nr2 112 120
       (Seq (Base u work) (Load work t u 0) (Load work u u 120) (Add t t u)
            (Base u stack) (Addr stack u u t 3 0) (Load stack t u 0)
            (Base u work) (Store work u 160 t)
            (Load work u u 144) (Cmp Ult u t u) (If u Skip (Return REFUSED u))
            (Base u marks) (Addr marks u u t 3 0) (Load marks u u 0)
            (CmpI Eq u u 0) (If u Skip (Return REFUSED u))
            (Shl u t 2) (Add t u t)
            (Base u terms) (Addr terms u u t 3 0)
            (Load terms t u 24) (CmpI Eq t t 1) (If t Skip (Return REFUSED t))
            (Load terms t u 32)
            (CmpI Ult u t (hf:top)) (If u Skip (Return REFUSED u))
            (Base u work) (Store work u 168 t)
            (Load work u u 24) (Cmp Ult u t u)
            (If u
                (Seq (Base u work) (Load work u u 40) (CmpI Eq u u 0)
                     (If u
                         (Seq (Base u work) (Store work u 32 t) (Imm t 1) (Store work u 40 t))
                         (Seq (Base u work) (Load work u u 32) (Cmp Ult u u t)
                              (If u (Seq (Base u work) (Store work u 32 t)))))))))))

(= (hyps_find:program)
   (p1:program hyps_find
     (Regions (Region rows RO 16 8) (Region table RO 8 8) (Region header RO 8 8)
              (Region terms RO 0 8) (Region tcount RO 8 8) (Region marks RO 0 8)
              (Region stack RO 0 8) (Region work RW 256 8))
     (Registers (As q1 v1) (As nq1 v2) (As r1 v3) (As nr1 v4) (As q2 v5) (As nq2 v6)
                (As r2 v7) (As nr2 v8) (As k v9) (As t v10) (As u v11))
     (Init)
     (Seq (Block hf_start
            (Base u work) (Arg0 t) (Store work u 0 t) (Arg1 t) (Store work u 8 t)
            (Base u tcount) (Load tcount t u 0) (Base u work) (Store work u 144 t)
            (Base u header) (Load header t u 0) (Base u work) (Store work u 88 t)
            (Imm t 0) (Store work u 176 t)
            (Imm t (hf:top)) (Store work u 24 t)
            (Load work t u 8) (Imm u 2) (Add t t u) (Base u work) (Store work u 96 t))
          (hf:big-while q1 nq1 r1 nr1 96 104
            (Block hf_round
              (Base u work) (Load work t u 176) (CmpI Eq t t 0)
              (If t
                  (Seq (Imm t 5) (Base u work) (Store work u 48 t) (Imm t 0) (Store work u 56 t)
                       (Imm t 1) (Store work u 176 t))
                  (Seq (hf:scan)
                       (Base u work) (Load work t u 40) (CmpI Eq t t 0)
                       (If t
                           (Imm TyBool k 0)
                           (Seq (Base u work) (Load work t u 32) (Shl t t 3) (Imm u 6) (Add t t u)
                                (Base u work) (Store work u 48 t) (Load work t u 16) (Store work u 56 t)
                                (Load work t u 32) (Store work u 24 t) (Imm TyBool k 1)))))
              (If k
                  (Seq (hf:lookup)
                       (Base u work) (Load work t u 64) (Store work u 16 t)
                       (Imm TyBool k 1)))))
          (Base u work) (Load work t u 16) (Return FIRED t))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write hyps_find:program $text $notes))
