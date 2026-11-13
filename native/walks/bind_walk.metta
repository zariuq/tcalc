; bind_walk.metta -- the binding walk: the de Bruijn image of an abstraction,
; authored with p1.metta as one standalone t-ISA p1 program, proved on its
; own (NATIVE-CHECKER.txt, sections 3, 4, 6 and 13; the proof is
; tcalc/native/hol/bind_walk.ml).
;
;   cetta --no-results bind_walk.metta TEXT NOTES
;
; writes the program's HOL text to TEXT and its annotations to NOTES.
;
; HOLR's ABS record builds TmAbs v body. Its de Bruijn image is
;   hdbAbs ty (hbind (x,ty) 0 (hdb body))
; and hbind replaces hdbVar x ty by hdbBound n, n rising under hdbAbs. The
; walk computes it over the hash-consed de Bruijn rows and returns the row of
; the whole image, the dbAbs row included.
;
; Regions (intern16's numbering for the rows):
;   0 rows    RW  de Bruijn rows, 16 bytes (k0, k1), k0 = tag + 8a, k1 = b:
;                 0 dbVar(name a, type b)  1 dbBound(a)  2 dbConst(name a, type b)
;                 3 dbComb(a, b)  4 dbAbs(type a, body b)  5 nil  6 cons
;   1 table   RW  intern16's table: 8-byte slots, 0 empty, id + 1 used
;   2 header  RW  word 0 the published row count
;   3 work    RW  the walk's own memory, at least 256 bytes (below)
; Inputs: arg0 = x (name id), arg1 = ty (type id), entry register v1 = t,
; the row of the body's image.
;
; Work region (W its base, L its length, K = L / 128 - 1 >= 1):
;   words 0..8   0 c, the private row count   1 tsp   2 vsp   3 lc   4 K
;                5 t   6 si   7 sn   8 mode    (the header is 128 bytes)
;   tasks        entry e at W + 128 + 32 e, e < K: (kind, i, n)
;                kind 0 VISIT, 1 COMB, 2 ABS
;   results      entry v at W + 128 + 32 (K + v), v < K: (i, n, r)
;   memo log     entry p at W + 128 + 32 (2K + p), p < K: (i, n, r)
;   memo table   slot s at W + 128 + 8 (12K + s), s < 4K: a log position
; Every result entry below vsp and every log entry below lc claims: row r
; is hbind at depth n of row i. The tasks, the memo table and everything
; above the counts are hints: a task is checked against its row and the
; results it combines, a memo slot against lc and the log entry's key, so a
; wrong, stale or corrupted work region cannot make the walk wrong.
; Bulk invalidation is lc := 0 on entry: a log position is valid only below
; this run's lc, and every log entry below it was written by this run.
;
; Interning: intern16's algorithm (the same hash, probe sequence and table),
; inline in the walk's loop, with the key in v1 (k0) and v2 (k1) and the row
; count in work word 0. New rows are appended at that private count; the
; published count (header word 0) is written once, last, on FIRED. Every
; other outcome leaves the header untouched, and rows written above it are
; invisible: the table's invariant speaks only of rows below the count.
;
; Outcomes:
;   FIRED          ret_val = the row of dbAbs ty (hbind (x,ty) 0 t)
;   UNSUPPORTED 1  the published count above the rows' capacity
;               2  t not below the published count
;               3  x or ty not below 2^60
;               4  the step budget (2^32 - 1 steps) used up
;               5, 6  no result for (t, 0) at the end
;               7  a task of no kind     8  a depth not below 2^60
;               9  a row with a list tag reached as a term
;              10  the task stack full
;              11, 12, 13  a task whose row, or results, do not match
;              14  every slot probed (table full)   15  results full
;              16  the rows full
;               2  (also) a loop above its cap (more than 2^32 - 1 slots)
;
; Registers: the walk's loop holds v10 (step) and v11 (budget); the probe
; loop v7 (probe), v8 (slots) and v9 (continue). Inside the probe loop: v1
; k0, v2 k1, v3 v4 temporaries, v5 the answer, v6 the hash. Elsewhere v1 ..
; v9 take the roles each block names.

!(import! &self "../p1/p1.metta")

(= (bw:cap) 4294967295)
(= (bw:gold) 11400714819323198485)
(= (bw:depth-cap) 1152921504606846976)

; ---- interning, intern16's algorithm ---------------------------------------

; One probe at (hash + probe) and (slots - 1).
(= (bw:probe)
   (Block bw_probe
     (Add v3 v6 v7)
     (Len v4 table) (Shr v4 v4 3) (Imm v5 1) (Sub v4 v4 v5)
     (And v3 v3 v4)
     (Base v4 table) (Addr table v4 v4 v3 3 0)
     (Load table v5 v4 0)
     (CmpI Eq v3 v5 0)
     (If v3 (bw:append) (bw:occupied))))

; An empty slot: the key goes to row c, the private count; then the slot
; and the private count.
(= (bw:append)
   (Block bw_append
     (Base v3 work) (Load work v5 v3 0)
     (Len v3 rows) (Shr v3 v3 4)
     (Cmp Ult v3 v5 v3)
     (If v3
         (Seq (Shl v3 v5 1) (Base v6 rows) (Addr rows v6 v6 v3 3 0)
              (Store rows v6 0 v1) (Store rows v6 8 v2)
              (Imm v3 1) (Add v3 v5 v3)
              (Store table v4 0 v3)
              (Base v6 work) (Store work v6 0 v3)
              (Imm TyBool v9 0))
         (Seq (Imm v3 16) (Return UNSUPPORTED v3)))))

; A used slot holds id + 1; an id below the private count names a row,
; compared with the key word for word.
(= (bw:occupied)
   (Block bw_occupied
     (Imm v3 1) (Sub v5 v5 v3)
     (Base v3 work) (Load work v3 v3 0)
     (Cmp Ult v3 v5 v3)
     (If v3
         (Seq (Shl v3 v5 1) (Base v4 rows) (Addr rows v4 v4 v3 3 0)
              (Load rows v3 v4 0) (Cmp Eq v3 v3 v1)
              (If v3
                  (Seq (Load rows v3 v4 8) (Cmp Eq v3 v3 v2)
                       (If v3 (Imm TyBool v9 0))))))))

; The key (v1, v2): its row in v5.
(= (bw:intern)
   (Block bw_intern
     (Xor v6 v1 v2) (Imm v3 (bw:gold)) (Mul v6 v6 v3) (Shr v3 v6 29) (Xor v6 v6 v3)
     (Len v8 table) (Shr v8 v8 3)
     (Imm TyBool v9 1)
     (Imm v5 0)
     (Invariant bw_probe_inv "\\N j s. bw_probe_inv st sq N j s"
       (EarlyLoop v7 v8 v9 (bw:cap) (bw:probe)))
     (If v9 (Seq (Imm v3 14) (Return UNSUPPORTED v3)))))

; ---- the result: published, or pushed and remembered -----------------------

; mode 2: publish the private count, FIRED with the row.
(= (bw:publish)
   (Block bw_publish
     (Load work v3 v2 0)
     (Base v4 header) (Store header v4 0 v3)
     (Return FIRED v5)))

; The result (si, sn, v5) goes to log entry lc and memo slot s.
(= (bw:memo)
   (Block bw_memo
     (Load work v4 v2 24) (Load work v6 v2 32)
     (Cmp Ult v3 v4 v6)
     (If v3
         (Seq (Shl v3 v6 1) (Add v3 v3 v4) (Shl v3 v3 2) (Addr work v3 v2 v3 3 128)
              (Store work v3 0 v7) (Store work v3 8 v8) (Store work v3 16 v5)
              (Shl v1 v6 2) (Imm v3 1) (Sub v1 v1 v3)
              (Imm v3 (bw:gold)) (Mul v9 v8 v3) (Add v9 v9 v7) (Mul v9 v9 v3) (Shr v9 v9 32)
              (And v9 v9 v1)
              (Shl v3 v6 3) (Shl v1 v6 2) (Add v1 v1 v3) (Add v1 v1 v9)
              (Addr work v1 v2 v1 3 128)
              (Store work v1 0 v4)
              (Imm v3 1) (Add v4 v4 v3) (Store work v2 24 v4)))))

; modes 0 and 1: the result (si, sn, v5) to the results; mode 1 remembers it.
(= (bw:push)
   (Block bw_push
     (Load work v4 v2 16) (Load work v6 v2 32)
     (Cmp Ult v7 v4 v6)
     (If v7 Skip (Seq (Imm v6 15) (Return UNSUPPORTED v6)))
     (Add v6 v6 v4) (Shl v6 v6 2) (Addr work v6 v2 v6 3 128)
     (Load work v7 v2 48) (Store work v6 0 v7)
     (Load work v8 v2 56) (Store work v6 8 v8)
     (Store work v6 16 v5)
     (Imm v6 1) (Add v4 v4 v6) (Store work v2 16 v4)
     (CmpI Eq v4 v3 1)
     (If v4 (bw:memo))))

(= (bw:post)
   (Block bw_post
     (Base v2 work)
     (Load work v3 v2 64)
     (CmpI Eq v4 v3 2)
     (If v4 (bw:publish)
         (Seq (CmpI Ult v4 v3 2) (If v4 (bw:push))))))

; Every step ends here: intern the key when v9 says so, then the result.
(= (bw:tail)
   (Block bw_tail
     (If v9 (bw:intern))
     (bw:post)))

; ---- the steps ----------------------------------------------------------------

; No task left: the result for (t, 0) is on top; dbAbs ty over it, mode 2.
(= (bw:last)
   (Block bw_last
     (Load work v3 v2 16)
     (CmpI Eq v4 v3 0)
     (If v4 (Seq (Imm v6 5) (Return UNSUPPORTED v6)))
     (Imm v4 1) (Sub v3 v3 v4)
     (Load work v4 v2 32) (Add v4 v4 v3) (Shl v4 v4 2) (Addr work v4 v2 v4 3 128)
     (Load work v5 v4 0) (Load work v6 v2 40) (Cmp Eq v5 v5 v6)
     (Load work v6 v4 8) (CmpI Eq v6 v6 0)
     (Bin BinAnd TyBool v5 v5 v6)
     (If v5 Skip (Seq (Imm v6 6) (Return UNSUPPORTED v6)))
     (Load work v2 v4 16)
     (Arg1 v1) (Shl v1 v1 3) (Imm v3 4) (Add v1 v1 v3)
     (Base v3 work) (Imm v4 2) (Store work v3 64 v4)
     (Imm TyBool v9 1)))

; A row of tag 0, 1 or 2 other than the variable: unchanged.
(= (bw:leaf)
   (Block bw_leaf
     (Mov v5 v8)
     (Imm v4 0) (Store work v2 64 v4)
     (Imm TyBool v9 0)))

; dbComb(a, b) visited: COMB(i, n) in place of the task, then VISIT(b, n),
; then VISIT(a, n) on top.
(= (bw:comb-expand)
   (Block bw_comb_expand
     (Load work v1 v2 32) (Imm v4 3) (Add v4 v3 v4) (Cmp Ult v1 v1 v4)
     (If v1 (Seq (Imm v6 10) (Return UNSUPPORTED v6)))
     (Shr v6 v6 3)
     (Shl v4 v3 2) (Addr work v4 v2 v4 3 128)
     (Imm v1 1) (Store work v4 0 v1)
     (Imm v1 0)
     (Store work v4 32 v1) (Store work v4 40 v5) (Store work v4 48 v7)
     (Store work v4 64 v1) (Store work v4 72 v6) (Store work v4 80 v7)
     (Imm v1 3) (Add v1 v3 v1) (Store work v2 8 v1)
     (Imm v1 3) (Store work v2 64 v1)
     (Imm TyBool v9 0)))

; dbAbs(A, b) visited: ABS(i, n) in place of the task, then VISIT(b, n + 1).
(= (bw:abs-expand)
   (Block bw_abs_expand
     (Load work v1 v2 32) (Imm v4 2) (Add v4 v3 v4) (Cmp Ult v1 v1 v4)
     (If v1 (Seq (Imm v6 10) (Return UNSUPPORTED v6)))
     (Shl v4 v3 2) (Addr work v4 v2 v4 3 128)
     (Imm v1 2) (Store work v4 0 v1)
     (Imm v1 0) (Store work v4 32 v1) (Store work v4 40 v5)
     (Imm v1 1) (Add v1 v7 v1) (Store work v4 48 v1)
     (Imm v1 2) (Add v1 v3 v1) (Store work v2 8 v1)
     (Imm v1 3) (Store work v2 64 v1)
     (Imm TyBool v9 0)))

; The row's tag, after the variable check.
(= (bw:tags)
   (Block bw_tags
     (Imm v1 7) (And v1 v6 v1)
     (CmpI Ult v9 v1 3)
     (If v9 (bw:leaf)
         (Seq (CmpI Eq v9 v1 3)
              (If v9 (bw:comb-expand)
                  (Seq (CmpI Eq v9 v1 4)
                       (If v9 (bw:abs-expand)
                           (Seq (Imm v6 9) (Return UNSUPPORTED v6)))))))))

; The variable itself: dbBound n.
(= (bw:bound)
   (Block bw_bound
     (CmpI Ult v1 v7 (bw:depth-cap))
     (If v1 Skip (Seq (Imm v6 8) (Return UNSUPPORTED v6)))
     (Shl v1 v7 3) (Imm v6 1) (Add v1 v1 v6)
     (Imm v2 0)
     (Base v6 work) (Imm v4 0) (Store work v6 64 v4)
     (Imm TyBool v9 1)))

; Not in the memo: the row (k0, k1); the variable is dbVar(x, ty) exactly.
(= (bw:miss)
   (Block bw_miss
     (Shl v1 v8 1) (Base v5 rows) (Addr rows v5 v5 v1 3 0)
     (Load rows v6 v5 0) (Load rows v5 v5 8)
     (Arg0 v1) (Shl v1 v1 3) (Cmp Eq v1 v6 v1)
     (Arg1 v9) (Cmp Eq v9 v5 v9)
     (Bin BinAnd TyBool v1 v1 v9)
     (If v1 (bw:bound) (bw:tags))))

; VISIT(i, n): the memo slot of (i, n) names a log position p; below lc,
; with the log entry's key (i, n), its result is the answer.
(= (bw:visit)
   (Block bw_visit
     (Load work v1 v2 32) (Shl v1 v1 2) (Imm v5 1) (Sub v1 v1 v5)
     (Imm v5 (bw:gold)) (Mul v6 v7 v5) (Add v6 v6 v8) (Mul v6 v6 v5) (Shr v6 v6 32) (And v6 v6 v1)
     (Load work v1 v2 32) (Shl v5 v1 3) (Shl v1 v1 2) (Add v1 v1 v5) (Add v1 v1 v6)
     (Addr work v1 v2 v1 3 128) (Load work v1 v1 0)
     (Load work v5 v2 24) (Cmp Ult v5 v1 v5)
     (Imm TyBool v9 0)
     (If v5
         (Seq (Load work v5 v2 32) (Shl v5 v5 1) (Add v5 v5 v1) (Shl v5 v5 2)
              (Addr work v5 v2 v5 3 128)
              (Load work v6 v5 0) (Cmp Eq v6 v6 v8)
              (Load work v1 v5 8) (Cmp Eq v1 v1 v7)
              (Bin BinAnd TyBool v9 v6 v1)
              (Load work v5 v5 16)))
     (If v9 (Seq (Imm v6 0) (Store work v2 64 v6) (Imm TyBool v9 0))
         (bw:miss))))

; COMB(i, n): row i is dbComb(a, b); the two results on top are for (a, n)
; and (b, n). Unchanged children give row i itself; otherwise the key
; dbComb(ra, rb).
(= (bw:comb)
   (Block bw_comb
     (Shl v1 v8 1) (Base v4 rows) (Addr rows v4 v4 v1 3 0)
     (Load rows v6 v4 0) (Load rows v5 v4 8)
     (Imm v1 7) (And v1 v6 v1) (CmpI Eq v1 v1 3)
     (If v1 Skip (Seq (Imm v6 11) (Return UNSUPPORTED v6)))
     (Shr v6 v6 3)
     (Load work v3 v2 16) (CmpI Ult v1 v3 2)
     (If v1 (Seq (Imm v6 12) (Return UNSUPPORTED v6)))
     (Imm v1 2) (Sub v3 v3 v1) (Store work v2 16 v3)
     (Load work v1 v2 32) (Add v1 v1 v3) (Shl v1 v1 2) (Addr work v4 v2 v1 3 128)
     (Load work v1 v4 0) (Cmp Eq v1 v1 v6)
     (Load work v3 v4 8) (Cmp Eq v3 v3 v7) (Bin BinAnd TyBool v1 v1 v3)
     (Load work v3 v4 32) (Cmp Eq v3 v3 v5) (Bin BinAnd TyBool v1 v1 v3)
     (Load work v3 v4 40) (Cmp Eq v3 v3 v7) (Bin BinAnd TyBool v1 v1 v3)
     (If v1 Skip (Seq (Imm v6 13) (Return UNSUPPORTED v6)))
     (Load work v1 v4 16) (Load work v3 v4 48)
     (Imm v4 1) (Store work v2 64 v4)
     (Cmp Eq v4 v1 v6) (Cmp Eq v9 v3 v5) (Bin BinAnd TyBool v4 v4 v9)
     (If v4 (Seq (Mov v5 v8) (Imm TyBool v9 0))
         (Seq (Shl v1 v1 3) (Imm v4 3) (Add v1 v1 v4) (Mov v2 v3) (Imm TyBool v9 1)))))

; ABS(i, n): row i is dbAbs(A, b); the result on top is for (b, n + 1).
; Unchanged gives row i; otherwise the key dbAbs(A, rb), whose k0 is row i's.
(= (bw:abs)
   (Block bw_abs
     (Shl v1 v8 1) (Base v4 rows) (Addr rows v4 v4 v1 3 0)
     (Load rows v6 v4 0) (Load rows v5 v4 8)
     (Imm v1 7) (And v1 v6 v1) (CmpI Eq v1 v1 4)
     (If v1 Skip (Seq (Imm v6 11) (Return UNSUPPORTED v6)))
     (CmpI Ult v1 v7 (bw:depth-cap))
     (If v1 Skip (Seq (Imm v6 8) (Return UNSUPPORTED v6)))
     (Load work v3 v2 16) (CmpI Eq v1 v3 0)
     (If v1 (Seq (Imm v6 12) (Return UNSUPPORTED v6)))
     (Imm v1 1) (Sub v3 v3 v1) (Store work v2 16 v3)
     (Load work v1 v2 32) (Add v1 v1 v3) (Shl v1 v1 2) (Addr work v4 v2 v1 3 128)
     (Load work v1 v4 0) (Cmp Eq v1 v1 v5)
     (Load work v3 v4 8) (Imm v9 1) (Add v9 v7 v9) (Cmp Eq v3 v3 v9)
     (Bin BinAnd TyBool v1 v1 v3)
     (If v1 Skip (Seq (Imm v6 13) (Return UNSUPPORTED v6)))
     (Load work v3 v4 16)
     (Imm v1 1) (Store work v2 64 v1)
     (Cmp Eq v1 v3 v5)
     (If v1 (Seq (Mov v5 v8) (Imm TyBool v9 0))
         (Seq (Mov v1 v6) (Mov v2 v3) (Imm TyBool v9 1)))))

; Pop the top task (kind, i, n); si, sn := i, n.
(= (bw:pop)
   (Block bw_pop
     (Imm v4 1) (Sub v3 v3 v4)
     (Store work v2 8 v3)
     (Shl v4 v3 2) (Addr work v4 v2 v4 3 128)
     (Load work v6 v4 0) (Load work v8 v4 8) (Load work v7 v4 16)
     (Store work v2 48 v8) (Store work v2 56 v7)
     (CmpI Eq v5 v6 0)
     (If v5 (bw:visit)
         (Seq (CmpI Eq v5 v6 1)
              (If v5 (bw:comb)
                  (Seq (CmpI Eq v5 v6 2)
                       (If v5 (bw:abs)
                           (Seq (Imm v6 7) (Return UNSUPPORTED v6)))))))))

; One step of the walk.
(= (bw:step)
   (Block bw_step
     (Base v2 work) (Load work v3 v2 8)
     (CmpI Eq v4 v3 0)
     (If v4 (bw:last) (bw:pop))))

(= (bw:body)
   (Block bw_body
     (bw:step)
     (bw:tail)))

; Entry: the published count within the rows, t below it, x and ty below
; 2^60; the work header, and VISIT(t, 0) as the one task.
(= (bw:prologue)
   (Block bw_prologue
     (Base v2 header) (Load header v3 v2 0)
     (Len v4 rows) (Shr v4 v4 4) (Cmp Ult v5 v4 v3)
     (If v5 (Seq (Imm v6 1) (Return UNSUPPORTED v6)))
     (Cmp Ult v5 v1 v3)
     (If v5 Skip (Seq (Imm v6 2) (Return UNSUPPORTED v6)))
     (Arg0 v4) (CmpI Ult v5 v4 (bw:depth-cap))
     (Arg1 v4) (CmpI Ult v6 v4 (bw:depth-cap))
     (Bin BinAnd TyBool v5 v5 v6)
     (If v5 Skip (Seq (Imm v6 3) (Return UNSUPPORTED v6)))
     (Base v2 work)
     (Store work v2 0 v3)
     (Len v4 work) (Shr v4 v4 7) (Imm v5 1) (Sub v4 v4 v5) (Store work v2 32 v4)
     (Store work v2 40 v1)
     (Imm v6 0)
     (Store work v2 128 v6) (Store work v2 136 v1) (Store work v2 144 v6)
     (Store work v2 8 v5)
     (Store work v2 16 v6) (Store work v2 24 v6)
     (Imm v11 (bw:cap))))

(= (bw:program)
   (p1:program bind_walk
     (Regions (Region rows RW 16 8) (Region table RW 8 8) (Region header RW 8 8)
              (Region work RW 256 8))
     (Registers)
     (Init (Entry v1 TyU64))
     (Seq (bw:prologue)
          (Invariant bw_inv "\\N j s. bw_inv st N j s"
            (Loop v10 v11 (bw:cap) (bw:body)))
          (Imm v6 4) (Return UNSUPPORTED v6))))

!(let* (($text (system:arg 0)) ($notes (system:arg 1)))
   (p1:write bw:program $text $notes))
