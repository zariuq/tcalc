(* Byte-memory requirements of the HOL bootstrap layout. *)
needs "native/hol/memory_words.ml";;

let boot_bytes = new_definition
 `boot_bytes = [61; 65; 98; 111; 111; 108; 102; 117; 110]`;;

let hol_boot_lengths = new_definition
 `hol_boot_lengths (bw:num->int64) <=>
    16 <= val(bw 1) /\ 8 <= val(bw 3) /\ 8 <= val(bw 5) /\
    16 <= val(bw 7) /\ 8 <= val(bw 9) /\ 8 <= val(bw 11) /\
    val(bw 13) < 8 * 5 * 2 EXP 60 /\ 8 <= val(bw 15) /\ val(bw 13) <= 5 * val(bw 17) /\
    val(bw 19) < 8 * 2 * 2 EXP 60 /\ 8 <= val(bw 21) /\ val(bw 19) <= 2 * val(bw 23) /\
    val(bw 25) < 8 * 1 * 2 EXP 60 /\ 8 <= val(bw 27) /\ val(bw 25) <= 1 * val(bw 29) /\
    val(bw 31) < 8 * 1 * 2 EXP 60 /\ 8 <= val(bw 33) /\ val(bw 31) <= 1 * val(bw 35) /\
    16 <= val(bw 51)`;;

let hol_boot_zero = new_definition
 `hol_boot_zero (bw:num->int64) (m:int64->byte) <=>
    pl_mw m (bw 4) 0 = 0 /\ pl_mw m (bw 10) 0 = 0 /\ pl_mw m (bw 14) 0 = 0 /\ pl_mw m (bw 20) 0 = 0 /\
    pl_mw m (bw 26) 0 = 0 /\ pl_mw m (bw 32) 0 = 0 /\ pl_mw m (bw 50) 0 = 0 /\ pl_mw m (bw 50) 1 = 0 /\
    (!i. 8 * i + 8 <= val(bw 17) ==> pl_mw m (bw 16) i = 0) /\
    (!i. 8 * i + 8 <= val(bw 23) ==> pl_mw m (bw 22) i = 0) /\
    (!i. 8 * i + 8 <= val(bw 29) ==> pl_mw m (bw 28) i = 0) /\
    (!i. 8 * i + 8 <= val(bw 35) ==> pl_mw m (bw 34) i = 0)`;;

let hol_boot_bytes_at = new_definition
 `hol_boot_bytes_at (bw:num->int64) (m:int64->byte) <=>
    val(bw 63) = 9 /\ !i. i < 9 ==> val(m(word_add (bw 62) (word i))) = EL i boot_bytes`;;
