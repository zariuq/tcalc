(* Numeric fields and constant bytes read from checked header equalities. *)
needs "native/hol/kernel_header_basis_load.ml";;
needs "native/hol/reader_hdr.ml";;

let HEADER_PLAN_FIELDS = CONV_RULE
 (RAND_CONV(REWRITE_CONV
   [pl_hdr_b;pl_hdr_a;pl_hdr_v1;pl_hdr_v0;pl_hdr_p;pl_hdr_commit;pl_hdr_g;APPEND;MAP] THENC
   DEPTH_CONV WORD_RED_CONV))
 (AP_TERM `MAP (MAP(val:int64->num))` pl_plan_hdr);;

let HEADER_CONSTANT_FIELDS = REWRITE_CONV
 [holr_hdr_const;holr_magic;holr_kernel_id;TL;APPEND] `holr_hdr_const`;;

let header_plan_field_theorems =
 ["HEADER_PLAN_FIELDS",HEADER_PLAN_FIELDS;"HEADER_CONSTANT_FIELDS",HEADER_CONSTANT_FIELDS];;
leaf_audit header_plan_field_theorems header_plan_field_theorems;;

(* Optional exports are data extracted from these theorem conclusions. *)
let header_plan_export directory =
    let write name rows =
      let channel = open_out(Filename.concat directory name) in
      List.iter (fun row -> List.iter (fun n -> Printf.fprintf channel "%d " n) row;
                            output_char channel '\n') rows;
      close_out channel in
    let rows = map (map dest_small_numeral o dest_list) (dest_list(rhs(concl HEADER_PLAN_FIELDS))) in
    let bytes = map dest_small_numeral (dest_list(rhs(concl HEADER_CONSTANT_FIELDS))) in
    write "plan.words" rows;write "header.bytes" [bytes];
    Printf.printf "HEADER_EXPORT %d steps %d constant-bytes\n%!" (length rows) (length bytes);;

let _ = match Sys.getenv_opt "TISA_HEADER_EXPORT" with
 | None -> ()
 | Some directory -> header_plan_export directory;;
