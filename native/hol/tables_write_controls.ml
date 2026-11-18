(* Positive and negative controls for the exact guarded write relation. *)
needs "native/hol/kernel_table_repr_load.ml";;

let TAB_PUTW_CELL_WRITES = prove
 (`tab_putw (\c s:num. 1) (\j:num. 1)
      (\j c s i w v s':num. s' = v) 0 0 5 1 0 0 9 1 9 9`,
  REWRITE_TAC[tab_putw] THEN CONV_TAC NUM_REDUCE_CONV);;

let TAB_PUTW_PAST_COUNT_KEEPS = prove
 (`tab_putw (\c s:num. 1) (\j:num. 1)
      (\j c s i w v s':num. s' = v) 0 0 5 1 1 0 9 2 0 5 /\
   ~(?pay s'. tab_putw (\c s:num. 1) (\j:num. 1)
      (\j c s i w v s':num. s' = v) 0 0 5 1 1 0 9 1 pay s')`,
  REWRITE_TAC[tab_putw] THEN CONV_TAC NUM_REDUCE_CONV);;

let TAB_PUTW_MISSING_WRITER_UNDEFINED = prove
 (`~(?k pay s'. tab_putw (\c s:num. 1) (\j:num. 1)
      (\j c s i w v s':num. F) 0 0 5 1 0 0 9 k pay s')`,
  REWRITE_TAC[tab_putw] THEN CONV_TAC NUM_REDUCE_CONV);;

let TAB_PUTW_WRONG_WIDTH_UNDEFINED = prove
 (`~(?k pay s'. tab_putw (\c s:num. 1) (\j:num. 1)
      (\j c s i w v s':num. s' = v) 0 0 5 2 0 0 9 k pay s')`,
  REWRITE_TAC[tab_putw] THEN CONV_TAC NUM_REDUCE_CONV);;

let tables_write_control_theorems =
 ["TAB_PUTW_CELL_WRITES",TAB_PUTW_CELL_WRITES;
  "TAB_PUTW_PAST_COUNT_KEEPS",TAB_PUTW_PAST_COUNT_KEEPS;
  "TAB_PUTW_MISSING_WRITER_UNDEFINED",TAB_PUTW_MISSING_WRITER_UNDEFINED;
  "TAB_PUTW_WRONG_WIDTH_UNDEFINED",TAB_PUTW_WRONG_WIDTH_UNDEFINED];;
leaf_audit tables_write_control_theorems tables_write_control_theorems;;
