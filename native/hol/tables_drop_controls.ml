(* The live-id guard changes the verdict even when setting an existing mark. *)
needs "native/hol/kernel_table_kinds_load.ml";;

let DROP_TYPE_MARKED_REFUSED = prove
 (`!inp cw ctx nms tys ntms dbs ths nmap ymap drops pol stk n.
     cw 0 = 0 /\ cw 1 = 1 /\ cw 8 = n /\ MEM (1,n) drops
     ==> tab_run hol_tables inp pl_plan_drop_type 0
          (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
          (0,0,(pl_set cw 24 0,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pl_plan_drop_type] THEN
  GEN_REWRITE_TAC I [CONJUNCT2 tab_run] THEN
  MAP_EVERY EXISTS_TAC [`0`;`0`;`(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol):nstate`] THEN
  REWRITE_TAC[tab_leaf;hol_tables;LET_DEF;LET_END_DEF;FST;SND] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[tab_live;hol_tn;hol_tdrop] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let DROP_TYPE_MISSING_GUARD_FIRES = prove
 (`!inp cw ctx nms tys ntms dbs ths nmap ymap drops pol stk n.
     cw 0 = 0 /\ cw 1 = 1 /\ cw 8 = n /\ n < LENGTH ymap /\ MEM (1,n) drops
     ==> tab_run hol_tables inp (TL pl_plan_drop_type) 0
          (cw,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,drops,pol),stk)
          (1,1,(pl_set cw 25 1,(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,CONS (1,n) drops,pol),stk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pl_plan_drop_type;TL] THEN
  GEN_REWRITE_TAC I [CONJUNCT2 tab_run] THEN
  MAP_EVERY EXISTS_TAC [`1`;`1`;`(ctx,nms,tys,ntms,dbs,ths,nmap,ymap,CONS (1,n) drops,pol):nstate`] THEN
  REWRITE_TAC[tab_leaf;hol_tables;LET_DEF;LET_END_DEF;FST;SND] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[tab_putw;hol_twd;hol_tn;hol_tput;hol_mspace;tab_run] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let tables_drop_control_theorems =
 ["DROP_TYPE_MARKED_REFUSED",DROP_TYPE_MARKED_REFUSED;
  "DROP_TYPE_MISSING_GUARD_FIRES",DROP_TYPE_MISSING_GUARD_FIRES];;
leaf_audit tables_drop_control_theorems tables_drop_control_theorems;;
