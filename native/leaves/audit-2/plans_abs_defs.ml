(* Extracted verbatim from plans_abs.ml by leaves/audit.sh. *)

let pl_ids = define
 `(pl_ids (D:(num#num#num)list) l [] <=> l < LENGTH D /\ EL l D = (5,0,0)) /\
  (pl_ids D l (CONS a ids) <=> l < LENGTH D /\ ?b. EL l D = (6,a,b) /\ pl_ids D b ids)`;;

let pl_tyids = define
 `(pl_tyids (D:(num#num#num)list) l [] <=> l < LENGTH D /\ EL l D = (2,0,0)) /\
  (pl_tyids D l (CONS a ids) <=> l < LENGTH D /\ ?b. EL l D = (3,a,b) /\ pl_tyids D b ids)`;;

let pl_cells_new = new_definition
 `pl_cells_new c n0 (D':(num#num#num)list) (ok:num->bool) <=>
    !i. n0 <= i /\ i < LENGTH D'
        ==> ?a b ids. EL i D' = (c,a,b) /\ a < i /\ b < i /\ ok a /\
                      pl_ids D' b ids /\ ALL ok ids`;;
