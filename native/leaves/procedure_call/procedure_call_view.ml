(* The call request observes frame arguments, hot inputs and target metadata. *)
needs "tisa/hol/tisa_p1.ml";;

let procedure_request_value = new_definition
 `procedure_request_value t i =
    if i = 0 then tisa_fword t 22 else
    if i = 1 then tisa_fword t 23 else
    if i = 7 then tisa_fword t 17 else tregs t (i - 1)`;;
