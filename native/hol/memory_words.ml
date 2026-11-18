(* Numeric word observations over the driver byte memory. *)
needs "native/driver/driver.ml";;

let pl_mw = new_definition
 `pl_mw (m:int64->byte) (b:int64) i = val(drv_word m (word_add b (word(8 * i))))`;;
