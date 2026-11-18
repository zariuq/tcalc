(* Existing p1 images inhabit every larger admitted native stack profile. *)
needs "native/driver/native_component_stack.ml";;
needs "native/driver/native_component_p1.ml";;

let COMPONENT_P1_STACK_IMAGE = prove
 (`!reserve p mc pc. 40 <= reserve /\ tisa_leaf_spec p mc pc
     ==> component_stack_image reserve (component_of_p1 p) mc pc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC COMPONENT_STACK_IMAGE_MONO THEN
  EXISTS_TAC `40` THEN ASM_REWRITE_TAC[COMPONENT_STACK_BASE_IMAGE;COMPONENT_P1_IMAGE]);;

let native_component_stack_p1_theorems = native_component_stack_theorems @
 ["COMPONENT_P1_STACK_IMAGE",COMPONENT_P1_STACK_IMAGE];;
