(* ========================================================================= *)
(* The native HOL fibre with its transform-step instance. Run HOL Light with *)
(* Mettapedia/hol_light/HolInHol as the working directory.                   *)
(*                                                                           *)
(* The transform development loads first: its definitions use "holds" as a  *)
(* variable name, and Harrison's Model defines a constant of that name.     *)
(* ========================================================================= *)

loadt "Transform/core.ml";;
loadt "Transform/frames.ml";;
loadt "Transform/prepared.ml";;
loadt "Transform/runs.ml";;
loadt "Transform/admission.ml";;
loadt "make.ml";;
loadt "native/hol/holfibre.ml";;
loadt "native/hol/holfibre_instance.ml";;
loadt "native/hol/holr_spec.ml";;
loadt "native/hol/holr_refine.ml";;
loadt "native/hol/holfibre_controls.ml";;
