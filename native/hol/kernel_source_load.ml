(* Load the native checker's source semantics and functional leaf contracts.
   The Model parser marker precedes ISA imports. Native leaf image proofs
   and concrete record fixtures have their own entrypoints. *)
let kernel_source_model_marked =
  exists (fun (file,_) -> Filename.basename file = "model_on_s2n.ml") !loaded_files;;
if exists (fun (name,_) -> name = "x86") (constants()) && not kernel_source_model_marked
then failwith "load kernel_source_load before ISA files";;

needs "native/hol/model_on_s2n.ml";;
needs "native/hol/zero_init_preserve.ml";;
needs "native/hol/reader_leaf_properties.ml";;
needs "native/hol/holr_leaf_link.ml";;
needs "native/hol/model_world_load.ml";;
needs "native/hol/holr_compose.ml";;
needs "native/hol/plans_drv.ml";;
needs "native/hol/plans_leaves.ml";;
needs "native/leaves/leaves_spec.ml";;
