Definition tm_cfe97741543f37f0 : (prop -> (prop -> prop)) := (fun (x0 : prop) => (fun (x1 : prop) => (forall (x2 : prop), ((x0 -> x2) -> ((x1 -> x2) -> x2))))).
Section S1. Variable a0 : SType.
Definition tm_5a6af35fb6d6bea4 : (a0 -> (a0 -> prop)) := (fun (x0 : a0) => (fun (x1 : a0) => (forall (x2 : (a0 -> (a0 -> prop))), (((x2 x0) x1) -> ((x2 x1) x0))))).
End S1.
Parameter In : (set -> (set -> prop)).
Definition tm_73c9efe869770ab4 : (set -> (set -> prop)) := In.
Parameter Empty : set.
Definition tm_e2a83319facad3a3 : set := Empty.
Parameter Union : (set -> set).
Definition tm_844774016d959cff : (set -> set) := Union.
Parameter Power : (set -> set).
Definition tm_2a38dbb37506341b : (set -> set) := Power.
Parameter Repl : (set -> ((set -> set) -> set)).
Definition tm_b1b8f6f9d4d6136b : (set -> ((set -> set) -> set)) := Repl.
Parameter UnivOf : (set -> set).
Definition tm_5a50bfe3a33a99c3 : (set -> set) := UnivOf.
Axiom kn_5a437ac4e488ce7d : (forall (x0 : set), (forall (x1 : (set -> set)), (forall (x2 : set), (((tm_73c9efe869770ab4 x2) ((tm_b1b8f6f9d4d6136b x0) (fun (x3 : set) => (x1 x3)))) -> (forall (x3 : prop), ((forall (x4 : set), (((tm_73c9efe869770ab4 x4) x0) -> ((((tm_5a6af35fb6d6bea4 set) x2) (x1 x4)) -> x3))) -> x3)))))).
(* Parameter tm_0a445311c45f0eb3 "0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e" "0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e" *)
Parameter tm_0a445311c45f0eb3 : (set -> (set -> set)).
Axiom kn_f270d6aed9b2d86f : (forall (x0 : set), (forall (x1 : set), (forall (x2 : set), (((tm_73c9efe869770ab4 x2) ((tm_0a445311c45f0eb3 x0) x1)) -> ((tm_cfe97741543f37f0 ((tm_73c9efe869770ab4 x2) x0)) ((tm_73c9efe869770ab4 x2) x1)))))).
(* Parameter tm_39cdf86d83c71365 "39cdf86d83c7136517f803d29d0c748ea45a274ccbf9b8488f9cda3e21f4b47c" "39cdf86d83c7136517f803d29d0c748ea45a274ccbf9b8488f9cda3e21f4b47c" *)
Parameter tm_39cdf86d83c71365 : set.
(* Parameter tm_6d39c64862ac40c9 "6d39c64862ac40c95c6f5e4ed5f02bb019279bfb0cda8c9bbe0e1b813b1e876c" "6d39c64862ac40c95c6f5e4ed5f02bb019279bfb0cda8c9bbe0e1b813b1e876c" *)
Parameter tm_6d39c64862ac40c9 : (set -> set).
Definition tm_f7cd39d139f71b38 : set := ((tm_0a445311c45f0eb3 tm_39cdf86d83c71365) ((tm_b1b8f6f9d4d6136b tm_39cdf86d83c71365) (fun (x0 : set) => (tm_6d39c64862ac40c9 x0)))).
Theorem target_thm : ((forall (x0 : (set -> prop)), ((forall (x1 : set), (((tm_73c9efe869770ab4 x1) tm_39cdf86d83c71365) -> (x0 x1))) -> ((forall (x1 : set), (((tm_73c9efe869770ab4 x1) tm_39cdf86d83c71365) -> (x0 (tm_6d39c64862ac40c9 x1)))) -> (forall (x1 : set), (((tm_73c9efe869770ab4 x1) tm_f7cd39d139f71b38) -> (x0 x1)))))) -> (forall (x0 : prop), x0)).
exact (fun (x0 : (set -> prop)) => (fun (H0 : (forall (x1 : set), (((tm_73c9efe869770ab4 x1) tm_39cdf86d83c71365) -> (x0 x1)))) => (fun (H1 : (forall (x1 : set), (((tm_73c9efe869770ab4 x1) tm_39cdf86d83c71365) -> (x0 (tm_6d39c64862ac40c9 x1))))) => (fun (x1 : set) => (fun (H2 : ((tm_73c9efe869770ab4 x1) tm_f7cd39d139f71b38)) => (((((((kn_f270d6aed9b2d86f tm_39cdf86d83c71365) ((tm_b1b8f6f9d4d6136b tm_39cdf86d83c71365) (fun (x2 : set) => (tm_6d39c64862ac40c9 x2)))) x1) H2) (x0 x1)) (fun (H3 : ((tm_73c9efe869770ab4 x1) tm_39cdf86d83c71365)) => ((H0 x1) H3))) (fun (H3 : ((tm_73c9efe869770ab4 x1) ((tm_b1b8f6f9d4d6136b tm_39cdf86d83c71365) tm_6d39c64862ac40c9))) => ((((((kn_5a437ac4e488ce7d tm_39cdf86d83c71365) tm_6d39c64862ac40c9) x1) H3) (x0 x1)) (fun (x2 : set) => (fun (H4 : ((tm_73c9efe869770ab4 x2) tm_39cdf86d83c71365)) => (fun (H5 : (((tm_5a6af35fb6d6bea4 set) x1) (tm_6d39c64862ac40c9 x2))) => ((H5 (fun (x3 : set) => (fun (x4 : set) => (x0 x4)))) ((H1 x2) H4))))))))))))).
Qed.
