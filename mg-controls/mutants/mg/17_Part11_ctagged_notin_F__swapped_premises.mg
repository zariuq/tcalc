Definition tm_5bf697cb0d1cdefb : prop := (forall (x0 : prop), x0).
Definition tm_058f630dd89cad5a : (prop -> prop) := (fun (x0 : prop) => (x0 -> tm_5bf697cb0d1cdefb)).
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
Definition tm_2f8b7f287504f141 : (set -> (set -> prop)) := (fun (x0 : set) => (fun (x1 : set) => (tm_058f630dd89cad5a ((tm_73c9efe869770ab4 x0) x1)))).
(* Parameter tm_158bae29452f8cbf "158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7" "158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7" *)
Parameter tm_158bae29452f8cbf : (set -> set).
Axiom kn_77b0506ab5458ffa : (forall (x0 : set), ((tm_73c9efe869770ab4 x0) (tm_158bae29452f8cbf x0))).
(* Parameter tm_0a445311c45f0eb3 "0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e" "0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e" *)
Parameter tm_0a445311c45f0eb3 : (set -> (set -> set)).
Axiom kn_c5d368c671e9b46c : (forall (x0 : set), (forall (x1 : set), (forall (x2 : set), (((tm_73c9efe869770ab4 x2) x1) -> ((tm_73c9efe869770ab4 x2) ((tm_0a445311c45f0eb3 x0) x1)))))).
Definition tm_153bff87325a9c75 : (set -> (set -> set)) := (fun (x0 : set) => (fun (x1 : set) => ((tm_0a445311c45f0eb3 x0) (tm_158bae29452f8cbf x1)))).
Theorem target_thm : (forall (x0 : set), (forall (x1 : (set -> prop)), ((forall (x2 : set), ((x1 x2) -> (forall (x3 : set), (((tm_73c9efe869770ab4 x3) x2) -> ((tm_2f8b7f287504f141 x0) x3))))) -> (forall (x2 : set), (forall (x3 : set), ((x1 x2) -> ((tm_2f8b7f287504f141 ((fun (x4 : set) => ((tm_153bff87325a9c75 x4) x0)) x3)) x2))))))).
exact (fun (x0 : set) => (fun (x1 : (set -> prop)) => (fun (H0 : (forall (x2 : set), ((x1 x2) -> (forall (x3 : set), (((tm_73c9efe869770ab4 x3) x2) -> ((tm_2f8b7f287504f141 x0) x3)))))) => (fun (x2 : set) => (fun (x3 : set) => (fun (H1 : (x1 x2)) => (fun (H2 : ((tm_73c9efe869770ab4 ((fun (x4 : set) => ((tm_153bff87325a9c75 x4) x0)) x3)) x2)) => (((((kn_c5d368c671e9b46c x3) (tm_158bae29452f8cbf x0)) x0) (kn_77b0506ab5458ffa x0)) ((((H0 x2) H1) ((fun (x4 : set) => ((tm_153bff87325a9c75 x4) x0)) x3)) H2))))))))).
Qed.
