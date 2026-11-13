Definition tm_5bf697cb0d1cdefb : prop := (forall (x0 : prop), x0).
Definition tm_058f630dd89cad5a : (prop -> prop) := (fun (x0 : prop) => (x0 -> tm_5bf697cb0d1cdefb)).
Section S1. Variable a0 : SType.
Definition tm_5a6af35fb6d6bea4 : (a0 -> (a0 -> prop)) := (fun (x0 : a0) => (fun (x1 : a0) => (forall (x2 : (a0 -> (a0 -> prop))), (((x2 x0) x1) -> ((x2 x1) x0))))).
End S1.
Section S2. Variable a0 : SType.
Definition tm_7966a66a9bb19810 : (a0 -> (a0 -> prop)) := (fun (x0 : a0) => (fun (x1 : a0) => (tm_058f630dd89cad5a (((tm_5a6af35fb6d6bea4 a0) x0) x1)))).
End S2.
Parameter In : (set -> (set -> prop)).
Definition tm_73c9efe869770ab4 : (set -> (set -> prop)) := In.
Definition tm_8a8e36b858cd07fc : (set -> (set -> prop)) := (fun (x0 : set) => (fun (x1 : set) => (forall (x2 : set), (((tm_73c9efe869770ab4 x2) x0) -> ((tm_73c9efe869770ab4 x2) x1))))).
Parameter Empty : set.
Definition tm_e2a83319facad3a3 : set := Empty.
Parameter Union : (set -> set).
Definition tm_844774016d959cff : (set -> set) := Union.
Parameter Power : (set -> set).
Definition tm_2a38dbb37506341b : (set -> set) := Power.
Parameter Repl : (set -> ((set -> set) -> set)).
Definition tm_b1b8f6f9d4d6136b : (set -> ((set -> set) -> set)) := Repl.
Definition tm_e7493d5f5a73b6cb : (set -> prop) := (fun (x0 : set) => (forall (x1 : set), (((tm_73c9efe869770ab4 x1) x0) -> ((tm_8a8e36b858cd07fc x1) x0)))).
Parameter UnivOf : (set -> set).
Definition tm_5a50bfe3a33a99c3 : (set -> set) := UnivOf.
(* Parameter tm_158bae29452f8cbf "158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7" "158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7" *)
Parameter tm_158bae29452f8cbf : (set -> set).
Axiom kn_77b0506ab5458ffa : (forall (x0 : set), ((tm_73c9efe869770ab4 x0) (tm_158bae29452f8cbf x0))).
Axiom kn_032df44ded59d711 : (forall (x0 : set), (forall (x1 : set), (((tm_73c9efe869770ab4 x1) (tm_158bae29452f8cbf x0)) -> (((tm_5a6af35fb6d6bea4 set) x1) x0)))).
(* Parameter tm_9db634daee7fc363 "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" *)
Parameter tm_9db634daee7fc363 : (set -> set).
Axiom kn_4675abc9d31454cc : ((tm_73c9efe869770ab4 tm_e2a83319facad3a3) (tm_9db634daee7fc363 tm_e2a83319facad3a3)).
Axiom kn_2a012236fc59f277 : (((tm_7966a66a9bb19810 set) tm_e2a83319facad3a3) (tm_9db634daee7fc363 tm_e2a83319facad3a3)).
Theorem target_thm : (tm_058f630dd89cad5a (tm_e7493d5f5a73b6cb (tm_158bae29452f8cbf (tm_9db634daee7fc363 tm_e2a83319facad3a3)))).
exact (fun (H0 : (tm_e7493d5f5a73b6cb (tm_158bae29452f8cbf (tm_9db634daee7fc363 tm_e2a83319facad3a3)))) => ((fun (H1 : ((tm_73c9efe869770ab4 tm_e2a83319facad3a3) (tm_158bae29452f8cbf (tm_9db634daee7fc363 tm_e2a83319facad3a3)))) => (kn_2a012236fc59f277 (((kn_032df44ded59d711 (tm_9db634daee7fc363 tm_e2a83319facad3a3)) tm_e2a83319facad3a3) H0))) ((((H0 (tm_9db634daee7fc363 tm_e2a83319facad3a3)) (kn_77b0506ab5458ffa (tm_9db634daee7fc363 tm_e2a83319facad3a3))) tm_e2a83319facad3a3) kn_4675abc9d31454cc))).
Qed.
