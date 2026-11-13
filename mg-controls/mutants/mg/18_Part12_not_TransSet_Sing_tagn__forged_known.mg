Definition tm_5bf697cb0d1cdefb : prop := (forall (x0 : prop), x0).
Definition tm_058f630dd89cad5a : (prop -> prop) := (fun (x0 : prop) => (x0 -> tm_5bf697cb0d1cdefb)).
Section S1. Variable a0 : SType.
Definition tm_5a6af35fb6d6bea4 : (a0 -> (a0 -> prop)) := (fun (x0 : a0) => (fun (x1 : a0) => (forall (x2 : (a0 -> (a0 -> prop))), (((x2 x0) x1) -> ((x2 x1) x0))))).
End S1.
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
Axiom kn_092f94151e13afcf : (forall (x0 : set), (forall (x1 : set), (((tm_73c9efe869770ab4 x0) x1) -> (((tm_73c9efe869770ab4 x1) x0) -> tm_5bf697cb0d1cdefb)))).
(* Parameter tm_9db634daee7fc363 "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" *)
Parameter tm_9db634daee7fc363 : (set -> set).
Axiom kn_4675abc9d31454cc : ((tm_73c9efe869770ab4 tm_e2a83319facad3a3) (tm_9db634daee7fc363 tm_e2a83319facad3a3)).
Definition tm_25c483dc8509e17d : (set -> prop) := (fun (x0 : set) => (forall (x1 : (set -> prop)), ((x1 tm_e2a83319facad3a3) -> ((forall (x2 : set), ((x1 x2) -> (x1 (tm_9db634daee7fc363 x2)))) -> (x1 x0))))).
Axiom kn_ad6e9c68eaa15a57 : (forall (x0 : set), ((tm_25c483dc8509e17d x0) -> (forall (x1 : set), (((tm_73c9efe869770ab4 x1) x0) -> ((tm_8a8e36b858cd07fc x1) x0))))).
Theorem target_thm : (forall (x0 : set), ((tm_25c483dc8509e17d x0) -> (((tm_73c9efe869770ab4 (tm_9db634daee7fc363 tm_e2a83319facad3a3)) x0) -> (tm_058f630dd89cad5a (tm_e7493d5f5a73b6cb (tm_158bae29452f8cbf x0)))))).
exact (fun (x0 : set) => (fun (H0 : (tm_25c483dc8509e17d x0)) => (fun (H1 : ((tm_73c9efe869770ab4 (tm_9db634daee7fc363 tm_e2a83319facad3a3)) x0)) => (fun (H2 : (tm_e7493d5f5a73b6cb (tm_158bae29452f8cbf x0))) => ((fun (H3 : ((tm_73c9efe869770ab4 tm_e2a83319facad3a3) (tm_158bae29452f8cbf x0))) => ((((kn_0000000000000000 tm_e2a83319facad3a3) (tm_9db634daee7fc363 tm_e2a83319facad3a3)) kn_4675abc9d31454cc) (((((kn_032df44ded59d711 x0) tm_e2a83319facad3a3) H3) (fun (x1 : set) => (fun (x2 : set) => ((tm_73c9efe869770ab4 (tm_9db634daee7fc363 tm_e2a83319facad3a3)) x2)))) H1))) ((((H2 x0) (kn_77b0506ab5458ffa x0)) tm_e2a83319facad3a3) ((((((kn_ad6e9c68eaa15a57 x0) H0) (tm_9db634daee7fc363 tm_e2a83319facad3a3)) H1) tm_e2a83319facad3a3) kn_4675abc9d31454cc))))))).
Qed.
