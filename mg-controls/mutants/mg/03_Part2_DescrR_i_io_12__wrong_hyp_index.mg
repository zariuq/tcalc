(* Parameter tm_174b78e53fc239e8 "174b78e53fc239e8c2aab4ab5a996a27e3e5741e88070dad186e05fb13f275e5" "174b78e53fc239e8c2aab4ab5a996a27e3e5741e88070dad186e05fb13f275e5" *)
Parameter tm_174b78e53fc239e8 : ((set -> prop) -> set).
Definition tm_87fba1d2da67f06e : (prop -> (prop -> prop)) := (fun (x0 : prop) => (fun (x1 : prop) => (forall (x2 : prop), ((x0 -> (x1 -> x2)) -> x2)))).
Section S1. Variable a0 : SType.
Definition tm_5a6af35fb6d6bea4 : (a0 -> (a0 -> prop)) := (fun (x0 : a0) => (fun (x1 : a0) => (forall (x2 : (a0 -> (a0 -> prop))), (((x2 x0) x1) -> ((x2 x1) x0))))).
End S1.
Section S2. Variable a0 : SType.
Definition tm_912ad2cdc2d23bb8 : ((a0 -> prop) -> prop) := (fun (x0 : (a0 -> prop)) => (forall (x1 : prop), ((forall (x2 : a0), ((x0 x2) -> x1)) -> x1))).
End S2.
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
Axiom kn_8769902da7e6c4b8 : (forall (x0 : (set -> prop)), (((tm_912ad2cdc2d23bb8 set) (fun (x1 : set) => (x0 x1))) -> (x0 (tm_174b78e53fc239e8 x0)))).
(* Parameter tm_322bf09a1711d51a "322bf09a1711d51a4512e112e1767cb2616a7708dc89d7312c8064cfee6e3315" "322bf09a1711d51a4512e112e1767cb2616a7708dc89d7312c8064cfee6e3315" *)
Parameter tm_322bf09a1711d51a : (((set -> prop) -> prop) -> (set -> prop)).
Axiom kn_503f5c46cb16e766 : (forall (x0 : ((set -> prop) -> prop)), (((tm_912ad2cdc2d23bb8 (set -> prop)) (fun (x1 : (set -> prop)) => (x0 x1))) -> ((forall (x1 : (set -> prop)), (forall (x2 : (set -> prop)), ((x0 x1) -> ((x0 x2) -> (((tm_5a6af35fb6d6bea4 (set -> prop)) x1) x2))))) -> (x0 (tm_322bf09a1711d51a x0))))).
Definition tm_1f005fdad5c6f987 : ((set -> ((set -> prop) -> prop)) -> set) := (fun (x0 : (set -> ((set -> prop) -> prop))) => (tm_174b78e53fc239e8 (fun (x1 : set) => ((tm_87fba1d2da67f06e ((tm_912ad2cdc2d23bb8 (set -> prop)) (fun (x2 : (set -> prop)) => ((x0 x1) x2)))) (forall (x2 : (set -> prop)), (forall (x3 : (set -> prop)), (((x0 x1) x2) -> (((x0 x1) x3) -> (((tm_5a6af35fb6d6bea4 (set -> prop)) x2) x3))))))))).
Definition tm_28d8599686476258 : ((set -> ((set -> prop) -> prop)) -> (set -> prop)) := (fun (x0 : (set -> ((set -> prop) -> prop))) => (tm_322bf09a1711d51a (fun (x1 : (set -> prop)) => ((x0 (tm_1f005fdad5c6f987 x0)) x1)))).
Theorem target_thm : (forall (x0 : (set -> ((set -> prop) -> prop))), (((tm_912ad2cdc2d23bb8 set) (fun (x1 : set) => ((tm_87fba1d2da67f06e ((tm_912ad2cdc2d23bb8 (set -> prop)) (fun (x2 : (set -> prop)) => ((x0 x1) x2)))) (forall (x2 : (set -> prop)), (forall (x3 : (set -> prop)), (((x0 x1) x2) -> (((x0 x1) x3) -> (((tm_5a6af35fb6d6bea4 (set -> prop)) x2) x3)))))))) -> ((x0 (tm_1f005fdad5c6f987 x0)) (tm_28d8599686476258 x0)))).
exact (fun (x0 : (set -> ((set -> prop) -> prop))) => (fun (H0 : ((tm_912ad2cdc2d23bb8 set) (fun (x1 : set) => ((tm_87fba1d2da67f06e ((tm_912ad2cdc2d23bb8 (set -> prop)) (fun (x2 : (set -> prop)) => ((x0 x1) x2)))) (forall (x2 : (set -> prop)), (forall (x3 : (set -> prop)), (((x0 x1) x2) -> (((x0 x1) x3) -> (((tm_5a6af35fb6d6bea4 (set -> prop)) x2) x3))))))))) => ((fun (H1 : ((tm_87fba1d2da67f06e ((tm_912ad2cdc2d23bb8 (set -> prop)) (fun (x1 : (set -> prop)) => ((x0 (tm_1f005fdad5c6f987 x0)) x1)))) (forall (x1 : (set -> prop)), (forall (x2 : (set -> prop)), (((x0 (tm_1f005fdad5c6f987 x0)) x1) -> (((x0 (tm_1f005fdad5c6f987 x0)) x2) -> (((tm_5a6af35fb6d6bea4 (set -> prop)) x1) x2))))))) => ((H0 ((x0 (tm_1f005fdad5c6f987 x0)) (tm_28d8599686476258 x0))) (fun (H2 : ((tm_912ad2cdc2d23bb8 (set -> prop)) (fun (x1 : (set -> prop)) => ((x0 (tm_1f005fdad5c6f987 x0)) x1)))) => (fun (H3 : (forall (x1 : (set -> prop)), (forall (x2 : (set -> prop)), (((x0 (tm_1f005fdad5c6f987 x0)) x1) -> (((x0 (tm_1f005fdad5c6f987 x0)) x2) -> (((tm_5a6af35fb6d6bea4 (set -> prop)) x1) x2)))))) => (((kn_503f5c46cb16e766 (fun (x1 : (set -> prop)) => ((x0 (tm_1f005fdad5c6f987 x0)) x1))) H2) H3))))) ((kn_8769902da7e6c4b8 (fun (x1 : set) => ((tm_87fba1d2da67f06e ((tm_912ad2cdc2d23bb8 (set -> prop)) (fun (x2 : (set -> prop)) => ((x0 x1) x2)))) (forall (x2 : (set -> prop)), (forall (x3 : (set -> prop)), (((x0 x1) x2) -> (((x0 x1) x3) -> (((tm_5a6af35fb6d6bea4 (set -> prop)) x2) x3)))))))) H0)))).
Qed.
