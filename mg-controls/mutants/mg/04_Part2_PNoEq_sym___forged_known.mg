Definition tm_87fba1d2da67f06e : (prop -> (prop -> prop)) := (fun (x0 : prop) => (fun (x1 : prop) => (forall (x2 : prop), ((x0 -> (x1 -> x2)) -> x2)))).
Definition tm_9c60bab687728bc4 : (prop -> (prop -> prop)) := (fun (x0 : prop) => (fun (x1 : prop) => ((tm_87fba1d2da67f06e (x0 -> x1)) (x1 -> x0)))).
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
Axiom kn_216084b9a145fac8 : (forall (x0 : prop), (forall (x1 : prop), (((tm_9c60bab687728bc4 x0) x1) -> ((tm_9c60bab687728bc4 x1) x0)))).
Definition tm_ac96e86902ef72d5 : (set -> ((set -> prop) -> ((set -> prop) -> prop))) := (fun (x0 : set) => (fun (x1 : (set -> prop)) => (fun (x2 : (set -> prop)) => (forall (x3 : set), (((tm_73c9efe869770ab4 x3) x0) -> ((tm_9c60bab687728bc4 (x1 x3)) (x2 x3))))))).
Theorem target_thm : (forall (x0 : set), (forall (x1 : (set -> prop)), (forall (x2 : (set -> prop)), ((((tm_ac96e86902ef72d5 x0) x1) x2) -> (((tm_ac96e86902ef72d5 x0) x2) x1))))).
exact (fun (x0 : set) => (fun (x1 : (set -> prop)) => (fun (x2 : (set -> prop)) => (fun (H0 : (((tm_ac96e86902ef72d5 x0) x1) x2)) => (fun (x3 : set) => (fun (H1 : ((tm_73c9efe869770ab4 x3) x0)) => (((kn_0000000000000000 (x1 x3)) (x2 x3)) ((H0 x3) H1)))))))).
Qed.
