Definition tm_87fba1d2da67f06e : (prop -> (prop -> prop)) := (fun (x0 : prop) => (fun (x1 : prop) => (forall (x2 : prop), ((x0 -> (x1 -> x2)) -> x2)))).
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
Axiom kn_7f6246d08629eeb1 : (forall (x0 : prop), (forall (x1 : prop), (x0 -> (x1 -> ((tm_87fba1d2da67f06e x0) x1))))).
Theorem target_thm : (forall (x0 : prop), (forall (x1 : prop), (forall (x2 : prop), (x0 -> (x1 -> (x2 -> ((tm_87fba1d2da67f06e ((tm_87fba1d2da67f06e x0) x1)) x2))))))).
exact (fun (x0 : prop) => (fun (x1 : prop) => (fun (x2 : prop) => (fun (H0 : x0) => (fun (H1 : x1) => (fun (H2 : x2) => ((((kn_7f6246d08629eeb1 (fun (x3 : prop) => x3)) x2) ((((kn_7f6246d08629eeb1 x0) x1) H0) H1)) H2))))))).
Qed.
