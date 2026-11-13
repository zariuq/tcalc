Definition tm_5bf697cb0d1cdefb : prop := (forall (x0 : prop), x0).
Definition tm_058f630dd89cad5a : (prop -> prop) := (fun (x0 : prop) => (x0 -> tm_5bf697cb0d1cdefb)).
Definition tm_87fba1d2da67f06e : (prop -> (prop -> prop)) := (fun (x0 : prop) => (fun (x1 : prop) => (forall (x2 : prop), ((x0 -> (x1 -> x2)) -> x2)))).
Section S1. Variable a0 : SType.
Definition tm_5a6af35fb6d6bea4 : (a0 -> (a0 -> prop)) := (fun (x0 : a0) => (fun (x1 : a0) => (forall (x2 : (a0 -> (a0 -> prop))), (((x2 x0) x1) -> ((x2 x1) x0))))).
End S1.
Section S2. Variable a0 : SType.
Definition tm_912ad2cdc2d23bb8 : ((a0 -> prop) -> prop) := (fun (x0 : (a0 -> prop)) => (forall (x1 : prop), ((forall (x2 : a0), ((x0 x2) -> x1)) -> x1))).
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
(* Parameter tm_3578b0d6a7b31871 "3578b0d6a7b318714bc5ea889c6a38cf27f08eaccfab7edbde3cb7a350cf2d9b" "3578b0d6a7b318714bc5ea889c6a38cf27f08eaccfab7edbde3cb7a350cf2d9b" *)
Parameter tm_3578b0d6a7b31871 : (prop -> (prop -> prop)).
Axiom kn_e7c3166e48d58a78 : (forall (x0 : set), (forall (x1 : (set -> set)), (forall (x2 : (set -> set)), ((forall (x3 : set), (((tm_73c9efe869770ab4 x3) x0) -> (((tm_5a6af35fb6d6bea4 set) (x1 x3)) (x2 x3)))) -> (((tm_5a6af35fb6d6bea4 set) ((tm_b1b8f6f9d4d6136b x0) (fun (x3 : set) => (x1 x3)))) ((tm_b1b8f6f9d4d6136b x0) (fun (x3 : set) => (x2 x3)))))))).
(* Parameter tm_158bae29452f8cbf "158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7" "158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7" *)
Parameter tm_158bae29452f8cbf : (set -> set).
(* Parameter tm_0a445311c45f0eb3 "0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e" "0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e" *)
Parameter tm_0a445311c45f0eb3 : (set -> (set -> set)).
Definition tm_153bff87325a9c75 : (set -> (set -> set)) := (fun (x0 : set) => (fun (x1 : set) => ((tm_0a445311c45f0eb3 x0) (tm_158bae29452f8cbf x1)))).
(* Parameter tm_f7e63d81e8f98ac9 "f7e63d81e8f98ac9bc7864e0b01f93952ef3b0cbf9777abab27bcbd743b6b079" "f7e63d81e8f98ac9bc7864e0b01f93952ef3b0cbf9777abab27bcbd743b6b079" *)
Parameter tm_f7e63d81e8f98ac9 : (set -> ((set -> prop) -> set)).
(* Parameter tm_f627d20f1b210634 "f627d20f1b21063483a5b96e4e2704bac09415a75fed6806a2587ce257f1f2fd" "f627d20f1b21063483a5b96e4e2704bac09415a75fed6806a2587ce257f1f2fd" *)
Parameter tm_f627d20f1b210634 : (set -> ((set -> prop) -> ((set -> set) -> set))).
(* Parameter tm_9db634daee7fc363 "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" *)
Parameter tm_9db634daee7fc363 : (set -> set).
Definition tm_dab6e51db9653e58 : (set -> prop) := (fun (x0 : set) => ((tm_87fba1d2da67f06e (tm_e7493d5f5a73b6cb x0)) (forall (x1 : set), (((tm_73c9efe869770ab4 x1) x0) -> (tm_e7493d5f5a73b6cb x1))))).
(* Parameter tm_2336eb45d48549dd "2336eb45d48549dd8a6a128edc17a8761fd9043c180691483bcf16e1acc9f00a" "2336eb45d48549dd8a6a128edc17a8761fd9043c180691483bcf16e1acc9f00a" *)
Parameter tm_2336eb45d48549dd : (set -> ((set -> prop) -> (set -> ((set -> prop) -> prop)))).
(* Parameter tm_1b39e85278dd9e82 "1b39e85278dd9e820e7b6258957386ac55934d784aa3702c57a28ec807453b01" "1b39e85278dd9e820e7b6258957386ac55934d784aa3702c57a28ec807453b01" *)
Parameter tm_1b39e85278dd9e82 : ((set -> ((set -> prop) -> prop)) -> ((set -> ((set -> prop) -> prop)) -> set)).
(* Parameter tm_be07c39b18a3aa93 "be07c39b18a3aa93f066f4c064fee3941ec27cfd07a4728b6209135c77ce5704" "be07c39b18a3aa93f066f4c064fee3941ec27cfd07a4728b6209135c77ce5704" *)
Parameter tm_be07c39b18a3aa93 : ((set -> ((set -> prop) -> prop)) -> ((set -> ((set -> prop) -> prop)) -> (set -> prop))).
Definition tm_1e55e667ef0bb79b : (set -> set) := (fun (x0 : set) => ((tm_0a445311c45f0eb3 x0) ((tm_b1b8f6f9d4d6136b x0) (fun (x1 : set) => ((fun (x2 : set) => ((tm_153bff87325a9c75 x2) (tm_158bae29452f8cbf (tm_9db634daee7fc363 tm_e2a83319facad3a3)))) x1))))).
Definition tm_3bbf071b189275f9 : (set -> (set -> prop)) := (fun (x0 : set) => (fun (x1 : set) => ((tm_87fba1d2da67f06e ((tm_8a8e36b858cd07fc x1) (tm_1e55e667ef0bb79b x0))) (forall (x2 : set), (((tm_73c9efe869770ab4 x2) x0) -> ((tm_3578b0d6a7b31871 ((tm_73c9efe869770ab4 ((fun (x3 : set) => ((tm_153bff87325a9c75 x3) (tm_158bae29452f8cbf (tm_9db634daee7fc363 tm_e2a83319facad3a3)))) x2)) x1)) ((tm_73c9efe869770ab4 x2) x1))))))).
Definition tm_89e534b3d5ad303c : (set -> ((set -> prop) -> set)) := (fun (x0 : set) => (fun (x1 : (set -> prop)) => ((tm_0a445311c45f0eb3 ((tm_f7e63d81e8f98ac9 x0) (fun (x2 : set) => (x1 x2)))) (((tm_f627d20f1b210634 x0) (fun (x2 : set) => (tm_058f630dd89cad5a (x1 x2)))) (fun (x2 : set) => ((fun (x3 : set) => ((tm_153bff87325a9c75 x3) (tm_158bae29452f8cbf (tm_9db634daee7fc363 tm_e2a83319facad3a3)))) x2)))))).
(* Parameter tm_87d7604c7ea9a2ae "87d7604c7ea9a2ae0537066afb358a94e6ac0cd80ba277e6b064422035a620cf" "87d7604c7ea9a2ae0537066afb358a94e6ac0cd80ba277e6b064422035a620cf" *)
Parameter tm_87d7604c7ea9a2ae : (set -> prop).
(* Parameter tm_bf1decfd8f4025a2 "bf1decfd8f4025a2271f2a64d1290eae65933d0f2f0f04b89520449195f1aeb8" "bf1decfd8f4025a2271f2a64d1290eae65933d0f2f0f04b89520449195f1aeb8" *)
Parameter tm_bf1decfd8f4025a2 : (set -> set).
Definition tm_0d574978cbb344ec : (set -> (set -> prop)) := (fun (x0 : set) => (fun (x1 : set) => ((((tm_2336eb45d48549dd (tm_bf1decfd8f4025a2 x0)) (fun (x2 : set) => ((tm_73c9efe869770ab4 x2) x0))) (tm_bf1decfd8f4025a2 x1)) (fun (x2 : set) => ((tm_73c9efe869770ab4 x2) x1))))).
Definition tm_0e3071dce24dfee0 : (set -> (set -> set)) := (fun (x0 : set) => (fun (x1 : set) => ((tm_89e534b3d5ad303c ((tm_1b39e85278dd9e82 (fun (x2 : set) => (fun (x3 : (set -> prop)) => ((tm_87fba1d2da67f06e (tm_dab6e51db9653e58 x2)) ((tm_73c9efe869770ab4 ((tm_89e534b3d5ad303c x2) x3)) x0))))) (fun (x2 : set) => (fun (x3 : (set -> prop)) => ((tm_87fba1d2da67f06e (tm_dab6e51db9653e58 x2)) ((tm_73c9efe869770ab4 ((tm_89e534b3d5ad303c x2) x3)) x1)))))) ((tm_be07c39b18a3aa93 (fun (x2 : set) => (fun (x3 : (set -> prop)) => ((tm_87fba1d2da67f06e (tm_dab6e51db9653e58 x2)) ((tm_73c9efe869770ab4 ((tm_89e534b3d5ad303c x2) x3)) x0))))) (fun (x2 : set) => (fun (x3 : (set -> prop)) => ((tm_87fba1d2da67f06e (tm_dab6e51db9653e58 x2)) ((tm_73c9efe869770ab4 ((tm_89e534b3d5ad303c x2) x3)) x1)))))))).
Definition tm_7df1da8a4be89c3e : (set -> set) := (fun (x0 : set) => ((tm_f7e63d81e8f98ac9 (tm_2a38dbb37506341b (tm_1e55e667ef0bb79b x0))) (fun (x1 : set) => ((tm_912ad2cdc2d23bb8 set) (fun (x2 : set) => ((tm_87fba1d2da67f06e ((tm_73c9efe869770ab4 x2) x0)) ((tm_3bbf071b189275f9 x2) x1))))))).
Definition tm_08c87b1a5ce6404b : (set -> set) := (fun (x0 : set) => ((tm_f7e63d81e8f98ac9 (tm_7df1da8a4be89c3e (tm_bf1decfd8f4025a2 x0))) (fun (x1 : set) => ((tm_0d574978cbb344ec x1) x0)))).
Definition tm_df0c7f1a5ed1eb8a : (set -> set) := (fun (x0 : set) => ((tm_f7e63d81e8f98ac9 (tm_7df1da8a4be89c3e (tm_bf1decfd8f4025a2 x0))) (fun (x1 : set) => ((tm_0d574978cbb344ec x0) x1)))).
Axiom kn_31b2acc991348788 : (forall (x0 : set), ((tm_87d7604c7ea9a2ae x0) -> (forall (x1 : set), (((tm_73c9efe869770ab4 x1) (tm_08c87b1a5ce6404b x0)) -> ((tm_73c9efe869770ab4 x1) (tm_7df1da8a4be89c3e (tm_bf1decfd8f4025a2 x0))))))).
Axiom kn_2dc5ff1f91f11220 : (forall (x0 : set), ((tm_87d7604c7ea9a2ae x0) -> (forall (x1 : set), (((tm_73c9efe869770ab4 x1) (tm_df0c7f1a5ed1eb8a x0)) -> ((tm_73c9efe869770ab4 x1) (tm_7df1da8a4be89c3e (tm_bf1decfd8f4025a2 x0))))))).
(* Parameter tm_352082c509ab97c1 "352082c509ab97c1757375f37a2ac62ed806c7b39944c98161720a584364bfaf" "352082c509ab97c1757375f37a2ac62ed806c7b39944c98161720a584364bfaf" *)
Parameter tm_352082c509ab97c1 : ((set -> ((set -> set) -> set)) -> (set -> set)).
Axiom kn_6ab3c415e6fdbeb4 : (forall (x0 : (set -> ((set -> set) -> set))), ((forall (x1 : set), ((tm_87d7604c7ea9a2ae x1) -> (forall (x2 : (set -> set)), (forall (x3 : (set -> set)), ((forall (x4 : set), (((tm_73c9efe869770ab4 x4) (tm_7df1da8a4be89c3e (tm_bf1decfd8f4025a2 x1))) -> (((tm_5a6af35fb6d6bea4 set) (x2 x4)) (x3 x4)))) -> (((tm_5a6af35fb6d6bea4 set) ((x0 x1) x2)) ((x0 x1) x3))))))) -> (forall (x1 : set), ((tm_87d7604c7ea9a2ae x1) -> (((tm_5a6af35fb6d6bea4 set) ((tm_352082c509ab97c1 x0) x1)) ((x0 x1) (tm_352082c509ab97c1 x0))))))).
Definition tm_6d39c64862ac40c9 : (set -> set) := (tm_352082c509ab97c1 (fun (x0 : set) => (fun (x1 : (set -> set)) => ((tm_0e3071dce24dfee0 ((tm_b1b8f6f9d4d6136b (tm_df0c7f1a5ed1eb8a x0)) (fun (x2 : set) => (x1 x2)))) ((tm_b1b8f6f9d4d6136b (tm_08c87b1a5ce6404b x0)) (fun (x2 : set) => (x1 x2))))))).
Theorem target_thm : (forall (x0 : set), ((tm_87d7604c7ea9a2ae x0) -> (((tm_5a6af35fb6d6bea4 set) (tm_6d39c64862ac40c9 x0)) ((tm_0e3071dce24dfee0 ((tm_b1b8f6f9d4d6136b (tm_df0c7f1a5ed1eb8a x0)) (fun (x1 : set) => (tm_6d39c64862ac40c9 x1)))) ((tm_b1b8f6f9d4d6136b (tm_08c87b1a5ce6404b x0)) (fun (x1 : set) => (tm_6d39c64862ac40c9 x1))))))).
exact ((fun (H0 : (forall (x0 : set), ((tm_87d7604c7ea9a2ae x0) -> (forall (x1 : (set -> set)), (forall (x2 : (set -> set)), ((forall (x3 : set), (((tm_73c9efe869770ab4 x3) (tm_7df1da8a4be89c3e (tm_bf1decfd8f4025a2 x0))) -> (((tm_5a6af35fb6d6bea4 set) (x1 x3)) (x2 x3)))) -> (((tm_5a6af35fb6d6bea4 set) ((tm_0e3071dce24dfee0 ((tm_b1b8f6f9d4d6136b (tm_df0c7f1a5ed1eb8a x0)) (fun (x3 : set) => (x1 x3)))) ((tm_b1b8f6f9d4d6136b (tm_08c87b1a5ce6404b x0)) (fun (x3 : set) => (x1 x3))))) ((tm_0e3071dce24dfee0 ((tm_b1b8f6f9d4d6136b (tm_df0c7f1a5ed1eb8a x0)) (fun (x3 : set) => (x2 x3)))) ((tm_b1b8f6f9d4d6136b (tm_08c87b1a5ce6404b x0)) (fun (x3 : set) => (x2 x3))))))))))) => ((kn_6ab3c415e6fdbeb4 (fun (x0 : set) => (fun (x1 : (set -> set)) => ((tm_0e3071dce24dfee0 ((tm_b1b8f6f9d4d6136b (tm_df0c7f1a5ed1eb8a x0)) (fun (x2 : set) => (x1 x2)))) ((tm_b1b8f6f9d4d6136b (tm_08c87b1a5ce6404b x0)) (fun (x2 : set) => (x1 x2))))))) H0)) (fun (x0 : set) => (fun (H0 : (tm_87d7604c7ea9a2ae x0)) => (fun (x1 : (set -> set)) => (fun (x2 : (set -> set)) => (fun (H1 : (forall (x3 : set), (((tm_73c9efe869770ab4 x3) (tm_7df1da8a4be89c3e (tm_bf1decfd8f4025a2 x0))) -> (((tm_5a6af35fb6d6bea4 set) (x1 x3)) (x2 x3))))) => ((fun (H2 : (((tm_5a6af35fb6d6bea4 set) ((tm_b1b8f6f9d4d6136b (tm_df0c7f1a5ed1eb8a x0)) (fun (x3 : set) => (x1 x3)))) ((tm_b1b8f6f9d4d6136b (tm_df0c7f1a5ed1eb8a x0)) (fun (x3 : set) => (x2 x3))))) => ((fun (H3 : (((tm_5a6af35fb6d6bea4 set) ((tm_b1b8f6f9d4d6136b (tm_08c87b1a5ce6404b x0)) (fun (x3 : set) => (x1 x3)))) ((tm_b1b8f6f9d4d6136b (tm_08c87b1a5ce6404b x0)) (fun (x3 : set) => (x2 x3))))) => ((H1 (fun (x3 : set) => (fun (x4 : set) => (((tm_5a6af35fb6d6bea4 set) ((tm_0e3071dce24dfee0 x4) ((tm_b1b8f6f9d4d6136b (tm_08c87b1a5ce6404b x0)) (fun (x5 : set) => (x1 x5))))) ((tm_0e3071dce24dfee0 ((tm_b1b8f6f9d4d6136b (tm_df0c7f1a5ed1eb8a x0)) (fun (x5 : set) => (x2 x5)))) ((tm_b1b8f6f9d4d6136b (tm_08c87b1a5ce6404b x0)) (fun (x5 : set) => (x2 x5)))))))) ((H3 (fun (x3 : set) => (fun (x4 : set) => (((tm_5a6af35fb6d6bea4 set) ((tm_0e3071dce24dfee0 ((tm_b1b8f6f9d4d6136b (tm_df0c7f1a5ed1eb8a x0)) (fun (x5 : set) => (x2 x5)))) x4)) ((tm_0e3071dce24dfee0 ((tm_b1b8f6f9d4d6136b (tm_df0c7f1a5ed1eb8a x0)) (fun (x5 : set) => (x2 x5)))) ((tm_b1b8f6f9d4d6136b (tm_08c87b1a5ce6404b x0)) (fun (x5 : set) => (x2 x5)))))))) (fun (x3 : (set -> (set -> prop))) => (fun (H4 : ((x3 ((tm_0e3071dce24dfee0 ((tm_b1b8f6f9d4d6136b (tm_df0c7f1a5ed1eb8a x0)) (fun (x4 : set) => (x2 x4)))) ((tm_b1b8f6f9d4d6136b (tm_08c87b1a5ce6404b x0)) (fun (x4 : set) => (x2 x4))))) ((tm_0e3071dce24dfee0 ((tm_b1b8f6f9d4d6136b (tm_df0c7f1a5ed1eb8a x0)) (fun (x4 : set) => (x2 x4)))) ((tm_b1b8f6f9d4d6136b (tm_08c87b1a5ce6404b x0)) (fun (x4 : set) => (x2 x4)))))) => H4))))) ((((kn_e7c3166e48d58a78 (tm_08c87b1a5ce6404b x0)) (fun (x3 : set) => (x1 x3))) (fun (x3 : set) => (x2 x3))) (fun (x3 : set) => (fun (H3 : ((tm_73c9efe869770ab4 x3) (tm_08c87b1a5ce6404b x0))) => ((H1 x3) ((((kn_31b2acc991348788 x0) H0) x3) H3))))))) ((((kn_e7c3166e48d58a78 (tm_df0c7f1a5ed1eb8a x0)) (fun (x3 : set) => (x1 x3))) (fun (x3 : set) => (x2 x3))) (fun (x3 : set) => (fun (H2 : ((tm_73c9efe869770ab4 x3) (tm_df0c7f1a5ed1eb8a x0))) => ((H1 x3) ((((kn_2dc5ff1f91f11220 x0) H0) x3) H2)))))))))))).
Qed.
