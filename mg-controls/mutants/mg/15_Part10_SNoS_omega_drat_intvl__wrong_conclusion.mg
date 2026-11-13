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
Axiom kn_7f6246d08629eeb1 : (forall (x0 : prop), (forall (x1 : prop), (x0 -> (x1 -> ((tm_87fba1d2da67f06e x0) x1))))).
(* Parameter tm_3578b0d6a7b31871 "3578b0d6a7b318714bc5ea889c6a38cf27f08eaccfab7edbde3cb7a350cf2d9b" "3578b0d6a7b318714bc5ea889c6a38cf27f08eaccfab7edbde3cb7a350cf2d9b" *)
Parameter tm_3578b0d6a7b31871 : (prop -> (prop -> prop)).
(* Parameter tm_158bae29452f8cbf "158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7" "158bae29452f8cbf276df6f8db2be0a5d20290e15eca88ffe1e7b41d211d41d7" *)
Parameter tm_158bae29452f8cbf : (set -> set).
(* Parameter tm_0a445311c45f0eb3 "0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e" "0a445311c45f0eb3ba2217c35ecb47f122b2301b2b80124922fbf03a5c4d223e" *)
Parameter tm_0a445311c45f0eb3 : (set -> (set -> set)).
Definition tm_153bff87325a9c75 : (set -> (set -> set)) := (fun (x0 : set) => (fun (x1 : set) => ((tm_0a445311c45f0eb3 x0) (tm_158bae29452f8cbf x1)))).
(* Parameter tm_f7e63d81e8f98ac9 "f7e63d81e8f98ac9bc7864e0b01f93952ef3b0cbf9777abab27bcbd743b6b079" "f7e63d81e8f98ac9bc7864e0b01f93952ef3b0cbf9777abab27bcbd743b6b079" *)
Parameter tm_f7e63d81e8f98ac9 : (set -> ((set -> prop) -> set)).
(* Parameter tm_9db634daee7fc363 "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" "9db634daee7fc36315ddda5f5f694934869921e9c5f55e8b25c91c0a07c5cbec" *)
Parameter tm_9db634daee7fc363 : (set -> set).
Definition tm_25c483dc8509e17d : (set -> prop) := (fun (x0 : set) => (forall (x1 : (set -> prop)), ((x1 tm_e2a83319facad3a3) -> ((forall (x2 : set), ((x1 x2) -> (x1 (tm_9db634daee7fc363 x2)))) -> (x1 x0))))).
(* Parameter tm_39cdf86d83c71365 "39cdf86d83c7136517f803d29d0c748ea45a274ccbf9b8488f9cda3e21f4b47c" "39cdf86d83c7136517f803d29d0c748ea45a274ccbf9b8488f9cda3e21f4b47c" *)
Parameter tm_39cdf86d83c71365 : set.
Axiom kn_7d6896163f052ef5 : (forall (x0 : set), (((tm_73c9efe869770ab4 x0) tm_39cdf86d83c71365) -> (tm_25c483dc8509e17d x0))).
Axiom kn_f88efc1bceb13c96 : (forall (x0 : set), (((tm_73c9efe869770ab4 x0) tm_39cdf86d83c71365) -> ((tm_73c9efe869770ab4 (tm_9db634daee7fc363 x0)) tm_39cdf86d83c71365))).
Definition tm_dab6e51db9653e58 : (set -> prop) := (fun (x0 : set) => ((tm_87fba1d2da67f06e (tm_e7493d5f5a73b6cb x0)) (forall (x1 : set), (((tm_73c9efe869770ab4 x1) x0) -> (tm_e7493d5f5a73b6cb x1))))).
Axiom kn_97063ca423850207 : (tm_dab6e51db9653e58 tm_39cdf86d83c71365).
(* Parameter tm_2336eb45d48549dd "2336eb45d48549dd8a6a128edc17a8761fd9043c180691483bcf16e1acc9f00a" "2336eb45d48549dd8a6a128edc17a8761fd9043c180691483bcf16e1acc9f00a" *)
Parameter tm_2336eb45d48549dd : (set -> ((set -> prop) -> (set -> ((set -> prop) -> prop)))).
Definition tm_1e55e667ef0bb79b : (set -> set) := (fun (x0 : set) => ((tm_0a445311c45f0eb3 x0) ((tm_b1b8f6f9d4d6136b x0) (fun (x1 : set) => ((fun (x2 : set) => ((tm_153bff87325a9c75 x2) (tm_158bae29452f8cbf (tm_9db634daee7fc363 tm_e2a83319facad3a3)))) x1))))).
Definition tm_3bbf071b189275f9 : (set -> (set -> prop)) := (fun (x0 : set) => (fun (x1 : set) => ((tm_87fba1d2da67f06e ((tm_8a8e36b858cd07fc x1) (tm_1e55e667ef0bb79b x0))) (forall (x2 : set), (((tm_73c9efe869770ab4 x2) x0) -> ((tm_3578b0d6a7b31871 ((tm_73c9efe869770ab4 ((fun (x3 : set) => ((tm_153bff87325a9c75 x3) (tm_158bae29452f8cbf (tm_9db634daee7fc363 tm_e2a83319facad3a3)))) x2)) x1)) ((tm_73c9efe869770ab4 x2) x1))))))).
(* Parameter tm_87d7604c7ea9a2ae "87d7604c7ea9a2ae0537066afb358a94e6ac0cd80ba277e6b064422035a620cf" "87d7604c7ea9a2ae0537066afb358a94e6ac0cd80ba277e6b064422035a620cf" *)
Parameter tm_87d7604c7ea9a2ae : (set -> prop).
(* Parameter tm_bf1decfd8f4025a2 "bf1decfd8f4025a2271f2a64d1290eae65933d0f2f0f04b89520449195f1aeb8" "bf1decfd8f4025a2271f2a64d1290eae65933d0f2f0f04b89520449195f1aeb8" *)
Parameter tm_bf1decfd8f4025a2 : (set -> set).
Definition tm_0d574978cbb344ec : (set -> (set -> prop)) := (fun (x0 : set) => (fun (x1 : set) => ((((tm_2336eb45d48549dd (tm_bf1decfd8f4025a2 x0)) (fun (x2 : set) => ((tm_73c9efe869770ab4 x2) x0))) (tm_bf1decfd8f4025a2 x1)) (fun (x2 : set) => ((tm_73c9efe869770ab4 x2) x1))))).
Definition tm_7df1da8a4be89c3e : (set -> set) := (fun (x0 : set) => ((tm_f7e63d81e8f98ac9 (tm_2a38dbb37506341b (tm_1e55e667ef0bb79b x0))) (fun (x1 : set) => ((tm_912ad2cdc2d23bb8 set) (fun (x2 : set) => ((tm_87fba1d2da67f06e ((tm_73c9efe869770ab4 x2) x0)) ((tm_3bbf071b189275f9 x2) x1))))))).
Axiom kn_ad91f617a46a583c : (forall (x0 : set), ((tm_dab6e51db9653e58 x0) -> (forall (x1 : set), (((tm_73c9efe869770ab4 x1) (tm_7df1da8a4be89c3e x0)) -> (forall (x2 : prop), ((((tm_73c9efe869770ab4 (tm_bf1decfd8f4025a2 x1)) x0) -> ((tm_dab6e51db9653e58 (tm_bf1decfd8f4025a2 x1)) -> ((tm_87d7604c7ea9a2ae x1) -> (((tm_3bbf071b189275f9 (tm_bf1decfd8f4025a2 x1)) x1) -> x2)))) -> x2)))))).
Definition tm_1334e1f799a3bc4d : (set -> set) := (fun (x0 : set) => ((tm_0a445311c45f0eb3 (tm_158bae29452f8cbf tm_e2a83319facad3a3)) ((tm_b1b8f6f9d4d6136b x0) (fun (x1 : set) => ((fun (x2 : set) => ((tm_153bff87325a9c75 x2) (tm_158bae29452f8cbf (tm_9db634daee7fc363 tm_e2a83319facad3a3)))) (tm_9db634daee7fc363 x1)))))).
Axiom kn_bad8d3abde1059b5 : (forall (x0 : set), (((tm_73c9efe869770ab4 x0) tm_39cdf86d83c71365) -> (tm_87d7604c7ea9a2ae (tm_1334e1f799a3bc4d x0)))).
Axiom kn_f8e000c80f123a78 : (forall (x0 : set), (((tm_73c9efe869770ab4 x0) tm_39cdf86d83c71365) -> ((tm_73c9efe869770ab4 (tm_1334e1f799a3bc4d x0)) (tm_7df1da8a4be89c3e tm_39cdf86d83c71365)))).
(* Parameter tm_6d39c64862ac40c9 "6d39c64862ac40c95c6f5e4ed5f02bb019279bfb0cda8c9bbe0e1b813b1e876c" "6d39c64862ac40c95c6f5e4ed5f02bb019279bfb0cda8c9bbe0e1b813b1e876c" *)
Parameter tm_6d39c64862ac40c9 : (set -> set).
Axiom kn_5fc6b424fa177911 : (forall (x0 : set), ((tm_87d7604c7ea9a2ae x0) -> (tm_87d7604c7ea9a2ae (tm_6d39c64862ac40c9 x0)))).
Axiom kn_c1b37e4f20f8dbe9 : (forall (x0 : set), (((tm_73c9efe869770ab4 x0) (tm_7df1da8a4be89c3e tm_39cdf86d83c71365)) -> ((tm_73c9efe869770ab4 (tm_6d39c64862ac40c9 x0)) (tm_7df1da8a4be89c3e tm_39cdf86d83c71365)))).
(* Parameter tm_29b9b279a7a5b776 "29b9b279a7a5b776b777d842e678a4acaf3b85b17a0223605e4cc68025e9b2a7" "29b9b279a7a5b776b777d842e678a4acaf3b85b17a0223605e4cc68025e9b2a7" *)
Parameter tm_29b9b279a7a5b776 : (set -> (set -> set)).
Axiom kn_6aafd837e0a0618c : (forall (x0 : set), (forall (x1 : set), ((tm_87d7604c7ea9a2ae x0) -> ((tm_87d7604c7ea9a2ae x1) -> (tm_87d7604c7ea9a2ae ((tm_29b9b279a7a5b776 x0) x1)))))).
Axiom kn_75b04e11158df96f : (forall (x0 : set), ((tm_87d7604c7ea9a2ae x0) -> (((tm_5a6af35fb6d6bea4 set) ((tm_29b9b279a7a5b776 x0) tm_e2a83319facad3a3)) x0))).
Axiom kn_97c4bd2d5316d0c2 : (forall (x0 : set), ((tm_87d7604c7ea9a2ae x0) -> (((tm_5a6af35fb6d6bea4 set) ((tm_29b9b279a7a5b776 (tm_6d39c64862ac40c9 x0)) x0)) tm_e2a83319facad3a3))).
Axiom kn_b6e57b081c34853a : (forall (x0 : set), (((tm_73c9efe869770ab4 x0) (tm_7df1da8a4be89c3e tm_39cdf86d83c71365)) -> (forall (x1 : set), (((tm_73c9efe869770ab4 x1) (tm_7df1da8a4be89c3e tm_39cdf86d83c71365)) -> ((tm_73c9efe869770ab4 ((tm_29b9b279a7a5b776 x0) x1)) (tm_7df1da8a4be89c3e tm_39cdf86d83c71365)))))).
Axiom kn_1ac1c52f6a378e7b : (forall (x0 : set), (forall (x1 : set), (forall (x2 : set), (forall (x3 : set), ((tm_87d7604c7ea9a2ae x0) -> ((tm_87d7604c7ea9a2ae x1) -> ((tm_87d7604c7ea9a2ae x2) -> ((tm_87d7604c7ea9a2ae x3) -> (((tm_5a6af35fb6d6bea4 set) ((tm_29b9b279a7a5b776 ((tm_29b9b279a7a5b776 x0) x1)) ((tm_29b9b279a7a5b776 x2) x3))) ((tm_29b9b279a7a5b776 ((tm_29b9b279a7a5b776 x0) x2)) ((tm_29b9b279a7a5b776 x1) x3))))))))))).
Axiom kn_2a7bc1eb055a0b8c : (forall (x0 : set), (forall (x1 : set), (forall (x2 : set), ((tm_87d7604c7ea9a2ae x0) -> ((tm_87d7604c7ea9a2ae x1) -> ((tm_87d7604c7ea9a2ae x2) -> (((tm_0d574978cbb344ec x0) ((tm_29b9b279a7a5b776 x2) x1)) -> ((tm_0d574978cbb344ec ((tm_29b9b279a7a5b776 x0) (tm_6d39c64862ac40c9 x1))) x2)))))))).
Axiom kn_d4057184df5419ca : (forall (x0 : set), ((tm_87d7604c7ea9a2ae x0) -> (forall (x1 : set), (((tm_73c9efe869770ab4 x1) tm_39cdf86d83c71365) -> ((tm_0d574978cbb344ec x0) ((tm_29b9b279a7a5b776 x0) (tm_1334e1f799a3bc4d x1))))))).
Axiom kn_9353dc5eb19fa58e : (forall (x0 : set), ((tm_25c483dc8509e17d x0) -> (((tm_5a6af35fb6d6bea4 set) ((tm_29b9b279a7a5b776 (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x0))) (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x0)))) (tm_1334e1f799a3bc4d x0)))).
Theorem target_thm : ((forall (x0 : set), (((tm_73c9efe869770ab4 x0) (tm_7df1da8a4be89c3e tm_39cdf86d83c71365)) -> (forall (x1 : set), (((tm_73c9efe869770ab4 x1) tm_39cdf86d83c71365) -> ((tm_912ad2cdc2d23bb8 set) (fun (x2 : set) => ((tm_87fba1d2da67f06e ((tm_73c9efe869770ab4 x2) (tm_7df1da8a4be89c3e tm_39cdf86d83c71365))) ((tm_87fba1d2da67f06e ((tm_0d574978cbb344ec x2) x0)) ((tm_0d574978cbb344ec x0) ((tm_29b9b279a7a5b776 x2) (tm_1334e1f799a3bc4d x1))))))))))) -> (forall (x0 : prop), x0)).
exact (fun (x0 : set) => (fun (H0 : ((tm_73c9efe869770ab4 x0) (tm_7df1da8a4be89c3e tm_39cdf86d83c71365))) => ((((((kn_ad91f617a46a583c tm_39cdf86d83c71365) kn_97063ca423850207) x0) H0) (forall (x1 : set), (((tm_73c9efe869770ab4 x1) tm_39cdf86d83c71365) -> ((tm_912ad2cdc2d23bb8 set) (fun (x2 : set) => ((tm_87fba1d2da67f06e ((tm_73c9efe869770ab4 x2) (tm_7df1da8a4be89c3e tm_39cdf86d83c71365))) ((tm_87fba1d2da67f06e ((tm_0d574978cbb344ec x2) x0)) ((tm_0d574978cbb344ec x0) ((tm_29b9b279a7a5b776 x2) (tm_1334e1f799a3bc4d x1)))))))))) (fun (H1 : ((tm_73c9efe869770ab4 (tm_bf1decfd8f4025a2 x0)) tm_39cdf86d83c71365)) => (fun (H2 : (tm_dab6e51db9653e58 (tm_bf1decfd8f4025a2 x0))) => (fun (H3 : (tm_87d7604c7ea9a2ae x0)) => (fun (H4 : ((tm_3bbf071b189275f9 (tm_bf1decfd8f4025a2 x0)) x0)) => (fun (x1 : set) => (fun (H5 : ((tm_73c9efe869770ab4 x1) tm_39cdf86d83c71365)) => ((fun (H6 : (tm_87d7604c7ea9a2ae (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1)))) => (fun (x2 : prop) => (fun (H7 : (forall (x3 : set), (((tm_87fba1d2da67f06e ((tm_73c9efe869770ab4 x3) (tm_7df1da8a4be89c3e tm_39cdf86d83c71365))) ((tm_87fba1d2da67f06e ((tm_0d574978cbb344ec x3) x0)) ((tm_0d574978cbb344ec x0) ((tm_29b9b279a7a5b776 x3) (tm_1334e1f799a3bc4d x1))))) -> x2))) => ((H7 ((tm_29b9b279a7a5b776 x0) (tm_6d39c64862ac40c9 (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1))))) ((((kn_7f6246d08629eeb1 ((tm_73c9efe869770ab4 ((tm_29b9b279a7a5b776 x0) (tm_6d39c64862ac40c9 (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1))))) (tm_7df1da8a4be89c3e tm_39cdf86d83c71365))) ((tm_87fba1d2da67f06e ((tm_0d574978cbb344ec ((tm_29b9b279a7a5b776 x0) (tm_6d39c64862ac40c9 (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1))))) x0)) ((tm_0d574978cbb344ec x0) ((tm_29b9b279a7a5b776 ((tm_29b9b279a7a5b776 x0) (tm_6d39c64862ac40c9 (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1))))) (tm_1334e1f799a3bc4d x1))))) ((((kn_b6e57b081c34853a x0) H0) (tm_6d39c64862ac40c9 (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1)))) ((kn_c1b37e4f20f8dbe9 (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1))) ((kn_f8e000c80f123a78 (tm_9db634daee7fc363 x1)) ((kn_f88efc1bceb13c96 x1) H5))))) ((((kn_7f6246d08629eeb1 ((tm_0d574978cbb344ec ((tm_29b9b279a7a5b776 x0) (tm_6d39c64862ac40c9 (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1))))) x0)) ((tm_0d574978cbb344ec x0) ((tm_29b9b279a7a5b776 ((tm_29b9b279a7a5b776 x0) (tm_6d39c64862ac40c9 (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1))))) (tm_1334e1f799a3bc4d x1)))) (((((((kn_2a7bc1eb055a0b8c x0) (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1))) x0) H3) H6) H3) ((((kn_d4057184df5419ca x0) H3) (tm_9db634daee7fc363 x1)) ((kn_f88efc1bceb13c96 x1) H5)))) ((((kn_9353dc5eb19fa58e x1) ((kn_7d6896163f052ef5 x1) H5)) (fun (x3 : set) => (fun (x4 : set) => ((tm_0d574978cbb344ec x0) ((tm_29b9b279a7a5b776 ((tm_29b9b279a7a5b776 x0) (tm_6d39c64862ac40c9 (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1))))) x3))))) ((((((((((kn_1ac1c52f6a378e7b x0) (tm_6d39c64862ac40c9 (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1)))) (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1))) (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1))) H3) ((kn_5fc6b424fa177911 (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1))) H6)) H6) H6) (fun (x3 : set) => (fun (x4 : set) => ((tm_0d574978cbb344ec x0) x4)))) ((((kn_97c4bd2d5316d0c2 (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1))) H6) (fun (x3 : set) => (fun (x4 : set) => ((tm_0d574978cbb344ec x0) ((tm_29b9b279a7a5b776 ((tm_29b9b279a7a5b776 x0) (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1)))) x4))))) ((((kn_75b04e11158df96f ((tm_29b9b279a7a5b776 x0) (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1)))) ((((kn_6aafd837e0a0618c x0) (tm_1334e1f799a3bc4d (tm_9db634daee7fc363 x1))) H3) H6)) (fun (x3 : set) => (fun (x4 : set) => ((tm_0d574978cbb344ec x0) x4)))) ((((kn_d4057184df5419ca x0) H3) (tm_9db634daee7fc363 x1)) ((kn_f88efc1bceb13c96 x1) H5)))))))))))) ((kn_bad8d3abde1059b5 (tm_9db634daee7fc363 x1)) ((kn_f88efc1bceb13c96 x1) H5)))))))))))).
Qed.
