(* Parameter tm_5bf697cb0d1cdefb "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87" "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87" *)
Parameter tm_5bf697cb0d1cdefb : prop.
(* Parameter tm_058f630dd89cad5a "058f630dd89cad5a22daa56e097e3bdf85ce16ebd3dbf7994e404e2a98800f7f" "058f630dd89cad5a22daa56e097e3bdf85ce16ebd3dbf7994e404e2a98800f7f" *)
Parameter tm_058f630dd89cad5a : (prop -> prop).
(* Parameter tm_87fba1d2da67f06e "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738" "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738" *)
Parameter tm_87fba1d2da67f06e : (prop -> (prop -> prop)).
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
(* Parameter tm_e7493d5f5a73b6cb "e7493d5f5a73b6cb40310f6fcb87d02b2965921a25ab96d312adf7eb8157e4b3" "e7493d5f5a73b6cb40310f6fcb87d02b2965921a25ab96d312adf7eb8157e4b3" *)
Parameter tm_e7493d5f5a73b6cb : (set -> prop).
(* Parameter tm_384d9f66d8806a02 "384d9f66d8806a02ebe28da535de6ad3715d7edbe784c055e3c70df3ad888708" "384d9f66d8806a02ebe28da535de6ad3715d7edbe784c055e3c70df3ad888708" *)
Parameter tm_384d9f66d8806a02 : (set -> prop).
(* Parameter tm_bb3da8f6f3861e95 "bb3da8f6f3861e950e002517b27fe9407103f6d9bfacf8e3d7600f2396cc1059" "bb3da8f6f3861e950e002517b27fe9407103f6d9bfacf8e3d7600f2396cc1059" *)
Parameter tm_bb3da8f6f3861e95 : (set -> prop).
(* Parameter tm_7c09f0cab3d30d5f "7c09f0cab3d30d5ff3c2ec8c2cff61e158c82ce67d886c8b6a8763990b8a0515" "7c09f0cab3d30d5ff3c2ec8c2cff61e158c82ce67d886c8b6a8763990b8a0515" *)
Parameter tm_7c09f0cab3d30d5f : (set -> prop).
(* Parameter tm_c7df083c7cf25a97 "c7df083c7cf25a97335c4c9d8dc333551ed272dcab0c9c75bdb57679962006f5" "c7df083c7cf25a97335c4c9d8dc333551ed272dcab0c9c75bdb57679962006f5" *)
Parameter tm_c7df083c7cf25a97 : (set -> prop).
(* Parameter tm_f73cdba5a4e557a8 "f73cdba5a4e557a8f57fbba8517c0f7593a0b36795e8f51b63ba62b37035c3d0" "f73cdba5a4e557a8f57fbba8517c0f7593a0b36795e8f51b63ba62b37035c3d0" *)
Parameter tm_f73cdba5a4e557a8 : (set -> prop).
(* Parameter tm_3578b0d6a7b31871 "3578b0d6a7b318714bc5ea889c6a38cf27f08eaccfab7edbde3cb7a350cf2d9b" "3578b0d6a7b318714bc5ea889c6a38cf27f08eaccfab7edbde3cb7a350cf2d9b" *)
Parameter tm_3578b0d6a7b31871 : (prop -> (prop -> prop)).
(* Parameter tm_25c483dc8509e17d "25c483dc8509e17d4b6cf67c5b94c2b3f3902a45c3c34582da3e29ab1dc633ab" "25c483dc8509e17d4b6cf67c5b94c2b3f3902a45c3c34582da3e29ab1dc633ab" *)
Parameter tm_25c483dc8509e17d : (set -> prop).
(* Parameter tm_dab6e51db9653e58 "dab6e51db9653e58783a3fde73d4f2dc2637891208c92c998709e8795ba4326f" "dab6e51db9653e58783a3fde73d4f2dc2637891208c92c998709e8795ba4326f" *)
Parameter tm_dab6e51db9653e58 : (set -> prop).
(* Parameter tm_d744bcd791713cf8 "d744bcd791713cf88021ce34168c3e2d109a8a6c45637d74541d94007e3139ca" "d744bcd791713cf88021ce34168c3e2d109a8a6c45637d74541d94007e3139ca" *)
Parameter tm_d744bcd791713cf8 : (set -> (set -> set)).
(* Parameter tm_0d574978cbb344ec "0d574978cbb344ec3744139d5c1d0d90336d38f956e09a904d230c4fa06b30d1" "0d574978cbb344ec3744139d5c1d0d90336d38f956e09a904d230c4fa06b30d1" *)
Parameter tm_0d574978cbb344ec : (set -> (set -> prop)).
Axiom kn_8c71cf7ec1276527 : (tm_5bf697cb0d1cdefb -> (forall (x0 : prop), x0)).
Axiom kn_b17372bc47d20b47 : (forall (x0 : set), (((tm_73c9efe869770ab4 x0) tm_e2a83319facad3a3) -> tm_5bf697cb0d1cdefb)).
Theorem target_thm : (forall (x0 : set), (((tm_73c9efe869770ab4 x0) tm_e2a83319facad3a3) -> (forall (x1 : set), (((tm_73c9efe869770ab4 x1) x0) -> (forall (x2 : set), (((tm_73c9efe869770ab4 x2) x1) -> ((tm_912ad2cdc2d23bb8 set) (fun (x3 : set) => (forall (x4 : set), (((tm_dab6e51db9653e58 x3) -> ((tm_87fba1d2da67f06e (tm_c7df083c7cf25a97 x3)) (tm_058f630dd89cad5a (tm_f73cdba5a4e557a8 x4)))) -> ((((tm_dab6e51db9653e58 x3) -> (tm_c7df083c7cf25a97 x3)) -> ((tm_384d9f66d8806a02 x3) -> ((((tm_058f630dd89cad5a (tm_384d9f66d8806a02 (tm_2a38dbb37506341b ((tm_d744bcd791713cf8 (tm_2a38dbb37506341b (tm_2a38dbb37506341b tm_e2a83319facad3a3))) tm_e2a83319facad3a3)))) -> (((tm_5a6af35fb6d6bea4 set) x3) x4)) -> (tm_bb3da8f6f3861e95 x3)) -> ((tm_87fba1d2da67f06e (tm_7c09f0cab3d30d5f x2)) (tm_058f630dd89cad5a ((tm_3578b0d6a7b31871 ((tm_0d574978cbb344ec x2) ((tm_d744bcd791713cf8 (tm_2a38dbb37506341b (tm_2a38dbb37506341b (tm_2a38dbb37506341b (tm_2a38dbb37506341b tm_e2a83319facad3a3))))) tm_e2a83319facad3a3))) (tm_e7493d5f5a73b6cb x4))))))) -> (tm_25c483dc8509e17d x3)))))))))))).
exact (fun (x0 : set) => (fun (H0 : ((tm_73c9efe869770ab4 x0) tm_e2a83319facad3a3)) => ((((kn_b17372bc47d20b47 x0) H0) kn_8c71cf7ec1276527) (forall (x1 : set), (((tm_73c9efe869770ab4 x1) x0) -> (forall (x2 : set), (((tm_73c9efe869770ab4 x2) x1) -> ((tm_912ad2cdc2d23bb8 set) (fun (x3 : set) => (forall (x4 : set), (((tm_dab6e51db9653e58 x3) -> ((tm_87fba1d2da67f06e (tm_c7df083c7cf25a97 x3)) (tm_058f630dd89cad5a (tm_f73cdba5a4e557a8 x4)))) -> ((((tm_dab6e51db9653e58 x3) -> (tm_c7df083c7cf25a97 x3)) -> ((tm_384d9f66d8806a02 x3) -> ((((tm_058f630dd89cad5a (tm_384d9f66d8806a02 (tm_2a38dbb37506341b ((tm_d744bcd791713cf8 (tm_2a38dbb37506341b (tm_2a38dbb37506341b tm_e2a83319facad3a3))) tm_e2a83319facad3a3)))) -> (((tm_5a6af35fb6d6bea4 set) x3) x4)) -> (tm_bb3da8f6f3861e95 x3)) -> ((tm_87fba1d2da67f06e (tm_7c09f0cab3d30d5f x2)) (tm_058f630dd89cad5a ((tm_3578b0d6a7b31871 ((tm_0d574978cbb344ec x2) ((tm_d744bcd791713cf8 (tm_2a38dbb37506341b (tm_2a38dbb37506341b (tm_2a38dbb37506341b (tm_2a38dbb37506341b tm_e2a83319facad3a3))))) tm_e2a83319facad3a3))) (tm_e7493d5f5a73b6cb x4))))))) -> (tm_25c483dc8509e17d x3))))))))))))).
Qed.
