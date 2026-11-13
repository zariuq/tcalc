Definition tm_5bf697cb0d1cdefb : prop := (forall (x0 : prop), x0).
Definition tm_058f630dd89cad5a : (prop -> prop) := (fun (x0 : prop) => (x0 -> tm_5bf697cb0d1cdefb)).
Definition tm_87fba1d2da67f06e : (prop -> (prop -> prop)) := (fun (x0 : prop) => (fun (x1 : prop) => (forall (x2 : prop), ((x0 -> (x1 -> x2)) -> x2)))).
Definition tm_cfe97741543f37f0 : (prop -> (prop -> prop)) := (fun (x0 : prop) => (fun (x1 : prop) => (forall (x2 : prop), ((x0 -> x2) -> ((x1 -> x2) -> x2))))).
Definition tm_9c60bab687728bc4 : (prop -> (prop -> prop)) := (fun (x0 : prop) => (fun (x1 : prop) => ((tm_87fba1d2da67f06e (x0 -> x1)) (x1 -> x0)))).
Section S1. Variable a0 : SType.
Definition tm_5a6af35fb6d6bea4 : (a0 -> (a0 -> prop)) := (fun (x0 : a0) => (fun (x1 : a0) => (forall (x2 : (a0 -> (a0 -> prop))), (((x2 x0) x1) -> ((x2 x1) x0))))).
End S1.
Section S2. Variable a0 : SType.
Definition tm_7966a66a9bb19810 : (a0 -> (a0 -> prop)) := (fun (x0 : a0) => (fun (x1 : a0) => (tm_058f630dd89cad5a (((tm_5a6af35fb6d6bea4 a0) x0) x1)))).
End S2.
Section S3. Variable a0 : SType.
Definition tm_912ad2cdc2d23bb8 : ((a0 -> prop) -> prop) := (fun (x0 : (a0 -> prop)) => (forall (x1 : prop), ((forall (x2 : a0), ((x0 x2) -> x1)) -> x1))).
End S3.
Parameter In : (set -> (set -> prop)).
Definition tm_73c9efe869770ab4 : (set -> (set -> prop)) := In.
Parameter Union : (set -> set).
Definition tm_844774016d959cff : (set -> set) := Union.
Axiom kn_f59dc74902bca3fa : (forall (x0 : set), (forall (x1 : set), ((forall (x2 : set), ((tm_9c60bab687728bc4 ((tm_73c9efe869770ab4 x2) x0)) ((tm_73c9efe869770ab4 x2) x1))) -> (((tm_5a6af35fb6d6bea4 set) x0) x1)))).
Axiom kn_8c71cf7ec1276527 : (tm_5bf697cb0d1cdefb -> (forall (x0 : prop), x0)).
Axiom kn_bfd151f806ea28dc : (forall (x0 : prop), (forall (x1 : prop), ((x0 -> x1) -> ((x1 -> x0) -> ((tm_9c60bab687728bc4 x0) x1))))).
Definition tm_2f8b7f287504f141 : (set -> (set -> prop)) := (fun (x0 : set) => (fun (x1 : set) => (tm_058f630dd89cad5a ((tm_73c9efe869770ab4 x0) x1)))).
(* Parameter tm_7491fed394c0760e "7491fed394c0760ecce5d4e1df80fe76188bef2528794da082e0223de99066ce" "7491fed394c0760ecce5d4e1df80fe76188bef2528794da082e0223de99066ce" *)
Parameter tm_7491fed394c0760e : set.
Axiom kn_28da36bc3608156f : (forall (x0 : set), ((tm_2f8b7f287504f141 x0) tm_7491fed394c0760e)).
Axiom kn_1174f35d06d32f6c : (forall (x0 : prop), ((tm_cfe97741543f37f0 x0) (tm_058f630dd89cad5a x0))).
Theorem target_thm : (forall (x0 : set), ((((tm_7966a66a9bb19810 set) x0) tm_7491fed394c0760e) -> ((tm_912ad2cdc2d23bb8 set) (fun (x1 : set) => ((tm_73c9efe869770ab4 x1) x0))))).
exact (fun (x0 : set) => (fun (H0 : (((tm_7966a66a9bb19810 set) x0) tm_7491fed394c0760e)) => ((fun (H1 : (tm_058f630dd89cad5a ((tm_912ad2cdc2d23bb8 set) (fun (x1 : set) => ((tm_73c9efe869770ab4 x1) x0))))) => ((kn_8c71cf7ec1276527 (H0 (((kn_f59dc74902bca3fa x0) tm_7491fed394c0760e) (fun (x1 : set) => ((((kn_bfd151f806ea28dc ((tm_73c9efe869770ab4 x1) x0)) ((tm_73c9efe869770ab4 x1) tm_7491fed394c0760e)) (fun (H2 : ((tm_73c9efe869770ab4 x1) x0)) => ((kn_8c71cf7ec1276527 (H1 (fun (x2 : prop) => (fun (H3 : (forall (x3 : set), (((tm_73c9efe869770ab4 x3) x0) -> x2))) => ((H3 x1) H2))))) ((tm_73c9efe869770ab4 x1) tm_7491fed394c0760e)))) (fun (H2 : ((tm_73c9efe869770ab4 x1) tm_7491fed394c0760e)) => ((kn_8c71cf7ec1276527 ((kn_28da36bc3608156f x1) H2)) ((tm_73c9efe869770ab4 x1) x0)))))))) ((tm_912ad2cdc2d23bb8 set) (fun (x1 : set) => ((tm_73c9efe869770ab4 x1) x0))))) (((kn_1174f35d06d32f6c ((tm_912ad2cdc2d23bb8 set) (fun (x1 : set) => ((tm_73c9efe869770ab4 x1) x0)))) ((tm_912ad2cdc2d23bb8 set) (fun (x1 : set) => ((tm_73c9efe869770ab4 x1) x0)))) (fun (H1 : ((tm_912ad2cdc2d23bb8 set) (fun (x1 : set) => ((tm_73c9efe869770ab4 x1) x0)))) => H1))))).
Qed.
