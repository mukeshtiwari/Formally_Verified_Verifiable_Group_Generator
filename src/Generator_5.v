Require Import Coq.NArith.NArith
  Verigen.Domainpar
  Znumtheory Lia
  Zdiv Zpow_facts.
From Coq Require Import String Ascii.
Open Scope N_scope.




(* 2048 bit prime*)

Module Pins <: Prime. 

Definition p : N := 0x891cd3e9886275e16d8d45a93c6422a098cfac04be454d85a7fe78e7f84e12a2d3dd0eac81f87be0c92e34630466873beea71482d720eaa6f41a2bc753e55a107994180602b24690f02dd233dfc68a8026a1cf9477a8b9cd3200599f6b23cffe6eeb4c9d0741224acb7a2703264e3f2d252ccd72bb5a1bb2f25d04f5872284e7cb623e918af7111b59d02911dc60ecd27b6d2d3a4c10da9d50dda173f8abecfa9093921a632440ea4d2c901b9b671e1fb532d22ba98b9feb30144afdf1ab5efb885c5f1a77a008b3e8c1590191981c36d9f6025e63ba13be12641aeacffc0535bb49df85f1bc3f79c9adfaa60e03f465f4b56b323d1eda1e90a5c8f18b312bcf.
Definition q : N := 0xa2c6afb5166a6f421183575a5e9fdc2d9128c871f7bd843ab73d6489.
Definition domain_parameter_seed : N := 0x19cebe75508cb677433ecc0c1435ade8f3ccd2d0d77e671f71b74b87.
Definition index : N := 0x56.
Definition k : N := Eval vm_compute in N.div (p - 1) q.
Definition ggen : N := 0x6767656e.



Theorem prime_p : prime (Z.of_N p).
Proof.
Admitted.

Theorem p_len : 1024 <= N.size p.
Proof.
  simpl. lia.
Qed.

Theorem prime_q : prime (Z.of_N q).
Proof.
Admitted.

Theorem q_len : 160 <= N.size q.
Proof.
  simpl. lia.
Qed.

Theorem k_gteq_2 : 2 <= k.
Proof.
  vm_compute; intro Hf.
  inversion Hf.
Qed.

Theorem safe_prime : p = k * q + 1.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem ggen_hyp : ggen =  0x6767656e.
Proof.
  unfold ggen.
  reflexivity.
Qed.

Theorem index_8bit : 0 <= index < 255.
Proof.
  vm_compute.
  split.
  intros Hf; inversion Hf.
  reflexivity.
Qed.


End Pins.


(* get a concrete instance *)
Module genr := Comp Pins.

Definition G : N := 0x3a99cca85d3cc9e671655c2e377eafd5bede54f21ebaaa43e950599b35337f3c68ef022a01befcae044cdc7ccc9b3f0f34e2a55651d7bb5ae2b86ddd5255d63bf2648b8fb10c53496be93666f5541a9165337e66604927a77a5024a747e18b8331efa04786f1c78d0011a82c70b1b025663cb831bb6e1ce6c40c4a6fd7b37e5a4e60b9b8ba8a0539c8f0e2a04ded2f5e832bd65586416063713e849aa6d54b799d321473e518a4c634b88cc90eeeebb1dc0b4171c4228611aa70ebf1832f1d57392cf74a9286e1e93f121b7214b3392de914f938741760187876a8735f4c3b0f4d8892c0c5332057306816109f0672008e64e49c3973cda393ce6be631419920.

Theorem G_is_gen : genr.Valid G = genr.compute_generator.
Proof.
  Time vm_compute.
  reflexivity.
Qed.



Time Eval vm_compute in genr.compute_generator.
(*

Finished transaction in 417.242 secs (414.838u,2.278s) (successful)
	 = genr.Valid
         7397663020529711748206327096495171056013349351297608836944581506776048299910727642018586975845411776739383886069050283668821048481626107184005913661785643385036737596310220141611324379597898168338084415315514945719018373740779993806917733907530535236684877616590789694426081749803454970748757282080960157265510732047192013417745603316937655021638539157108532588624321791236022232330371996545235390513598460611657625080679893233973467700124099006756332896043933323158170849561410748839052823646886645648103667336693441857536896810350359149834341507095181106437695481549438875894694601062306932502363245043364720122144
     : genr.Tag
Finished transaction in 0.348 secs (0.343u,0.005s) (successful)

*)
Time Eval vm_compute in (genr.verify_generator 7397663020529711748206327096495171056013349351297608836944581506776048299910727642018586975845411776739383886069050283668821048481626107184005913661785643385036737596310220141611324379597898168338084415315514945719018373740779993806917733907530535236684877616590789694426081749803454970748757282080960157265510732047192013417745603316937655021638539157108532588624321791236022232330371996545235390513598460611657625080679893233973467700124099006756332896043933323158170849561410748839052823646886645648103667336693441857536896810350359149834341507095181106437695481549438875894694601062306932502363245043364720122144).

(*
= true
     : bool
Finished transaction in 487.489 secs (485.787u,1.571s) (successful)
*)