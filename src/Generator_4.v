Require Import Coq.NArith.NArith
  Verigen.Domainpar
  Znumtheory Lia
  Zdiv Zpow_facts.
From Coq Require Import String Ascii.
Open Scope N_scope.






(* 2048 bit prime *)

Module Pins <: Prime. 

Definition p : N := 0xf3caef1fcda11aacb1447b96aa97554653b028b7e733047c4e19cc578d39de5e7c9df4e59fb87b1d39ee2306f93bc57f29c02fb3a8a3cd1d58fd1790390ef56462e3a870bdfeeb5638527ba744420ee7b729087507c2d06fb298211c599e80506f60a3eae7f1f046bcac7641919becb9d9565d3f30e733db9beb8535f83f886b9d4a49762fe43f04f941a4c8961c4e850e3570e319973679aadd294ec3a141a55b11396c19048ed11eaec1e9150000b7b3524f21586607f778f3101b99ef8034aafd79cd92c4f1bf27cd849b574378eaffe0622fad1c6ae920371fd4cf1a7c0ab6c9fe7726a7b0443f9e08b1ebe81355ad4c86b998124da92b4f60476428ff11.
Definition q : N := 0x85b5a2b6f85d50c703fc27a86a17b4cbcbc540efb6b9c9223ddd9c0b.
Definition domain_parameter_seed : N := 0xa4da80bed4f907b8295d6e7bb763032b3fdd5e61b61ce6d0b67e9dcf.
Definition index : N := 0x38.
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

Definition G : N := 0x84eb7f9cb58e6d2e733f1826e9bf740c221df0b8d61974d41da836125de34f0c08eaccc883912fad83945d15bcb511c9bd4090b3014d143dea02c63e7c4e9e9fefcf97e5d4bc4bbef8dcc697a4091a88f119f12b66d90c0a8ea75c5ec3e496c43a63d002379763c15d56c30bc1c2d12909b8615d237c47967d3229a0f4dcecc7872a094e598320151c39c3d0f18b7a587f127e7f9308e99b842c82bbaf05e1c111f9381e522f0adb1dd082cd1868e0429e3bea495b301177f687e0e603e3ae01f6f8bbb451d39744d581858a33fed1de569cbd7bdc139140d300ed7783e8948a91766ce833b83624859d0ccbee23a7c4c2da2692494fca6b1e2185bee808356a.


Theorem G_is_gen : genr.Valid G = genr.compute_generator.
Proof.
  Time vm_compute.
  reflexivity.
Qed.



Time Eval vm_compute in genr.compute_generator.
(*
Finished transaction in 413.996 secs (412.942u,1.074s) (successful)
	 = genr.Valid
         16779584886618334955777146143805151742756109597848073032897659526710040302176218585670602669216587991633935024592787306349889100902129684576531517671064338120830768458737964024941626899266181419534731022507702381832220695652481201002313417792528591777912496057497664476810455186127730777145720725703338677122474655371704794416925100215075257492292453624627321349273605377338405654300066568869264460444035900045343943151207471750966197679881151399230919361519925420099999305148035925485570132525240424489924786140236333173248767301480930310664404386723788396232966052596334360090754073589039580595341483241910869439850
     : genr.Tag
Finished transaction in 0.349 secs (0.344u,0.005s) (successful)
*)

Time Eval vm_compute in (genr.verify_generator 16779584886618334955777146143805151742756109597848073032897659526710040302176218585670602669216587991633935024592787306349889100902129684576531517671064338120830768458737964024941626899266181419534731022507702381832220695652481201002313417792528591777912496057497664476810455186127730777145720725703338677122474655371704794416925100215075257492292453624627321349273605377338405654300066568869264460444035900045343943151207471750966197679881151399230919361519925420099999305148035925485570132525240424489924786140236333173248767301480930310664404386723788396232966052596334360090754073589039580595341483241910869439850).

(*
= true
     : bool
Finished transaction in 489.413 secs (486.363u,2.701s) (successful)

*)