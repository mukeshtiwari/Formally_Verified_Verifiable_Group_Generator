Require Import Coq.NArith.NArith
  Verigen.Domainpar
  Znumtheory Lia
  Zdiv Zpow_facts.
From Coq Require Import String Ascii.
Open Scope N_scope.




(* 1024 bit prime*)

Module Pins <: Prime. 

Definition p : N := 0xfbdf34147bf5d8a45671c906923c1dbe86e9123fae5750d6c1986e00a9946f7f833372a436f98f75dc798bb454825eb625d49011d1e4401baacb653bb9dac6cc8ac91e61ba4310458ff6d6ddabcba29db025eedba6e2f837344dee4814e2a7e2e92ceb1e6e665ee08ce187ffd420fee7a99e046a4af719fa8c689630e88f8729.
Definition q : N := 0x93db61194cb0b9236eea63617d149cd6dd8e2bf1.
Definition domain_parameter_seed : N := 0x75709e9ca555a80cb7ab154e9d29d2775fe215d8.
Definition index: N := 0xae.
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

Definition G : N := 0x7db10e27fffe43fc9582367a449f7be217130cdf89a5eff65fbebefc9478ba39ad03d1b0d0254c0f1b8246d914c0d1df25f55a5dabbb51caa1942403fdc22c832e4d7048ce0ad64cb76252fdcfaecd78722c2e10417495ee9d4e0d8376f891a3042b103de915355c0e60e168cf48c0fa232a13bf9b58a0f9b3ad7db7ad39c536.

Theorem G_is_gen : genr.Valid G = genr.compute_generator.
Proof.
  Time vm_compute.
  reflexivity.
Qed.



Time Eval vm_compute in genr.compute_generator.
(*
Finished transaction in 51.232 secs (50.885u,0.334s) (successful)
	 = genr.Valid
         88263658766223357461869144483248908802431230135321993360469791817434515043095308104988988885613316192808653647560362493809139862324204760674673830428720363991237057673925805011298607088991781235425078687556099730304327702471847840027357950827996311819356543334664389981253439309485633438223355769536120472886
     : genr.Tag
Finished transaction in 0.105 secs (0.104u,0.001s) (successful)

*)

Time Eval vm_compute in (genr.verify_generator 88263658766223357461869144483248908802431230135321993360469791817434515043095308104988988885613316192808653647560362493809139862324204760674673830428720363991237057673925805011298607088991781235425078687556099730304327702471847840027357950827996311819356543334664389981253439309485633438223355769536120472886).

(*
= true
     : bool
Finished transaction in 63.977 secs (63.598u,0.335s) (successful)

*)