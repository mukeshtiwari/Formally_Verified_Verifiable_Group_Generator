Require Import Coq.NArith.NArith
  Verigen.Domainpar
  Verigen.Functions
  Znumtheory Lia
  Zdiv Zpow_facts.
From Coq Require Import String Ascii.
Open Scope N_scope.



(* 1024 bit prime *)

Module Pins <: Prime. 
Definition p : N :=
0xff600483db6abfc5b45eab78594b3533d550d9f1bf2a992a7a8daa6dc34f8045ad4e6e0c429d334eeeaaefd7e23d4810be00e4cc1492cba325ba81ff2d5a5b305a8d17eb3bf4a06a349d392e00d329744a5179380344e82a18c47933438f891e22aeef812d69c8f75e326cb70ea000c3f776dfdbd604638c2ef717fc26d02e17.
Definition q : N := 0xe21e04f911d1ed7991008ecaab3bf775984309c3.
Definition k : N := Eval vm_compute in N.div (p - 1) q.
Definition domain_parameter_seed : N :=  0x180180ee2f0ae4a7b3a1ab1b8414228913ef2911.
Definition ggen : N := 0x6767656e.
Definition index : N := 0x79.



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


Definition G := 0xc52a4a0ff3b7e61fdf1867ce84138369a6154f4afa92966e3c827e25cfa6cf508b90e5de419e1337e07a2e9e2a3cd5dea704d175f8ebf6af397d69e110b96afb17c7a03259329e4829b0d03bbc7896b15b4ade53e130858cc34d96269aa89041f409136c7242a38895c9d5bccad4f389af1d7a4bd1398bd072dffa896233397a.

Theorem G_is_gen : genr.Valid G = genr.compute_generator.
Proof.
  Time vm_compute.
  reflexivity.
Qed.



Time Eval vm_compute in genr.compute_generator.
(*
= genr.Valid
       138454106708200479055735335430888877165820506315681808529812588774891294266745965935843260905810124292112533861018873505541666292973867778507479111324012276358327291576815142910454131034197568218833096994765060449736987726137450505727390912803873697812682423871774182713509275008471752297521355610521695631738
   : genr.Tag
*)


Time Eval vm_compute in (genr.verify_generator 138454106708200479055735335430888877165820506315681808529812588774891294266745965935843260905810124292112533861018873505541666292973867778507479111324012276358327291576815142910454131034197568218833096994765060449736987726137450505727390912803873697812682423871774182713509275008471752297521355610521695631738).

(*
= true : bool
*)





