Require Import Coq.NArith.NArith
  Verigen.Domainpar
  Znumtheory Lia
  Zdiv Zpow_facts.
From Coq Require Import String Ascii.
Open Scope N_scope.



(* 1024 bit prime *)


Module Pins <: Prime. 

Definition p : N := 0xa377415c4b56a12d8d5cc65055db2255c205a28fe8b85599de4b63c7a4626385592d5a9df3d6ad37df33b1038013c7a97da438e944364be745b0555d6483e6ee81a7c2ab1ec2da984ac56a5fe355aa551d7c3faaf1ecd863d91df37261127233f40ae13db116d43b4378c953914f0b96194d380c61d09e8f31e742c1660116e1.
Definition q : N := 0xeb64999ebe50eff1880487ba19aec8b232222aab.
Definition domain_parameter_seed : N := 0xb45c41ee354ccad6520fde67c1ae9d452352f1e0.
Definition index : N := 0x50.
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

Definition G : N := 0x91ec008e233f224f0311d1c0d054446d7d9a6d23803e9fbfc97eed51745afe66a7601fc06d8e8028e5c1f177d3c930a568bd61c0f7c69c7d2853f3a5f0d981271cacf5d65758be60da01f7a9c000c42d18fd76e06f213c6e8fb8e8f8d4e5e354e796f1e95acbcf558f2959b9d527219fa043a2f3dd97db1fff37275af5d5ab1e.


Theorem G_is_gen : genr.Valid G = genr.compute_generator.
Proof.
  Time vm_compute.
  reflexivity.
Qed.



Time Eval vm_compute in genr.compute_generator.
(* 
= genr.Valid
102469831306215617781528906572847226693904307485739300130034645449135192789390308052087414564151228873441394591233561760912933102036228956601258949517417972024163761928741329990676466410461313046468961302321734855374139857073309659521504765942247678350704168525388693094421920249884964626193856064170107448094
: genr.Tag
Finished transaction in 51.755 secs (51.512u,0.238s) (successful)
*)

Time Eval vm_compute in (genr.verify_generator 102469831306215617781528906572847226693904307485739300130034645449135192789390308052087414564151228873441394591233561760912933102036228956601258949517417972024163761928741329990676466410461313046468961302321734855374139857073309659521504765942247678350704168525388693094421920249884964626193856064170107448094).

(*
= true
     : bool
Finished transaction in 64.817 secs (64.296u,0.488s) (successful)
*)






