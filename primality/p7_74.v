From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo74:
  prime  23377111993633837->
  prime  11881666721436151495252921.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      11881666721436151495252921
      508260675
      ((23377111993633837,1)::nil)
      0
      1080
      6
      36)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
