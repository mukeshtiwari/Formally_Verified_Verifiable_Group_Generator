From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo40:
  prime  206209712180582360058470143->
  prime  25812668917919247631855455535243715547043.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      25812668917919247631855455535243715547043
      125176785540123
      ((206209712180582360058470143,1)::nil)
      0
      119164
      93
      961)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
