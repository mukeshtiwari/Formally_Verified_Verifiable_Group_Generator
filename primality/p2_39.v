From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo39:
  prime  25812668917919247631855455535243715547043->
  prime  162249041006554268007705274797834123589594737277.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      162249041006554268007705274797834123589594737277
      6285636
      ((25812668917919247631855455535243715547043,1)::nil)
      0
      1272112
      129
      1849)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
