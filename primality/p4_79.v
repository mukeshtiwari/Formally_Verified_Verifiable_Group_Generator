From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo79:
  prime  2816249641->
  prime  35662180885921.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      35662180885921
      12663
      ((2816249641,1)::nil)
      0
      221184
      48
      576)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
