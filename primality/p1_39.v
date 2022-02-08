From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo39:
  prime  2619426498556680433->
  prime  18092219050992197265201299557.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      18092219050992197265201299557
      6906939004
      ((2619426498556680433,1)::nil)
      0
      5832
      9
      81)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
