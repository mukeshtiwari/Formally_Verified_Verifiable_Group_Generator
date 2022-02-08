From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo40:
  prime  11190113358133->
  prime  2619426498556680433.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2619426498556680433
      234084
      ((11190113358133,1)::nil)
      0
      192
      4
      16)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
