From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo76:
  prime  15867033888061->
  prime  104532018694100461.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      104532018694100461
      6588
      ((15867033888061,1)::nil)
      0
      78608
      17
      289)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
