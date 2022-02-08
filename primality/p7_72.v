From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo72:
  prime  87882427100100997730250576487417->
  prime  53316071460953772812439412794347360011.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      53316071460953772812439412794347360011
      606675
      ((87882427100100997730250576487417,1)::nil)
      0
      500
      5
      25)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
