From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo107:
  prime  33594023621->
  prime  71824034781593.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      71824034781593
      2138
      ((33594023621,1)::nil)
      30513722420705
      0
      34112585734099
      68225171468199)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
