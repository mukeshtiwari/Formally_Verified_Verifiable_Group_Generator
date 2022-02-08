From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo41:
  prime  1199081629973173->
  prime  206209712180582360058470143.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      206209712180582360058470143
      171973039221
      ((1199081629973173,1)::nil)
      206209712180582359300886239
      8234810772496
      0
      2869636)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
