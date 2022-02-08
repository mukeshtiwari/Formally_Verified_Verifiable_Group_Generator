From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo41:
  prime  6701029->
  prime  11190113358133.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      11190113358133
      1669909
      ((6701029,1)::nil)
      0
      54
      3
      9)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
