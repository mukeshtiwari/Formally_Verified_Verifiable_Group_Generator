From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo41:
  prime  211948161232579->
  prime  479638690173740827.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      479638690173740827
      2263
      ((211948161232579,1)::nil)
      0
      192
      4
      16)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
