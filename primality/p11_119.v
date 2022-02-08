From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo119:
  prime  248880039264721->
  prime  4088601288693391999.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      4088601288693391999
      16428
      ((248880039264721,1)::nil)
      0
      5832
      9
      81)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
