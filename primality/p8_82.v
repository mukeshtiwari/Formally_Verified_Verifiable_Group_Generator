From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo82:
  prime  1659108721->
  prime  4732254109989697.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      4732254109989697
      2852287
      ((1659108721,1)::nil)
      0
      1238519631397054
      3549190582492305
      4436488228116381)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
