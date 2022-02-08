From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo75:
  prime  104532018694100461->
  prime  378514307375051614573669.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      378514307375051614573669
      3621037
      ((104532018694100461,1)::nil)
      0
      47250
      15
      225)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
