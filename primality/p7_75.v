From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo75:
  prime  39488365236169->
  prime  23377111993633837.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      23377111993633837
      592
      ((39488365236169,1)::nil)
      0
      5832
      9
      81)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
