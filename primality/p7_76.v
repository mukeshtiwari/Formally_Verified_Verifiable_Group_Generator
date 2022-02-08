From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo76:
  prime  201471189889->
  prime  39488365236169.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      39488365236169
      196
      ((201471189889,1)::nil)
      0
      3584
      8
      64)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
