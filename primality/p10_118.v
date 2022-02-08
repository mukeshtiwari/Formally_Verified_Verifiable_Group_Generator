From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo118:
  prime  4704087594993277409->
  prime  538448682474459892391929.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      538448682474459892391929
      114464
      ((4704087594993277409,1)::nil)
      100
      0
      20
      100)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
