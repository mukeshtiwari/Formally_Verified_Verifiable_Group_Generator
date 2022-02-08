From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo119:
  prime  73501368737533661->
  prime  4704087594993277409.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      4704087594993277409
      64
      ((73501368737533661,1)::nil)
      100
      0
      20
      100)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
