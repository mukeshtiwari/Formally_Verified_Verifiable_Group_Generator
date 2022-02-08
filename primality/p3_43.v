From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo43:
  prime  64035967->
  prime  25422596557.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      25422596557
      397
      ((64035967,1)::nil)
      0
      2058
      7
      49)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
