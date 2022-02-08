From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo42:
  prime  25422596557->
  prime  211948161232579.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      211948161232579
      8337
      ((25422596557,1)::nil)
      0
      1080
      6
      36)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
