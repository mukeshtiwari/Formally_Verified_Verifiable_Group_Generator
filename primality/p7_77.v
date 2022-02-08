From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo77:
  prime  49295413->
  prime  201471189889.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      201471189889
      4087
      ((49295413,1)::nil)
      0
      30445403030
      151103393496
      188879369941)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
