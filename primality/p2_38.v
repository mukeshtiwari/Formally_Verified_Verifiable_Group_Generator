From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo38:
  prime  162249041006554268007705274797834123589594737277->
  prime  16142557195877206286911504798127574425995392359804445821.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      16142557195877206286911504798127574425995392359804445821
      99492466
      ((162249041006554268007705274797834123589594737277,1)::nil)
      2178
      0
      99
      1089)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
