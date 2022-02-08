From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo80:
  prime  2387947357->
  prime  150794520695308537.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      150794520695308537
      63148176
      ((2387947357,1)::nil)
      0
      221184
      48
      576)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
