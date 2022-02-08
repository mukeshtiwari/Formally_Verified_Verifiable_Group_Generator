From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo77:
  prime  406847205727->
  prime  15867033888061.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      15867033888061
      39
      ((406847205727,1)::nil)
      0
      19008
      12
      144)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
