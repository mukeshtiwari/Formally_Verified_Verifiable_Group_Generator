From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo79:
  prime  208870589->
  prime  1405283683061.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1405283683061
      6728
      ((208870589,1)::nil)
      1405283683025
      0
      12
      36)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
