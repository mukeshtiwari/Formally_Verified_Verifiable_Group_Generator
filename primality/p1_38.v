From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo38:
  prime  18092219050992197265201299557->
  prime  188140985911267861423946194626901.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      188140985911267861423946194626901
      10399
      ((18092219050992197265201299557,1)::nil)
      0
      19008
      12
      144)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
