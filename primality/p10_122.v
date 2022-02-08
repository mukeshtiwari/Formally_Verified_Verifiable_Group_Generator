From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo122:
  prime  8574079->
  prime  2789425176781.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2789425176781
      325332
      ((8574079,1)::nil)
      0
      1272112
      129
      1849)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
