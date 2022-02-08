From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo121:
  prime  2789425176781->
  prime  86472197895793.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      86472197895793
      31
      ((2789425176781,1)::nil)
      0
      19008
      12
      144)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
