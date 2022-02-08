From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo42:
  prime  401928217->
  prime  1199081629973173.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1199081629973173
      2983323
      ((401928217,1)::nil)
      0
      6912
      24
      144)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
