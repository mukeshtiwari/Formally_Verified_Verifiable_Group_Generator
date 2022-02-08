From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo104:
  prime  3428478896656160075752092089539417957->
  prime  9636717055537684898522652361864837844677654301.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      9636717055537684898522652361864837844677654301
      2810785000
      ((3428478896656160075752092089539417957,1)::nil)
      9636717055537684898522652361864837844677654265
      0
      12
      36)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
