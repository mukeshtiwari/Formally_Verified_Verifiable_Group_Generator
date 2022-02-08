From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo76:
  prime  6956041757792540729->
  prime  422595744363205086117845549.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      422595744363205086117845549
      60752330
      ((6956041757792540729,1)::nil)
      103968
      0
      1368
      51984)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
