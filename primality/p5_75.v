From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo75:
  prime  422595744363205086117845549->
  prime  25186706364047031257545928103569.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      25186706364047031257545928103569
      59600
      ((422595744363205086117845549,1)::nil)
      100
      0
      20
      100)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
