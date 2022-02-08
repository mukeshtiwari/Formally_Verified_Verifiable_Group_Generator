From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo77:
  prime  86950522037090249->
  prime  6956041757792540729.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      6956041757792540729
      80
      ((86950522037090249,1)::nil)
      100
      0
      20
      100)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
