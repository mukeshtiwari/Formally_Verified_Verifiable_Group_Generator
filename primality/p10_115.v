From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo115:
  prime  4955950558850274991939631318283193->
  prime  517718419179735126776916194485822381493.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      517718419179735126776916194485822381493
      104464
      ((4955950558850274991939631318283193,1)::nil)
      517718419179735126776916173739990905333
      36370126051009921296
      0
      6030764964)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
