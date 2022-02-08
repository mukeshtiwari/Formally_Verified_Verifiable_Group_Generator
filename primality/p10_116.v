From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo116:
  prime  37680100350880616627817671311->
  prime  4955950558850274991939631318283193.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      4955950558850274991939631318283193
      131527
      ((37680100350880616627817671311,1)::nil)
      0
      1015808
      32
      1024)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
