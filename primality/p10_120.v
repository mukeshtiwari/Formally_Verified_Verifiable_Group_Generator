From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo120:
  prime  86472197895793->
  prime  73501368737533661.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      73501368737533661
      850
      ((86472197895793,1)::nil)
      27563013276575124
      0
      36750684368766832
      55126026553150248)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
