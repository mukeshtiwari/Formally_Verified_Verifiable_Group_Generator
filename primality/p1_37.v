From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo37:
  prime  188140985911267861423946194626901->
  prime  34582570902321968142700804652362627159.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      34582570902321968142700804652362627159
      183812
      ((188140985911267861423946194626901,1)::nil)
      34582570901474135900317301068469097239
      26331379788896662181242840604542371570
      0
      97477976010097357444)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
