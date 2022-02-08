From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo36:
  prime  34582570902321968142700804652362627159->
  prime  2093732590139278917263428482539571041653837.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2093732590139278917263428482539571041653837
      60543
      ((34582570902321968142700804652362627159,1)::nil)
      0
      78608
      17
      289)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
