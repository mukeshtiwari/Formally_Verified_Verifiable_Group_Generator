From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo76:
  prime  345478049905178359155938576881->
  prime  2628742481728502069742011960725633.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2628742481728502069742011960725633
      7609
      ((345478049905178359155938576881,1)::nil)
      0
      58320
      36
      324)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
