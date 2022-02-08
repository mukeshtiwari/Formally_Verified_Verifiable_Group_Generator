From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo77:
  prime  27627491538472454701->
  prime  345478049905178359155938576881.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      345478049905178359155938576881
      12504864925
      ((27627491538472454701,1)::nil)
      0
      1457750
      35
      1225)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
