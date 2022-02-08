From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo79:
  prime  6568809752638910349004891->
  prime  14364231743055391865087823571184881.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      14364231743055391865087823571184881
      2186732800
      ((6568809752638910349004891,1)::nil)
      0
      99144
      18
      324)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
