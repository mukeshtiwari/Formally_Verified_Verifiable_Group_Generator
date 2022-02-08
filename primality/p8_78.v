From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo78:
  prime  14364231743055391865087823571184881->
  prime  1642101276132584953776278568705188245389037.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1642101276132584953776278568705188245389037
      114318768
      ((14364231743055391865087823571184881,1)::nil)
      0
      4052240
      296
      5476)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
