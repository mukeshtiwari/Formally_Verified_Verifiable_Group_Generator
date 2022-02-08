From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo77:
  prime  1642101276132584953776278568705188245389037->
  prime  979920652329567805996085186101517086130053709503.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      979920652329567805996085186101517086130053709503
      596748
      ((1642101276132584953776278568705188245389037,1)::nil)
      0
      5832
      9
      81)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
