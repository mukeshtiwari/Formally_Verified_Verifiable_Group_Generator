From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo74:
  prime  378514307375051614573669->
  prime  517887315990776888002183434152551.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      517887315990776888002183434152551
      1368210675
      ((378514307375051614573669,1)::nil)
      0
      500
      5
      25)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
