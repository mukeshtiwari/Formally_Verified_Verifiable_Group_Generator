From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo67:
  prime  6776456606293410301236701493892538026402364558401646444859583703463227->
  prime  3167939251789318968545748054782810387151430861763972274969758490494160965929.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      3167939251789318968545748054782810387151430861763972274969758490494160965929
      467492
      ((6776456606293410301236701493892538026402364558401646444859583703463227,1)::nil)
      3167939251789318968545748054782810387151430861763972274969758490494160871849
      9834496
      0
      3136)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
