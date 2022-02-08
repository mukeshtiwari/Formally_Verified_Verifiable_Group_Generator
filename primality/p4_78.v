From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo78:
  prime  35662180885921->
  prime  27627491538472454701.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      27627491538472454701
      774700
      ((35662180885921,1)::nil)
      0
      54
      3
      9)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
