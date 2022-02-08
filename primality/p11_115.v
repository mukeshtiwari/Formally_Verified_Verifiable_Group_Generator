From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo115:
  prime  10492504530720708046338171434923129->
  prime  2224424442783039323682545799822955619261761489.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2224424442783039323682545799822955619261761489
      212001284943
      ((10492504530720708046338171434923129,1)::nil)
      0
      221184
      48
      576)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
