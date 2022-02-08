From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo117:
  prime  5665946868464462250896653->
  prime  125925669151623297995917822831.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      125925669151623297995917822831
      22225
      ((5665946868464462250896653,1)::nil)
      0
      61440
      16
      256)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
