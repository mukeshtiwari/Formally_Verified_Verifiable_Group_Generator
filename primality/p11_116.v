From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo116:
  prime  125925669151623297995917822831->
  prime  10492504530720708046338171434923129.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      10492504530720708046338171434923129
      83323
      ((125925669151623297995917822831,1)::nil)
      0
      3584
      8
      64)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
