From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo78:
  prime  1405283683061->
  prime  86950522037090249.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      86950522037090249
      61874
      ((1405283683061,1)::nil)
      61187404396470941
      0
      28983507345696767
      9661169115232325)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
