From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo105:
  prime  8241884923488954977149597->
  prime  3428478896656160075752092089539417957.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      3428478896656160075752092089539417957
      415982378847
      ((8241884923488954977149597,1)::nil)
      0
      192
      4
      16)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
