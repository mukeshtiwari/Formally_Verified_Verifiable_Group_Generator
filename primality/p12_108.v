From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo108:
  prime  5734669->
  prime  33594023621.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      33594023621
      5858
      ((5734669,1)::nil)
      12597758859
      0
      16797011812
      25195517718)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
