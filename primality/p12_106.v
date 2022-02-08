From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo106:
  prime  71824034781593->
  prime  8241884923488954977149597.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      8241884923488954977149597
      114751071122
      ((71824034781593,1)::nil)
      4120942461744477488574839
      0
      18
      81)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
