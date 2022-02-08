From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo40:
  prime  479638690173740827->
  prime  12155647799415374728567975423.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      12155647799415374728567975423
      25343342913
      ((479638690173740827,1)::nil)
      0
      119164
      93
      961)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
