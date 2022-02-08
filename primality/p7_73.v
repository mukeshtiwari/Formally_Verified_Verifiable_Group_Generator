From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo73:
  prime  11881666721436151495252921->
  prime  87882427100100997730250576487417.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      87882427100100997730250576487417
      7396473
      ((11881666721436151495252921,1)::nil)
      0
      4823609
      98
      2401)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
