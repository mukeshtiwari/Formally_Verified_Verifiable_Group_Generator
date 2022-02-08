From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo73:
  prime  315717631076902301080018634305498796093->
  prime  138300739728499206792687881568294899909109199.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      138300739728499206792687881568294899909109199
      438052
      ((315717631076902301080018634305498796093,1)::nil)
      138300739728499205944855639184791316015579279
      9501955807025115933281263315351902213136
      0
      97477976010097357444)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
