From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo73:
  prime  7184598157482408295256855570549069075991910743619676379487512660735613->
  prime  697143113014990524113658466577087819598521089160368494672136498812315148093.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      697143113014990524113658466577087819598521089160368494672136498812315148093
      97033
      ((7184598157482408295256855570549069075991910743619676379487512660735613,1)::nil)
      0
      54
      3
      9)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
