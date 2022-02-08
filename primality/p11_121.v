From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo121:
  prime  2156196199->
  prime  174652674517.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      174652674517
      81
      ((2156196199,1)::nil)
      0
      740292464
      2513
      128881)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
