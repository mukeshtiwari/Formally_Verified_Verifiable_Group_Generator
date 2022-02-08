From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo80:
  prime  46357161274830326863->
  prime  6568809752638910349004891.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      6568809752638910349004891
      141700
      ((46357161274830326863,1)::nil)
      0
      5832
      9
      81)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
