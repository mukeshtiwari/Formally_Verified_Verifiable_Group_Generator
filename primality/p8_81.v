From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo81:
  prime  4732254109989697->
  prime  46357161274830326863.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      46357161274830326863
      9796
      ((4732254109989697,1)::nil)
      0
      711828
      117
      1521)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
