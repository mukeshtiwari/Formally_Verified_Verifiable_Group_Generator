From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo118:
  prime  4088601288693391999->
  prime  5665946868464462250896653.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      5665946868464462250896653
      1385791
      ((4088601288693391999,1)::nil)
      4598956468621534833922099
      1082113175760902255013270
      0
      146549572109561995142831)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
