From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo113:
  prime  157702795295546355891797783928828805431555932027233->
  prime  4543732938055281605954477746564631522375922270201138151.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      4543732938055281605954477746564631522375922270201138151
      28812
      ((157702795295546355891797783928828805431555932027233,1)::nil)
      0
      5832
      9
      81)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
