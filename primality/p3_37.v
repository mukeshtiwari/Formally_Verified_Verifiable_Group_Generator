From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo37:
  prime  3099692399048396904575555146314266893658909->
  prime  2400005033196000368099521177403520479927874482891.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2400005033196000368099521177403520479927874482891
      774272
      ((3099692399048396904575555146314266893658909,1)::nil)
      2400005033196000368099521177403520479927874146751
      92236816
      0
      9604)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
