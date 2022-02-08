From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo70:
  prime  45050229465261691109032038989773195446113855210010644018090240396240657->
  prime  30368567273990281902471127902641775925099047467554000833387387110691859611379261.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      30368567273990281902471127902641775925099047467554000833387387110691859611379261
      674104608
      ((45050229465261691109032038989773195446113855210010644018090240396240657,1)::nil)
      30368567273990281902471127902641775925099047467554000833387387110691859611043121
      92236816
      0
      9604)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
