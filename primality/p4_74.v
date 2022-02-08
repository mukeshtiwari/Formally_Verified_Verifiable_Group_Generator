From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo74:
  prime  3162893595045828086340899413494056986611788281->
  prime  43096607629079989297774329316631567909409028015077293.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      43096607629079989297774329316631567909409028015077293
      13625690
      ((3162893595045828086340899413494056986611788281,1)::nil)
      2178
      0
      99
      1089)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
