From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo75:
  prime  19370619978509801223531832058947481482641431->
  prime  898699913902962227765760947211611985893554528759.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      898699913902962227765760947211611985893554528759
      46395
      ((19370619978509801223531832058947481482641431,1)::nil)
      898699913902962227765760947211611985893553378271
      475439166
      435
      7569)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
