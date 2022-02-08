From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo39:
  prime  12155647799415374728567975423->
  prime  230528960214814584603528114483172789621.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      230528960214814584603528114483172789621
      18964761403
      ((12155647799415374728567975423,1)::nil)
      0
      23625
      30
      225)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
