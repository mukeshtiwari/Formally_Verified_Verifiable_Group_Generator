From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo117:
  prime  538448682474459892391929->
  prime  37680100350880616627817671311.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      37680100350880616627817671311
      69979
      ((538448682474459892391929,1)::nil)
      0
      16632231795505897183370133291
      18840050175440308313908836950
      2355006271930038539238651005)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
