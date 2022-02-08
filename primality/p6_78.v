From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo78:
  prime  66576253->
  prime  406847205727.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      406847205727
      6111
      ((66576253,1)::nil)
      0
      740292464
      2513
      128881)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
