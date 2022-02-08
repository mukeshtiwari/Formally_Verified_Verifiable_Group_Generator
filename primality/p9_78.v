From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo78:
  prime  11460383579414819587->
  prime  27510328986274436925985828009.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      27510328986274436925985828009
      2400471921
      ((11460383579414819587,1)::nil)
      0
      500
      5
      25)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
