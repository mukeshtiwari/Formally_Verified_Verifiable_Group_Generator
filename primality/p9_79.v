From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo79:
  prime  150794520695308537->
  prime  11460383579414819587.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      11460383579414819587
      76
      ((150794520695308537,1)::nil)
      0
      5237753432779429148
      5730191789707409809
      3581369868567131181)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
