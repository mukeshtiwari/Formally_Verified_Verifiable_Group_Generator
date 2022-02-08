From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo76:
  prime  979920652329567805996085186101517086130053709503->
  prime  11984146380922091022236188950771894285344073460456971619.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      11984146380922091022236188950771894285344073460456971619
      12229711
      ((979920652329567805996085186101517086130053709503,1)::nil)
      0
      75449
      38
      361)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
