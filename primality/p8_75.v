From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo75:
  prime  11984146380922091022236188950771894285344073460456971619->
  prime  395359086332236444189500764819067231805655272289375265734451601.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      395359086332236444189500764819067231805655272289375265734451601
      32990175
      ((11984146380922091022236188950771894285344073460456971619,1)::nil)
      0
      221184
      48
      576)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
