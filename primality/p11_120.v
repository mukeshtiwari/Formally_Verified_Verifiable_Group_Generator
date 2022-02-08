From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo120:
  prime  174652674517->
  prime  248880039264721.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      248880039264721
      1425
      ((174652674517,1)::nil)
      0
      192
      4
      16)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
