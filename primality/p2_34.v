From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo34:
  prime  451964782523112428629899749021419502114132138371035623124516869980813->
  prime  158592634328230058756517302332620017588662293980861522071657483356045653761.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      158592634328230058756517302332620017588662293980861522071657483356045653761
      350896
      ((451964782523112428629899749021419502114132138371035623124516869980813,1)::nil)
      0
      1297032
      34
      1156)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
