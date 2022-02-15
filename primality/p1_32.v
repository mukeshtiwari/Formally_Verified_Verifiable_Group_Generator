From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo32:
  prime  638585390964319093534047013311465854729971769025737911220689->
  prime  88916657485426292383875860690053947467035147084633173684440344882184519.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      88916657485426292383875860690053947467035147084633173684440344882184519
      139240043295
      ((638585390964319093534047013311465854729971769025737911220689,1)::nil)
      88916657485426292383875860690053947467035147084633173684440344124600615
      8234810772496
      0
      2869636)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.