From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo69:
  prime  2041193022234480363070121430110948513149463756869655276000073739347917464092765501387216679087013456591->
  prime  2953271547517646630582922209456004302971117544134264557498712708352068657713742538018380835965305124520590711.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2953271547517646630582922209456004302971117544134264557498712708352068657713742538018380835965305124520590711
      1446836
      ((2041193022234480363070121430110948513149463756869655276000073739347917464092765501387216679087013456591,1)::nil)
      2953271547517646630582922209456004302971117544134264557498712708352068657713742538018380835965286175418324871
      31749105730618655022
      74219
      5508459961)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.