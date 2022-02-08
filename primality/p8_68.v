From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo68:
  prime  2953271547517646630582922209456004302971117544134264557498712708352068657713742538018380835965305124520590711->
  prime  463896941412524415085334837739139699906400172715066142428004893567526535690487984495785932266887237452546228969093.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      463896941412524415085334837739139699906400172715066142428004893567526535690487984495785932266887237452546228969093
      157079
      ((2953271547517646630582922209456004302971117544134264557498712708352068657713742538018380835965305124520590711,1)::nil)
      463896941412524415085334837739139699906400172715066142428004893567526535690487984495785932266887237433597126703253
      31749105730618655022
      74219
      5508459961)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
