From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo25:
  prime  402993608005566732818699834364724680853093899428308907232610138859612549668253870650159829514796863842127524221->
  prime  1310801189015386689170072203244765380423624402914483250199287148161025186564886593688707164628839353458066088555104881.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1310801189015386689170072203244765380423624402914483250199287148161025186564886593688707164628839353458066088555104881
      3252660
      ((402993608005566732818699834364724680853093899428308907232610138859612549668253870650159829514796863842127524221,1)::nil)
      791944834177349893404513433108426174779474809871709573662115591452475874390933069479040971221710097069058269235790423
      1229304243918111315046075903676700903526286659202069507297984466309805988498880560260580081269801761583146820699383984
      629158066298703501645053093154416493330707965246787461421080284963500592623057407940019789276421784329927475673178907
      266287836543766703051843121902906371121631036805064125944042346209063429142194364300882802782995985499447409508245238)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
