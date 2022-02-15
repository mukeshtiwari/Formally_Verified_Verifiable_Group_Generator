From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo51:
  prime  145242637171307790715551623128635301098968364746227216937898906803757439419368923829676551900736035547968971467088085849237897311410446384003968773281533646459824353277896087709988619627427->
  prime  5868761869339351232865961792867630800562080621796728395058990657151239370429869454460827710415040073711572662755525666511497953880820325435603903393658184232069193331597345059026708026908049122257.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      5868761869339351232865961792867630800562080621796728395058990657151239370429869454460827710415040073711572662755525666511497953880820325435603903393658184232069193331597345059026708026908049122257
      40406605
      ((145242637171307790715551623128635301098968364746227216937898906803757439419368923829676551900736035547968971467088085849237897311410446384003968773281533646459824353277896087709988619627427,1)::nil)
      2533577691596196520802295155217441434268524762428360131413470396466690158591079390484958584040789831759564418471066582110039021133733642457733230094242357682473580257229004450597410161092029285401
      3616909290999278267960586668535631940476611987308304144863089333113563895719005063351686284041970435137701579554314726040240334910233808013894591450328249674435028394624476989004946141176557040595
      0
      4145501166427186074063539804825215903768710450458116643805526314677136373501954923354406693688435899512765900895493827128801691893289918472599727373766693617586217256275321368692848428865028954471)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.