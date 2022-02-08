From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo77:
  prime  1338497435222454449100745906007265046125174543148304922393821903549249564097568924402338444976342637235059940301121254036728543372089078678870002316661974701903751795156058685588422425194882396861603369842973666001799140241957783417325121458013960460641392494011248469345599418951097368817217046555480261->
  prime  146440988895383073912765307338536846901416971242226596644340873001612747059222723312086642249526718911976202888524773040396359744710149831019130343459036689676321185178496439015951414205778052893214966977724728224476859038555492547180735032037808420252359826094087754494746140836757384558876092866851681988111.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      146440988895383073912765307338536846901416971242226596644340873001612747059222723312086642249526718911976202888524773040396359744710149831019130343459036689676321185178496439015951414205778052893214966977724728224476859038555492547180735032037808420252359826094087754494746140836757384558876092866851681988111
      109407
      ((1338497435222454449100745906007265046125174543148304922393821903549249564097568924402338444976342637235059940301121254036728543372089078678870002316661974701903751795156058685588422425194882396861603369842973666001799140241957783417325121458013960460641392494011248469345599418951097368817217046555480261,1)::nil)
      146440988895383073912765307338536846901416971242226596644340873001612747059222723312086642249526718911976202888524773040396359744710149831019130343459036689676321185178496439015951414205778052893214966977724728224476859038555492547180735032037808420252359826094087754494746140836757384558876092866851454145287
      1358190060766
      2787
      863041)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
