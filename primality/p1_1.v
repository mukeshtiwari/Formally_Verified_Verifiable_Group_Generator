From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo1:
  prime  101307729990178565164101868459786605520876313062602288906594143237961150498577825686759201098780514050346225249084409624020624258316174915232470517151207079710288244287849444987159276947257058128784750373420252816227408295948087050083741790160177300045750282429727837487050942486388655637331833->
  prime  38631372753964821718331473194165046923459201831222943021884824858502011636171186535654825877394677081276375035557610668698912586550932031900852284893724235030329076315140294787423285527263391882311323529614629052560823853294083503860006988125834068352153672805506267153507201033277541184789704173023.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      38631372753964821718331473194165046923459201831222943021884824858502011636171186535654825877394677081276375035557610668698912586550932031900852284893724235030329076315140294787423285527263391882311323529614629052560823853294083503860006988125834068352153672805506267153507201033277541184789704173023
      381327
      ((101307729990178565164101868459786605520876313062602288906594143237961150498577825686759201098780514050346225249084409624020624258316174915232470517151207079710288244287849444987159276947257058128784750373420252816227408295948087050083741790160177300045750282429727837487050942486388655637331833,1)::nil)
      23617137401335295891398236645947904710961261981164734814453012780857812075797912167011430446079595692206574830072793686238048074377206430104611210944034434650286860026100605674239975077428924721408530984495541503269804584095811981788049034138649734646852481212231594232875889502566720464362333978387
      36145011730076131074377850194509652261305740382492650947301610540700628757241139497232611661279555268315467659775411458839446532475662686201315999398501888782421619686420390369494941924209612187403207600125132350008027138522417515786243222373483398577586643138533659159196233249061264439136681408696
      4387509620977331433502688589286959500589671318222525708942185621324961330936623120835321166143543654579563093930122133830594685016512846452180708790992845111185107568846139371460817418735614590265397357751430425169623529394979588710556323628713409027947846155010295193647476364560123864848285307569
      1529715144568092580689684603038489194333568694086856840301821977063730741593887810206219438910485128696163221768173647681063715802898945102598483349801492514523241848289825670548868007008767921215794249745601687713522966639621475775459531910707635845033698373621734553483641003404929535844409588758)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.