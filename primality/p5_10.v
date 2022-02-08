From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo10:
  prime  4419800637237745910305752305418370460524693644649581154589140717799435911569988557185156270269193971420500966557131645955401522624851960580995593977163072683650016723014858926251018552875498092091069053725890601237114773775849264703129451629275986918854060231294255536154867913361281378944944523673467350940374569212293687311798960135889504138022956306040426770063109414608347568655125701909848639784389796087835274264483749772005379676160509462543901441232264246720554442623943976647130702687923041730240447->
  prime  1009774669640285281199757907741996856811802307952992444208900811549286765397015670840785323362477000569040654525307285328169449786139110500569870665175104894515171372139973039056875945395058353496620563205016916149942686800913070875332690865352882519090460192751035645998731116665535069401088084385320822134242005457204413857310009153815949617213930233669856777763546996791943742300677510009414161437095453603467725502899599570034137952046375716222925978062194390476688559125571684744386501464389934262104468737718280638349001.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1009774669640285281199757907741996856811802307952992444208900811549286765397015670840785323362477000569040654525307285328169449786139110500569870665175104894515171372139973039056875945395058353496620563205016916149942686800913070875332690865352882519090460192751035645998731116665535069401088084385320822134242005457204413857310009153815949617213930233669856777763546996791943742300677510009414161437095453603467725502899599570034137952046375716222925978062194390476688559125571684744386501464389934262104468737718280638349001
      228466112505781875
      ((4419800637237745910305752305418370460524693644649581154589140717799435911569988557185156270269193971420500966557131645955401522624851960580995593977163072683650016723014858926251018552875498092091069053725890601237114773775849264703129451629275986918854060231294255536154867913361281378944944523673467350940374569212293687311798960135889504138022956306040426770063109414608347568655125701909848639784389796087835274264483749772005379676160509462543901441232264246720554442623943976647130702687923041730240447,1)::nil)
      1008294652682421364405181900540153130380124545403822232311403586579191134191713005158555179434873361576722807876547998790015991040301238671167940705960731294052001263888920212683318857713318645503028129656047649035240451482151881792054360526575464646377016255101662250471502749259637640064533416793800933174628942351765414833581499100482592808589591041873206593653744017271365187138427393005794122638623752283288830830179209154105533128472396616379928658350623318642118724576394219541407115046608360342366527745157114184055405
      532318735035350507008675664820497103078960184861434922371781263549776000924965469791279377561953296884591715937003417483041106137496395859406202822878365974962875466244822991243962695440661464467414093991402407566050822900656587679355786536586376946339614993868079578877981561154696646510787476297108301048028242253584063401449467526351129409215574617484266522914498139435012982139122354949064117946810069191286078283725912410631867021521310492757915799020782338706670015521482876562516748322767303619597441208163028699741771
      0
      847945571836853983649947626494758954019473550082270184907229386037047729254766277498007961571937163378908982176058839661333376174920608222834523420049852895596155416903337085855820515966791553589992444396839317801641276975871486891658538549540781024636504654102756220096763544346868645863271326380838933933042133495987150374518662470327318847649388535477602746242438750243212023028360354427534453742771600620831885289769869077942884595301321064538114173695959794577991526487521704856081005310987472898427354970608528467519585)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
