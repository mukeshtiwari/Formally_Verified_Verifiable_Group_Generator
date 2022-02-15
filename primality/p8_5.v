From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo5:
  prime  12127071018306873000555666011682051952469158411327557527463115015829230719613149714478768721485628701266398118373527875072713426428199676249906109205914581904868615620410175437197190250766061604508671506732379598410733521237576061929546887655702260579618567968705092011864160459193125269412608170403606719378651805337199983817082534078613649397671899732232687862936007286610191402222560653801774616656063013760418981592055421850835721812801874357383712339316768222054313719064693909253682757193839808284594835468821720473758497640571210173477464005444329607308998493237244090420418937->
  prime  19067066331166402133202658667185374869464541102853212856377014235282872071218325741032677134036373895026223568769501792724200357110544789576468628039510937435313492887349167765168337907142707977105662475904638668332039225636767427618154473695093960348298624715859861132769699157656952646715169680871252078071645378097038183636614035747774862786756741004470153984535264039980364748013481151070768690945731114822053487600833164769987772842691864593525605407765424703001753600304132853846773031513087215748412625127469889648378434687491208537029748670809277389745704189989579122166230597951969.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      19067066331166402133202658667185374869464541102853212856377014235282872071218325741032677134036373895026223568769501792724200357110544789576468628039510937435313492887349167765168337907142707977105662475904638668332039225636767427618154473695093960348298624715859861132769699157656952646715169680871252078071645378097038183636614035747774862786756741004470153984535264039980364748013481151070768690945731114822053487600833164769987772842691864593525605407765424703001753600304132853846773031513087215748412625127469889648378434687491208537029748670809277389745704189989579122166230597951969
      1572273
      ((12127071018306873000555666011682051952469158411327557527463115015829230719613149714478768721485628701266398118373527875072713426428199676249906109205914581904868615620410175437197190250766061604508671506732379598410733521237576061929546887655702260579618567968705092011864160459193125269412608170403606719378651805337199983817082534078613649397671899732232687862936007286610191402222560653801774616656063013760418981592055421850835721812801874357383712339316768222054313719064693909253682757193839808284594835468821720473758497640571210173477464005444329607308998493237244090420418937,1)::nil)
      129396702582447683697619681542146040994686301760238976908003647467044499181108237993466482978272035244770753055450415654958995339477567981051460757459638319931049088123107841747904473968134588233542000875351617503847035310465743550461608349660897824611763523917937748938365898841005528040750355349202417057515073397109169527033354450571516152894527387094074091519085422542708446477389958052252592685143090207705377511584389777273747094779762002990757486276963975918341632648650621776006653097860642677893099164289440331479130926229477203702878069448246925779150188459716744259230213598179
      5211835903505528658793535944292204727503110321845123081238444796790989153369854417881345724374238533011534138467456629886591557856405099113188923138768677291438654952419054523373433328591577820835787820318844481380097975208283061881247820787884579913631532629685938012590602821387508440239535678462941419349033611075617632903878823166093010582149861954968271515912385639402535760377023575882058846403776164876347496298447514126076177125007657488451598803471330788848802096685019330598551992759689152284711606340228390983389376793712148663103731848180700914163392229629971215598298111239419
      567097352579788805703916691481798645336548317784036998896357337883499019051058232723885130155737563451140361424699811049748286843174318201514106355949988374226611266185186447052771208604864668132445650055018876313784968753586146023575154010059371401544569222393310485819527687891402252206827011991444308430621872320896668426307664571674212465386892582467702228100859841858096521569616230349363264236565359224295341055765985509360700354437060253019199501022306879366618044519083707624268502197953155320760733992354365747657360515795537528956778113833630197383499085722116621994493138792286
      14433756174692443218468938449307011272290647133649783101944592150427836890198388913347476909903603227629914657839516399782844217501200196540273648827751246889998509497890462731368075806894901513627732016505435746209438019430479602216944883343193602169421213150953951223560273649411827908077373460903580023438563272512192649855962066378203674327971245999254888648040032760404775283141820504499915269161121142481252380652046924028324635857717222434650329908993787582381657740973367939117985472429107530132277801114889662143068826988147749426273179976609874508783609316867463263099550723566754)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.