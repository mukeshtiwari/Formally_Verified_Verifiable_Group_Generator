From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo19:
  prime  259909892572069592252476458719655670084312328203809996051771829225336486837979297334465016263776616834448275740415366435934398679665484932425197272659948497556322927986118858747392228346102317255385356343549928310173527985011726235351315483886212732396589242174346339172120428803003360552651291333870415155348570194126658670414305331017274351821087540518502917880677665699591681387347396839470712511340541648435686738306561131992119411599139581635376951729270287788577102568739417053099913973655708610685384694216258254457570656572378734719059472540180065937588167805905686463489199348106397376576565447579932589995161704455054474702685439313852546241026853379400700538870484377670063459403086672996919340100915117009339214073257200105746753847815425078031->
  prime  2204490829049270871185608890676587958328148041444100838644674227998205535964549956246814449454133435015589592513819712664164365912586630379819751559257692689288977075623684552961384921794031187515336034191798589619587365612119731361100084597546506784220758185929817119827355975717154983296713658067940935279153833655096180169410194317134571196053665531521727358691534914182314046653516098138839594679475879787787575529326306712819694843754494096301005524394749071965220880998741598590453260958271026692283892814777273167176699076559519596379161081187312197516910418821384445573140568461352754675156378641501546183426904176949961577993862430111485548368562220594217129667419730557107632404557567637606478075684128419218106259082748706155183106925188401685231708479603.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2204490829049270871185608890676587958328148041444100838644674227998205535964549956246814449454133435015589592513819712664164365912586630379819751559257692689288977075623684552961384921794031187515336034191798589619587365612119731361100084597546506784220758185929817119827355975717154983296713658067940935279153833655096180169410194317134571196053665531521727358691534914182314046653516098138839594679475879787787575529326306712819694843754494096301005524394749071965220880998741598590453260958271026692283892814777273167176699076559519596379161081187312197516910418821384445573140568461352754675156378641501546183426904176949961577993862430111485548368562220594217129667419730557107632404557567637606478075684128419218106259082748706155183106925188401685231708479603
      8481750376
      ((259909892572069592252476458719655670084312328203809996051771829225336486837979297334465016263776616834448275740415366435934398679665484932425197272659948497556322927986118858747392228346102317255385356343549928310173527985011726235351315483886212732396589242174346339172120428803003360552651291333870415155348570194126658670414305331017274351821087540518502917880677665699591681387347396839470712511340541648435686738306561131992119411599139581635376951729270287788577102568739417053099913973655708610685384694216258254457570656572378734719059472540180065937588167805905686463489199348106397376576565447579932589995161704455054474702685439313852546241026853379400700538870484377670063459403086672996919340100915117009339214073257200105746753847815425078031,1)::nil)
      604136861086997057073987351013172965360697014595674923636158649133065010285984721552823103852872993848628490174878910073585633331904709711876901497918739320309532440602330703579316121951939362177771555098463987131411885639519070802269763381453858482669723767231554815964664398362351166734012260093309459729048165699308378416028292770792814089999596280280018271074412403445165755924077958813001318553621505087795028394099791295800613418758847727701988633934602452300779693911025737406697621122594143100412600847224398746354896099941117135319882070548062501970635897107542464671844796106887669846461441784565152289633028040469934679257529520040052661922547281573199126984940362934590305651387813048699296879843726834882991162612496303117940000497926442400210168125049
      2155878846423808442700504717969123389323520500191392105007768758942877917757221677294272735090279109965836238951705475244954555296405328965715506736083289212388504123219994167731169595878257962767412137290533432653285692398416902022266316946726362395621392663278478373082078775320549183347119411861979836647481349655725327600607001191962176325501684426370621034509011120845023775771646147671562551052172879869414967275711097926763700793133589141788047418210837885638065963736994370781608578944713635135290785210522280378265861348582228929293942429833217338457582463585940974182627207586997718504393094418875429338201247856083064878314141772532025238268947257364418951852727050105479181461960028230350929890307044157166227163217344738872547854342523231186972102073747
      1648551358759358533372685450358692378098969093716280881584459072270819044508690598757443324335368639143199041012010252478609167757214877382868430851978833205956385339785238444592796427612001967360062668448360817714087243021084992438553494018333097475206955277852187061962987345517034607081490996692999691847124247694157930419901218843612185759509131373674175056283033354300929595795863032018359511887861250044312576716503067540299461330062707178752752266445475877091334147114677610131398079016802687319263921072893697975116118084097861629533695983373275972365084417179730387112668808859617796088583536633550640926715717070834384217381198987392731988331043911682101896831903717159585017882040756491389146358078835037294127723685619414475810193914068762272903249177953
      2121126861087691350410190130502440040730777167713664400650170250066493588851226709920205737626052902310599112704333711807666402913913218875466965194650283516765267203111488732029627237192972320016448255209118549393607898136744901798285413359601300162083107178087549924935048310011444843775233729942963519163839819085691817999902032541915829625462016997653685281635416359650799265512661772044510915855174037796726297660506950130213186256735270173215143877199427908865587282425184545194187273743057591207114329776262109411221132566614247700388775469887482331743858209008923596971905073520789187826647672348511590986058989773723969370940185100899225111985894369339106761820691376824925519156712839925800922384620372945652260855512642138231762027574259475488713185179703)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
