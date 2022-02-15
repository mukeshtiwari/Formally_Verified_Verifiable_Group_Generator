From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo16:
  prime  12787613473983251498206557042594547289067603705344397943282110133023203593322633672948929730458767492098682165635866129707352363982925554143566585546535235262339564035955703891077285613827752251732980522171850905297291672703414007023866883662890677724456739644612934038131212366230761813652918692289436568203567071454521512184940121782175870962823159541309305226392903815374883415713936904127567643603169222263028281486318007412236303320163906682818227265953450295850225974679681119537847905360207123539800178888358357698880206086231657582688970430175793687793382397714191220566426230238570520777932075496525653558239721538201936498544620394773188991453148468033732261399593803601018851355383334435486225901867127339836621923738512540259052782167066982186679306758040397408551->
  prime  3334165611525549096133388443943846692867752584509266253343717703423671965701383568082666244341436283284857795774901919463116811270724111434068690115890318030890843889350874498336144987235765155603346943467955373941784046990651947707360908044960137965808503554498508743498103525096811450720980102315393954173988856808623211958028177712753843539620733679843740388898327383397954852512757624757151242068267978113599805720027718800970684264788973492969320101228451595968226273305455440174622481325753295072858167902735369319462657931370819384973024157161579109859227748706157832224838873033363938043439456889062363163309534941470393232198546999289124739838079079391435847786275468340605567505081430693188261000308721101986705619080333073357867389608617085290647039549776587856830059507.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      3334165611525549096133388443943846692867752584509266253343717703423671965701383568082666244341436283284857795774901919463116811270724111434068690115890318030890843889350874498336144987235765155603346943467955373941784046990651947707360908044960137965808503554498508743498103525096811450720980102315393954173988856808623211958028177712753843539620733679843740388898327383397954852512757624757151242068267978113599805720027718800970684264788973492969320101228451595968226273305455440174622481325753295072858167902735369319462657931370819384973024157161579109859227748706157832224838873033363938043439456889062363163309534941470393232198546999289124739838079079391435847786275468340605567505081430693188261000308721101986705619080333073357867389608617085290647039549776587856830059507
      260734
      ((12787613473983251498206557042594547289067603705344397943282110133023203593322633672948929730458767492098682165635866129707352363982925554143566585546535235262339564035955703891077285613827752251732980522171850905297291672703414007023866883662890677724456739644612934038131212366230761813652918692289436568203567071454521512184940121782175870962823159541309305226392903815374883415713936904127567643603169222263028281486318007412236303320163906682818227265953450295850225974679681119537847905360207123539800178888358357698880206086231657582688970430175793687793382397714191220566426230238570520777932075496525653558239721538201936498544620394773188991453148468033732261399593803601018851355383334435486225901867127339836621923738512540259052782167066982186679306758040397408551,1)::nil)
      1781027244775142543305563960869534465678205162724254953834429949369656343684960871249000222030741267376207268484953572305286667678141671697454297197880613130094820492126502780608413362094485282146481358866313749629168672806704737256161690272429585009554430555545744060322844670722657886320303428787378080046323700843322240849747140976416993916068276855998881138617188713779224236144363537108905841083128714008737951631188028165635051612062899665929692842600618565276624772746829888516634752860315966694684941503623950385397022610471643526573053871255163464946215202267969372031347711620941384665849690960056537501260857382163653668167724926076766491342845558781949048921210011537786322566091647838182589005270102267913775502008988396757180102269804991369730812761696475090502790684
      2193679400936687277744824523397252249322580700010183918963381744354522068163227845706758040608361455045782655366474401594325360670308112505866988772570832416733958979000447238372161252915957002894093757681733105902093438063533092836107638454225238656105628868696376752601188183258516593206797772384716201428152088837763591974775218223876034670732867424828634580085599687165360378109044646911299835439994798841429363738030288755338472036451072022212342294236214347038564266742328468017767058644011738900213886992079874678616873481935035362173152937706900716502569962597748949738753535566601521307556517755693879660782879667610887574730695106160742287178814326385802177261167473729539817128904090320632307978693022723063685655799253743928297070043533764029444516469087508147487352845
      303125890167421163802968703035039322921918280768514133388689768678629546714771191861308443202942277686063713540173168578508391425305547970847931378450002466365648069867527852039269649462555953897595877632640847467787777714850125247651838898632123582963542907413200588716361196146011404072229761728078087957451964048179538378730094909289802012230399799996709756364107732913464974330166165805168112870695614687196808923400612528642340850494698257171591064513688165084230577460700708133780225878291559742730699311158439192556866679163100214629172313872378244731795326220668748910879586290809631117724110088852509485681494518168321704549703261894603497813421295949160319335551520210153876659322087599253100276975471000092648813242639875319685071647413530889394186258287359825532843456
      2811963242363457192125481584682181044020116820941432838244469030102730046975720957893946050619261297091552998033969313322137292479791704410907474147582770353338972934127539491192156652079253646740317370964884429844439759203216989618156683214189768771602846583065604879888110162783695700567927615706233523822013488870593018878633589721070775708402939534488081517720180242541019215471416088959932777377731208700173544376854923689630358248101299158038186568320490452722557747609857181751920168928057947546024751532985849393830269666604309430862397122770527530917626374458838910857013636584573987379534158351196968975602563246667551901305129212946351770717556436445147285877258287716079899718802195463125345067913508125844459293187918362062516433664258888267255242808495932578016003260)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.