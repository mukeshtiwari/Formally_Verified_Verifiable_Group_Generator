From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo27:
  prime  2495818402816583323207358081158586878993786719628341989347711310899418104805155559945536794672267398304554130331604606795791791224594115760785552624309250140517414963646349784776030011009156173393523726794427317420334256620204628945060325088159942732461237212553967650054505517462435791907426037386827224055543988310226389748116018664466272555050126705428869231829896504807638651254129500455062161822533981789715736359621385475897833224375704620964403839817271714379718642151999619520000460749355554457740343822046318041971214434276524372809872638736666341921494219478755519113596174440921868925080503156025045865196652864204026200639102583651913586993155983797666155473261172943->
  prime  2560515007454394796111539217338379768071063658974547870395582683500552820917914802370444999463761913803404782498060461413152306036718044429536635719436594522659907394333990463896994260954535519720230648840392462342504161220313573336574178835095224767972097403577791599479218409486097052505250335127968559357511799575204078223166682100286567275261531960181177005830275364851923443002962731247862164535973740605696719475112702891628547941002505404674395607797464525931244472355146685551701642802412436532225936753635288643713043767699699331384724500605340616921947895421649704330656101858669479553723677911219020501646928770050064564644107117059800612283612392366910191119509944804561731.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2560515007454394796111539217338379768071063658974547870395582683500552820917914802370444999463761913803404782498060461413152306036718044429536635719436594522659907394333990463896994260954535519720230648840392462342504161220313573336574178835095224767972097403577791599479218409486097052505250335127968559357511799575204078223166682100286567275261531960181177005830275364851923443002962731247862164535973740605696719475112702891628547941002505404674395607797464525931244472355146685551701642802412436532225936753635288643713043767699699331384724500605340616921947895421649704330656101858669479553723677911219020501646928770050064564644107117059800612283612392366910191119509944804561731
      1025922
      ((2495818402816583323207358081158586878993786719628341989347711310899418104805155559945536794672267398304554130331604606795791791224594115760785552624309250140517414963646349784776030011009156173393523726794427317420334256620204628945060325088159942732461237212553967650054505517462435791907426037386827224055543988310226389748116018664466272555050126705428869231829896504807638651254129500455062161822533981789715736359621385475897833224375704620964403839817271714379718642151999619520000460749355554457740343822046318041971214434276524372809872638736666341921494219478755519113596174440921868925080503156025045865196652864204026200639102583651913586993155983797666155473261172943,1)::nil)
      798566202300128429185582273290594893113580277514400012387849267373159104817095178930441479662244437769282483616256894127890950168008584681486143999677241446122602636539458795642275712578997604302769662566901840146978695704604117112502776154469194058963919258096916279958732238526435173839475115895924157254038951260860624706653036709863380837516588477934763307907986908031905394508983011638084956615594710880575620697931240294042060904450066917518279113114596440793090414281135201033593378620146316715044815381274802100201820125967561023732536815459826638006067265183442969598959799602732032259884863999550740420794723555725325171817932336600356251257775729075883544547098890359536793
      210735362007373915946709539056606998678729791874031995596758928072269540806941042716723274428104223053135320792272214377418106492261078707702669362878780722272189921811632097276315153717212810540193263267772282451254674710839271226625616655344539299069476974677587136951416460854795924713932700228057592564930013510859266559251414682592684971858902549383345409928756232084303260880219572445310747558314533139607038699166187238585901783934034245389558344979004381207676641819636430448178556902506891884483852937246268815570189952053729064724383710940070294950551040585404546952823032911850998216416223088499229055374360640317578958656327165440005853768357494468055451357949033368825654
      0
      2135250972179024443093763221782084996315734159139084966836054089185927569078238500388096600262013590191758602834983442904798033494217921759269253068889819102679090270512492906385098090504912544846083993218490616835104486374899413632585335834351298198053764763424628326217110259107984004874495719368510391822174533925470308699265936559937344303539758510509046622422791853228371865558862916458533563113211745589859842823570407292395843798796981953136184548605485690306846047103684682701184680104222460591594700734085451139324397729754653698587759168945364566020678563285736824738694492077583486041580370046646967190363882192631408647693684749640432672170484848501248450322430486092558684)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
