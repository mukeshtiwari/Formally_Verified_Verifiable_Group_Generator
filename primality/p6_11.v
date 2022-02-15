From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo11:
  prime  47404564669958861102857741512078919215288339402719735760870188133321112351249214151689993476260528666984610557662391878741568517239802471153091999654771930501653402160636304326288214491539436262739498909473382359979237526083620751020721519689716281196148714501603501040037612147122925888952895663897839276837263139411675052502643430136721555726413363314344158056443245752623723335596946592543347716869960223759909898952586456300900038639209794959939746190264450212855378325268567168682189200297446583269509532804557->
  prime  29471417855313423947646657898059464076144760606670859722532995962485735548771636438105668944191170672264332383698709031013633147167985196315877296185371709192877920123267590399653382949390067524545146472019601813199091969966187020909582568791096612019645655805649533008130138679767871589188923855817275211973293323566116129062521427125492525121021277473526850712377626164212073724437517609297190555147383539042083261787603824190085727989193371217969315773434684026439263666925546567017535747720212654757688929602007324091.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      29471417855313423947646657898059464076144760606670859722532995962485735548771636438105668944191170672264332383698709031013633147167985196315877296185371709192877920123267590399653382949390067524545146472019601813199091969966187020909582568791096612019645655805649533008130138679767871589188923855817275211973293323566116129062521427125492525121021277473526850712377626164212073724437517609297190555147383539042083261787603824190085727989193371217969315773434684026439263666925546567017535747720212654757688929602007324091
      621700
      ((47404564669958861102857741512078919215288339402719735760870188133321112351249214151689993476260528666984610557662391878741568517239802471153091999654771930501653402160636304326288214491539436262739498909473382359979237526083620751020721519689716281196148714501603501040037612147122925888952895663897839276837263139411675052502643430136721555726413363314344158056443245752623723335596946592543347716869960223759909898952586456300900038639209794959939746190264450212855378325268567168682189200297446583269509532804557,1)::nil)
      6982240116001776174255579338266825155846651483185688718343932995344187303327249196968895116211048779572604576688960278004094907513196217419468946455021311035628791819143985863410700766255055387701501877445399608734014813073577905863806922767657572555448568183424201284020479050126748177460295332787486724359342936568091647096715694590705791519069373816476341226406839924557580094708360412993108319355252734438789876981806077304940129789245053472245114446740501335852461329533708675095819289192073424011233409866041550930
      11592456299859959093763587049704147018832061417005397351527608576353444716214094466373866436548102598833366745647029883144579146255240260367806457374279458141236793608254596437528375153138250501875545415482610871153995043833591092017038900618818841039990413613210883063310700022349282616557825353213349801921121899599410822230838235209528857755995150150637140669845456952860934788615701234825047985808793000760826128358174015232600889089882815081342968246971707076556514099356311621135286287909097024877089288294390787820
      27319712813066750203910255730539667769386141400706703745464120542198303108241512141117510649944465430602748916773357597031155405501044797980507404378949330754914309913919268549445656654012885411396215254259548935340138581895519926634738801793099080027608970689690194748948193591227791908131338530874636730317082774319991696819758972462029930475745363951990015259475114964591604377577220289718787772625811636345981124350145162833599859994347793556687754978509791124553320135750292374100367688122433451720954251741391197570
      14848752662958008211657784264437843720158168257811136457110070140261474955831268911353212086073231099648034033846208738473321589701326062156049161390288179297819695980362157185408679725916842706362317821405577634824497114346563200063142640606734034000706793191333612572245697221852758272834108612861251893843431614563020015094767417656931705321575796097660488398127215299850100223784760381705481807061892010903508975808633066080866087264330700251087505294174563158589464671038985241154305266945561709478569572849260395827)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.