From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo29:
  prime  937598764364477287569303719232213428680284306321654126915636199637159777953028028113220958479107025589102273270129970041601488507453877352687028738452001104019042467666071805607009824281275418800547691958324111987143786238367573180562764324307686655092210199800557866992889185215926516882679752482063068320735730462254447984319457433461535547877083690949724691668208645375187294910739287170564906348156262350527433572150189991371793640860484173425831272354553801886591485189733007840045203259866572346363502478352382999147495100259959016570720444235865015781693129884335520770736025295699296545942824669675092911422366101243020205870262542081146661622883603148010361->
  prime  98559444511229487991997637661971043409442805996225960167244761669658598698644353287233673934365251422900841863882792320803106870415044133437107773957335904053377725158589802133603265718623390748894772830967072327976567665590960925167577223006899713496638043992834842420425518260712979528190412901161987678807419250461725317663677045948237897604272036061843023546870379273699927887195783711823082349633525168323875047485396442473804691232766658243730518019755985883156105019586989266209732890166340273480407929405012617185630993374591638123381631132892245813343109206649173271547151542072538314132430802952093643772775922664623756974867213103880162979865067815072097097891.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      98559444511229487991997637661971043409442805996225960167244761669658598698644353287233673934365251422900841863882792320803106870415044133437107773957335904053377725158589802133603265718623390748894772830967072327976567665590960925167577223006899713496638043992834842420425518260712979528190412901161987678807419250461725317663677045948237897604272036061843023546870379273699927887195783711823082349633525168323875047485396442473804691232766658243730518019755985883156105019586989266209732890166340273480407929405012617185630993374591638123381631132892245813343109206649173271547151542072538314132430802952093643772775922664623756974867213103880162979865067815072097097891
      105119
      ((937598764364477287569303719232213428680284306321654126915636199637159777953028028113220958479107025589102273270129970041601488507453877352687028738452001104019042467666071805607009824281275418800547691958324111987143786238367573180562764324307686655092210199800557866992889185215926516882679752482063068320735730462254447984319457433461535547877083690949724691668208645375187294910739287170564906348156262350527433572150189991371793640860484173425831272354553801886591485189733007840045203259866572346363502478352382999147495100259959016570720444235865015781693129884335520770736025295699296545942824669675092911422366101243020205870262542081146661622883603148010361,1)::nil)
      26021583204929370351070649990925082898013755731834633105991539357890243622578524749603013322368998299551362980731419592204477535917870655573886023279173423690781497019382678756040627453607318173569005048633033808457994352907792398133307078898862685867615619650774947678503307103543372309527644516437275751680891449762092790335880846141567252379185986794352132759196730507995274869613451116242681119291154666512371815833264263341352331461621066422696349481985499267083238192128667615641756007931074677577088909455669743140333558562385210807982970257009881964389360112071437963519846704040346481923204755044456104570076766568772945768280717310716442548462232233157156586663
      23652941019830159369445044177545114850764050678335912828276926884987126963240397802454068174224897640180095440624780210814299804144876075888425047304777802062741003307698387121087233466463757625799603703036749019726135190028322978374262213762683072298754786566921080719587338496854312598155917777423630563292086882129294314681386228961566181666501330488598994824847945845865070294711402216965178014382547892278414798975186215416636727487245591256267649657482104614590001179084637405276040404315704710086437976183873518675749001694532452759110344978716996744951731513359555501893945263574395412075369664588881799016780791762869976752303347910415364628156557377581311615577
      46389865905254037598777349281338240559792675246370494073807641438352486684488280874500517019295034912602711591264690042220222098833402115790698917160349776366330889059733730796249782402290471141886394440334662237170610647120395341221614940341581555490284894879300217970857432015850722718669730942275825820224680317897445816836295442481986897392543839854327728189231172437050317221711342373110670324083964029632346771307567898314127271602112340571209120192335322109416563767852621771921612917463454085621332947032149646264859489527636059806175553208001450495049479946018647520428999024464595811290102932918310414090922840137755272279116217940125359502921977021199009878949
      14492204533463008346171645154677348155219495002792776518939200126930195478578980170798086166287768274496639558659788240780479369555107264859301447538515805965416977967083188713834894926611792423892580706393355577171823208566687991716059392649533702336863932513502901005398070118373109165412471842415170999332257462052963298302012203531896415211017661333299238462781694233375151476301103829637544262990190828557842022535493816856337637278566321568398723082180559721924618505069000206461317899624391017749070761553038786464283142720973648941468128895447037790978455185829800086466452891786445761288151458858628760722761700159923989492323542234037253030114275441791933874077)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.