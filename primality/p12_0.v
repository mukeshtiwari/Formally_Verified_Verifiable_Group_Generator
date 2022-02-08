From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo0:
  prime  304571472569627817825321002020795071014107706457806014245277006696197556847225123153130898726985704600510652537924586255408189227983526805847129733648660949363131771763661151989119584630564465639460917043689298449987327548238692668011190330334256651924186733840882736792341920126329551913312087292479995498537880249905072228712829055341219280588843041059985766386036413825283724202805849597824108366550112243988830265134781458888772906245897246461936662860025540231150062068113128037939688134513499731279147072283469374496475909541917519175891877044677750296505512872583800583121465068285062892385613744511531318971027622956695713743178419717927181981646140762830116601423846029237429829179090545960661026790735613835535417004085479675343858091643668964486202840300915892513749878236309856919304790499421588028496002447957628237116482815403032446039021764675159487515092366817050242111288485725920826990538995362871111149309->
  prime  5482286506253300720855778036374311278253938716240508256414986120531556023250052216756356177085742682809191745682642552597347406103703482505248335205675897088536371891745900735804152523350160381510296506786407372099771895868296468024201425946016619734635361209135889262262154562273931934439617571264639918973681844498291300116830922996141947050599174739079743794948655448855107035650505292760833950597902020391798944772426066259997912312426150436314859931480459723720550393527136309279783956238570642752324074956764864535468398249803497540315782108949050329323340173081976175319156914813688634593077981749180737988015889880044283090091043893578292543853435299066768677766995319823731825791939309290907399147361036593410054792752734769478376751139521252251296265424144809100215289499080872374072576993994832895087491218608702018076789260665087512684366936082611452521261814776401093498661330779524451857606272491606063934695699.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      5482286506253300720855778036374311278253938716240508256414986120531556023250052216756356177085742682809191745682642552597347406103703482505248335205675897088536371891745900735804152523350160381510296506786407372099771895868296468024201425946016619734635361209135889262262154562273931934439617571264639918973681844498291300116830922996141947050599174739079743794948655448855107035650505292760833950597902020391798944772426066259997912312426150436314859931480459723720550393527136309279783956238570642752324074956764864535468398249803497540315782108949050329323340173081976175319156914813688634593077981749180737988015889880044283090091043893578292543853435299066768677766995319823731825791939309290907399147361036593410054792752734769478376751139521252251296265424144809100215289499080872374072576993994832895087491218608702018076789260665087512684366936082611452521261814776401093498661330779524451857606272491606063934695699
      18
      ((304571472569627817825321002020795071014107706457806014245277006696197556847225123153130898726985704600510652537924586255408189227983526805847129733648660949363131771763661151989119584630564465639460917043689298449987327548238692668011190330334256651924186733840882736792341920126329551913312087292479995498537880249905072228712829055341219280588843041059985766386036413825283724202805849597824108366550112243988830265134781458888772906245897246461936662860025540231150062068113128037939688134513499731279147072283469374496475909541917519175891877044677750296505512872583800583121465068285062892385613744511531318971027622956695713743178419717927181981646140762830116601423846029237429829179090545960661026790735613835535417004085479675343858091643668964486202840300915892513749878236309856919304790499421588028496002447957628237116482815403032446039021764675159487515092366817050242111288485725920826990538995362871111149309,1)::nil)
      418307829879905331169095347555150083232631780419646630593557313272453714583857629066400342032929915963643795832712207053651430073726298497898226153039084668066729734366624703643529649523131427948000412077964275107811856040728541660499511466241923781285883471548363862675115828388193547874135934903864934930251070362933510706527238131014863348868265024419713879675408123454151723546543847887660441927451855161645987622275188330984926873289517938670464417387041101166485781103429342140127872305235737861325800579658160156157075930544999978019652952137337932885655518577525665794618413281641245726560682017286798756008004873004657940679523563646102080667010911738319494723175327399657240575625529807456677286102014401994978480897092402188496679823622727431584978264843957266757656378975811753590244892769688364919822704026175976467163012766249888225039375580304297109671336960722174628126341375398598298809951595404368181355086
      4321210831417075499700112402653286002876647689383186402924189903621532500441359791385857115728947175912195859745187370707992551810287355367662460048788904642293804816327201116898643562350942795620817896814051005638590877769470983344490309177937278928005368130841941665687249803354011922347037587835710151013471131266649972382623210239729055071545479033098747389499911563120038665150562360944817491843223711262277778265756082460219845555345680196606546892418428276723329387580801800821366315046388811030565319613324765020941591759196872521052668003142839806666491820664616154326889076420212027838993346975227256086996359504516913837840748630790950205037615811151879316908815480509584065060395226273216139849445312257919422600536012025796594714138665281628490007529927446145800269075467310536861057144789510827430070129466375979009793426082869459938807777490874328509124002593344160729732598092984301261830145203375228243880992
      0
      4424144085574274437413122981597301135256175594237293332566571368017362172529023727062117632703844929899565468558859265403295373580198311691573453524355461512480658058433993474603129150017108372890044064934084857490777890053371390901048942751051154038767130956266627825031083745359923199334430312609414052769105163066075713358622888711189740892847672670455351915533607809420190422301103383040348126034009713178936487306978247026213944698216458569837756726133780498535105817362340745264315761852210908068828338383095318320962946996527142171161320528221923294559888826503500129585731811784262721839221821769391953008393141128129062328830515859547885223937244264380651958450636280742430966829856323665833121466203408892137240115499352770545192328183464320726859874208550820577436334911451691023551874807818194382992721453265129648474191852950788965251952467104041955774262638800196705209810274365507600407719267431326255445930400)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
