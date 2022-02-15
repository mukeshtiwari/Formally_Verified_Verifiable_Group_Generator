From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo5:
  prime  50297959852185680747145399585848955810447840586016720970051540456796077478892907954491435218007602332200063716966793302736664795286645097001419594313816657534949209982127987029416902995250046132917853749070192777334053867580730274651663823919890290204105749834688276953051928457988050370630068268270473108955891442598004873343517191634850776131634047500270334533245570936510713514876230187568267061127426319524402443643538304627964479709527930513222011629114927528035708397701650659299115306251159104606567774318591078085612165396978555842176283026521117146568685255306821836921879314226601942004283073745251229799521788256143832012397074523668618738682348858215973185882639874532590503822052673004119807300160945785628583543099189707566034011180416477484003824854640479950587093015947988785963985865731063785371952141712378877762519094192357756456268719142247863->
  prime  175415078423330509052483355261908265157800980613879186298689982599820668331664288085563382718651897302144667289516830789436097905183739967394535290796766137412180752855002989539744159968784017793666330090065068620558437318036191044605439227178962652468992160960025015121779408892255412149433164993783782916747776091716330806562925510178505576655081641717021754255358768728255169514584251312593959593667164856476828841423475259238006029690511318946743051004210345874450099429731794645421801513640977091639367566563163472231756369154077457521502694200581705054957687024899156586205913684342046999122458051497784222896651721393439023469724639610837823696941353030962315088390309170062155462391284876576127748511083279331722397367350813594347326343976927575118414024169361568175816746028643953521507545500918066598434959668243250039986348179710672976634937784038607147171772729.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      175415078423330509052483355261908265157800980613879186298689982599820668331664288085563382718651897302144667289516830789436097905183739967394535290796766137412180752855002989539744159968784017793666330090065068620558437318036191044605439227178962652468992160960025015121779408892255412149433164993783782916747776091716330806562925510178505576655081641717021754255358768728255169514584251312593959593667164856476828841423475259238006029690511318946743051004210345874450099429731794645421801513640977091639367566563163472231756369154077457521502694200581705054957687024899156586205913684342046999122458051497784222896651721393439023469724639610837823696941353030962315088390309170062155462391284876576127748511083279331722397367350813594347326343976927575118414024169361568175816746028643953521507545500918066598434959668243250039986348179710672976634937784038607147171772729
      3487518757
      ((50297959852185680747145399585848955810447840586016720970051540456796077478892907954491435218007602332200063716966793302736664795286645097001419594313816657534949209982127987029416902995250046132917853749070192777334053867580730274651663823919890290204105749834688276953051928457988050370630068268270473108955891442598004873343517191634850776131634047500270334533245570936510713514876230187568267061127426319524402443643538304627964479709527930513222011629114927528035708397701650659299115306251159104606567774318591078085612165396978555842176283026521117146568685255306821836921879314226601942004283073745251229799521788256143832012397074523668618738682348858215973185882639874532590503822052673004119807300160945785628583543099189707566034011180416477484003824854640479950587093015947988785963985865731063785371952141712378877762519094192357756456268719142247863,1)::nil)
      12283214648624354234699513910368744141833160403890971621470447284587786193765271266150753854731651904314330796703512943899432515434988001553383179407042858564629647330382514048604112229937344783163930982855041075857044112817403674935552161908226691683366573061851788784772835358878737810244215364751011895062992439119210136325766107011120854517067746627404485045863492162866212235965516546916048433238485036632781135293336356855791039944422024011451734476911337891595653313063896245519072464139954018865997086126233311690374922339810440820945868732689414103306798009006761554295321105776550407511911583296495650527193330303313757519030961750487932310344012846253071683894895752745557075403090814040667342768580309505696060506874613498539119031163728811639904353568636632425838321192904775714660223432659325836016321008421783288205406225372457078220244765711340614418409982
      113864268635334872572779056998653054143281464049451374227537998220751261082974943198109810319719716197010158746479545850191592445473972599065686746989734010245906432375093266429309212385304732852796872461268609827558194923033201911900399930207385628024345932914389539523603390333924513088249367515597394530809942364730834907033143086474397833974905798567629435561777283223936316068753955304810365464332285850340927755020883489831733911430256241613917787815240954360036480400079953917775478206140081325048544774098437992941266488204079168729838330466611519206548392322245296520185664097103538905190121811150049382306599501155139429608139531978545223531217104515621166031890534734979587456309194488712064073776469118539997977463486916518517805738956974512119298652107748489075339820805602452827670853413992636931474905839094339422916098658056188795975332965918684185313427475
      77401477964237788644286874747177138584502562018931839690636395707305929931432705054396125295502397892579622140780532783637960291302369819198068008345988863556393231513473066594538359155227035425577906666506336913254766221871862659578271790021208705251420949923392791038616231791260453191693799124368125208035324529702955228097129777519900819785287392277457956757679713247894556012745560792913915866743215657484374651448474884475456225986689439436159060965179895343871520009722559719012304966146279498408313429173502173560609883319348841552184605869870344546883443280428855505973073670347886792334964350890230575173231298309837160905939963855914298092094009500316414552670970973450807484872911893989437202853974277101377800070820403864001306170766498906831431636041148984744410256690849496147522077991365134223088718452103849548568664886816459243554113148234320872405111293
      159945883887822325639665421750400766647452423710810764115828886507541131507131817225304923886631353271719180108071154220439316661351718693545712943529935794068868567169505982630189575203030161436750555744785134650323216070788000869673927924684169678950203216676092393855183903439654639766078621745710305094587074736842122786859425333851646082575784707873735871421083145054165879658944538468013779113356337416070005774195388896752727995220083964138519848667056154212288952561198836735482528000510967921690540554157435157919527372702269436696443678708950857183287515308534965554673460098513651869450597546577784706165163314446462134221860640214900236525087679962080335038806235339456519790335737111809738793933266434311518799977070517404503481039546186969953807927360787143589417923012616197072524385697369010393990762454635855678875462426458380415817341778919406082216799063)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.