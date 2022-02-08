From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo12:
  prime  3881267944629207667374431089735355700762451562732913893345018711258286802278200685763012742781907555051762495632961718232471173081315579837779604480776631654149560342225791434382447754611176669336309687946088513861443686594345090998022014633567956684320263383418080034473968924409175300398458567663150138571058057414795873450227981504652800005476055952551074573035122112740856568695179105706166036526707558572060859047135992548936252871278630546469182400840908344191144384786593447692108469566173261987858093->
  prime  47404564669958861102857741512078919215288339402719735760870188133321112351249214151689993476260528666984610557662391878741568517239802471153091999654771930501653402160636304326288214491539436262739498909473382359979237526083620751020721519689716281196148714501603501040037612147122925888952895663897839276837263139411675052502643430136721555726413363314344158056443245752623723335596946592543347716869960223759909898952586456300900038639209794959939746190264450212855378325268567168682189200297446583269509532804557.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      47404564669958861102857741512078919215288339402719735760870188133321112351249214151689993476260528666984610557662391878741568517239802471153091999654771930501653402160636304326288214491539436262739498909473382359979237526083620751020721519689716281196148714501603501040037612147122925888952895663897839276837263139411675052502643430136721555726413363314344158056443245752623723335596946592543347716869960223759909898952586456300900038639209794959939746190264450212855378325268567168682189200297446583269509532804557
      12213680
      ((3881267944629207667374431089735355700762451562732913893345018711258286802278200685763012742781907555051762495632961718232471173081315579837779604480776631654149560342225791434382447754611176669336309687946088513861443686594345090998022014633567956684320263383418080034473968924409175300398458567663150138571058057414795873450227981504652800005476055952551074573035122112740856568695179105706166036526707558572060859047135992548936252871278630546469182400840908344191144384786593447692108469566173261987858093,1)::nil)
      6610145780462501766182261914744661032998296663404973020740918467278572190404050394417015549471628827882546198720460522151302984975330715484705276130708009865116155577162192849502701054165796068385768919503553345391356370205661052531219651630598751795789520649093789452410103975887852426314140584743462058193925241686559368954525774209508639519163036719733462328988518490588033725293307113346276604816289307958237166829802422048048745678695519537203957143865995698472781481381388921433857681595741287414918099235126
      41002700827554602366229749737082511325090347614989777570358805853186153698610814113784814603221478171165141199553280569983182906284967443280445169830625531361025898548762281005218802842025487742058173033221709394446989834660146560568297730847458830579752253259810770381079629676862488747569270311565536048697005116434162589830398567157819577289277698200749063897397048771664453106368873491327376824011454644304189698992546850461190608619522756315694547856767745138042361387886431413396192855926806809402133244076449
      15047563762748032973940855939982110042765411216621058424022031317776120291926518561971977057404827369520986053882873580341833473566561063111709066723019065908026661533134191829703604979730093863831618678035150215383521897511724535854897705060244640722560915702117564176733128878084772477022030970550583177618756220047482989229129843184736527512150795952010473507837966215233565618240902243318534088808960281995829940617141912366314973223576700491568843541235359253811252757369814839527015781886916417350883987007265
      19979322902223313506633353558879924388249983978670241045878470394591900879887643737231165647133543093358850421896991295580284660016075320972302800596087520865914704076703684208711557632252101628449344239368329577184899102166574772694199986916220189372335207546625257910735557878567298421822429537137793949533814316372579243434707449847629926256438327793642028590693638981552821528691085048897931137597637085073788924283125316481228643218336436743107882985138292519209215239612090476831283265028524307109757688548469)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
