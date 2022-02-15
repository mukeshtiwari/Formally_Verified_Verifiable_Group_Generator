From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo12:
  prime  52939936705060593820485766783644379470276152940537022085047741574930086483145688893628997777885179049629547922303680762269108842854752532480185609684647862308057684346295933798869868611432417372054357754883393073613637076608035724826022767348436220738817870663220661016395580221315646795902997227362639986927672029246591233432367320261725369053511350702782857934488696694807973458296921375248411518502118235642792332231200406307337818287867015714798860389108057112394273228404704800724207893244163973900441097380614547195883283130553->
  prime  1124056735278805969200351730671750343090943067017481618084751481583186548668957805657978548538547083503488309578938916447416061945505247001341387391039028973071050233265910747652588281868588859687271120814957522446254799683753907973798997091823794775356683426073552064751024802638889835018922013869484154964856219679887682631021820384993098319940451910282624218497680593713641672586499923216238604990096534736997191041819157526250345689382485160614724918424560921833645019114013691934447971523075513367404457651208179748953524524924702783597.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1124056735278805969200351730671750343090943067017481618084751481583186548668957805657978548538547083503488309578938916447416061945505247001341387391039028973071050233265910747652588281868588859687271120814957522446254799683753907973798997091823794775356683426073552064751024802638889835018922013869484154964856219679887682631021820384993098319940451910282624218497680593713641672586499923216238604990096534736997191041819157526250345689382485160614724918424560921833645019114013691934447971523075513367404457651208179748953524524924702783597
      21232680
      ((52939936705060593820485766783644379470276152940537022085047741574930086483145688893628997777885179049629547922303680762269108842854752532480185609684647862308057684346295933798869868611432417372054357754883393073613637076608035724826022767348436220738817870663220661016395580221315646795902997227362639986927672029246591233432367320261725369053511350702782857934488696694807973458296921375248411518502118235642792332231200406307337818287867015714798860389108057112394273228404704800724207893244163973900441097380614547195883283130553,1)::nil)
      658353820510159756794599530891407289217329667375791051323360895418428866739655850618874282932083468786124342097003745964894584289159915464857486982849890107801372044468099517329826307026300380880253127686023337397069476697424486022818731167290751255307427416286898954194581757398400166533479494975658032806760876431633532795043791587100732354307434548074663244025495405849413837165133264955377482838955482702457904005871696784419782212144076233836096487899472905183312791012331966456956351071073832899119018545574702458845726418000107093936
      597621183377323959512429701859023878689450620095515503865355921894689829719783571367949063693084045538649503452859805823166409973934869134166110622298728981491209804202727734809537161630246411393559277406911657156388360456049408575173550468987648410987703544105620962760040636649468247256516546547798515963568110912408144444696689425367564713307632358306786728822331573172521292161386827961245439700473240447957823983091589691234729987222127555701927340716472162316386443477885070730755784974599562558794864942789955096318000487742765398958
      376933366681844467125464007270241054739646880566179736964205619075597219663599641845760840318533216444839687234931246249802165428588905844909900201980093429002232001257926506123933465415599573967741678027185324407432086046665442189182937124429454827150831832764434897889524347177019301805626907571887730351779807776442677949775818699397212601618775412072456563318965021247951111770997689079680232378318022923687480691136593467304211235133168934893440881940380640104207126843042043667913591258453917187135333180195117609612502468287751563404
      1087433140571445218902965988600740045245197816634773847905139638346731752192345808654542438619756183526381481165352783275425536579886186992310879536392142775806588035060030945268660836572924947971652244558187843957185195795165922654173874932370765645372529332385606915065318581615296291208432463574485500077236283448704703743776785841078396309659693022885624107667236056657675141272594750904522946886953287202390775573403196976126473565017651574433588469912603077242573665835989280351554092004912895358077628190712184084746678963576461957603)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.