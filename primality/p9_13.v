From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo13:
  prime  90858923784501841327158074304454411157898066825429619731136410875165154613128084150120623303371001718366814566569301004588000662141472470521983574862647817088721610657321691912681742019203115810431960380154078144926387906804037309697838948641172556834440590488995908737962372942494808213993813561980654319630010394763026637399333347944596043518880650820653051425833967894132989291534333951592829136768984497563298943375456846850888782262298280266830020065633771776608854103573072012829191973905878359618313272457->
  prime  367731414202515563126171918661655600480149842530600324091205421489007362203435212783883124153845745803600950472679993566878857143169735209311387995022667047009842213367442686252090230658506545660487730821231924631192228556169096480278326555889047092801634934325288129478736573815480544478149865739339493681159725136180259334324655159127664844756121185581406638609178031212099417097690686363503599148555770459589335205575255225383826032509129638959805352712998682018970613762408248075405401936471545957661256394258695269078772103.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      367731414202515563126171918661655600480149842530600324091205421489007362203435212783883124153845745803600950472679993566878857143169735209311387995022667047009842213367442686252090230658506545660487730821231924631192228556169096480278326555889047092801634934325288129478736573815480544478149865739339493681159725136180259334324655159127664844756121185581406638609178031212099417097690686363503599148555770459589335205575255225383826032509129638959805352712998682018970613762408248075405401936471545957661256394258695269078772103
      4047279000075950
      ((90858923784501841327158074304454411157898066825429619731136410875165154613128084150120623303371001718366814566569301004588000662141472470521983574862647817088721610657321691912681742019203115810431960380154078144926387906804037309697838948641172556834440590488995908737962372942494808213993813561980654319630010394763026637399333347944596043518880650820653051425833967894132989291534333951592829136768984497563298943375456846850888782262298280266830020065633771776608854103573072012829191973905878359618313272457,1)::nil)
      268912303248352450689088167879706986988743267073133964509253082821200497137597454673530151056958440511128911427901967129652768869375019494931829545571585886979169378549183135869578759176516784927971550705023492350149807998391038369895959009188757810740037776126399051520956894923706105838481449625240031659291048190463015443660240688415761351223572602445111299664808688422232088322984905654102915314434544867058266528128746129377834111404570520809852979680672144538400236153458768252621238569796968877222515152764329762600986057
      316984503651706542984079931964375971484879658751451521511670542662681358469390259427262133140432352453537210355243228360400945441878913738185077657878830948336750550025588900625238579092751099756503199423019217181576133190510192791353093683444865949953322982335549293332499865920707479225536944150555619462052505800883166694645994696207501311252013913006926074594618058459992103634616322723966099500200027473543946185241272185570232176591189277623359577264112864525410885551597809813675530414366312349856057457603720427234072760
      0
      26153913450898261273639314908213106094279316843576237728543732387525304414354063163097735084979059278564510826628101289663914218445029236973723431982754201621428198616511668396152328680131621197760625556044707460919801669006116095252060525700619069760809255088236086366573986164774870301521731444577837077159139616374789810231556238606093848285396167368562735419364891268492247924156520107858971027503842747830834420287165161062989699616989519710732807778893988743542582605149932908051714316746354153223364612706768958738062670)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
