From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo21:
  prime  126113690272946167255337122695739195727150352091002352976759845671113351522479326080652593979565059294696628572462902334909111527728619011793986702477943648869479365850384829478593759878117632120418131522412398447534047009937856824615853745445759810516246210726122134621942174111843615873315582419424931272477658888507159286361426581682297625148003987990705434689169186344579263393905417339573186719583280428594560448485022752662527659649514692904223557293952202290419584850978157039998397092209933315629638413926812925032874836276657895622180008730272946124190922250677455937863233359715785766089618147064062702047634346114404346867097777969435474317827303391824417020034396936177340172309670172041955893736576638536003852656793->
  prime  517248489001849682629379413467903269009467554256429011515091526267287023095106523766436345999280066429215596935654138060348807820047095198702971443403511637145806880715845067121042508333940931252348878415054663694095945602313019002639112985453284846453498229802856195843160626779018461607023311772033717634679228867900227764324016171397413885285208862752478986395688987812817651505642316647930553269801593433999933182704021836803923934624785534121633199246990556847177804878706696045237513401896375951090500627777453569658850889529497468183495708068613762086996655076697689166290855758008379974491018979897162837275728923079670392013959020762480972945914994691905291836864822608797699764041020510764176710374794757909133620188558630687433.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      517248489001849682629379413467903269009467554256429011515091526267287023095106523766436345999280066429215596935654138060348807820047095198702971443403511637145806880715845067121042508333940931252348878415054663694095945602313019002639112985453284846453498229802856195843160626779018461607023311772033717634679228867900227764324016171397413885285208862752478986395688987812817651505642316647930553269801593433999933182704021836803923934624785534121633199246990556847177804878706696045237513401896375951090500627777453569658850889529497468183495708068613762086996655076697689166290855758008379974491018979897162837275728923079670392013959020762480972945914994691905291836864822608797699764041020510764176710374794757909133620188558630687433
      4101445988
      ((126113690272946167255337122695739195727150352091002352976759845671113351522479326080652593979565059294696628572462902334909111527728619011793986702477943648869479365850384829478593759878117632120418131522412398447534047009937856824615853745445759810516246210726122134621942174111843615873315582419424931272477658888507159286361426581682297625148003987990705434689169186344579263393905417339573186719583280428594560448485022752662527659649514692904223557293952202290419584850978157039998397092209933315629638413926812925032874836276657895622180008730272946124190922250677455937863233359715785766089618147064062702047634346114404346867097777969435474317827303391824417020034396936177340172309670172041955893736576638536003852656793,1)::nil)
      371171454077052540462065345726892428652396157659484907146686324460345546583597009054418395206181705481162997329458001574350184703223040155279816191214588850763795965279191347640438391368121426810576291291581605017476946751252781633495194913598639986624028504134910677010165288746337535138099910748512372899624830360506065518700507621269222585344917220463982039230544939866200236165272998694587445291706621056805534490338148834732928988459747768111345390024803131928280200787371646111986818231272525766839986121339845848835942609411694091245367316314019562349291823784912675140886584500925520496095612860504622482540319353335011185987458738774021288880218876992571769621497616008928673449954654034800980182846394883024366915597925578200187
      451114036535827118620596923111125215904520745885351273651816337997046416223208539512448118633261813895895245694556497632969547791783653159211960761068666872311012771896814339606457880666867863213136126938518639448457710809878981140375816294671768808349841275717948617274222516186328440143917641652702689285933287613253835480637433328378332359617768604103550853377188759078584542550344607302279150059594286482832257103631385915222490594244392257934191213183006221226130011232419878677880670962132610533966958544736091104303106980831046805013756428931720163603740433565278969975271939423348531583894476925424292700381310527038934327756928101188180111778744381789628007193880397198879640391132196633940253187964615144183566637869217499893780
      0
      415027884185494309740858911411618436068643128885887515013157350707892775523905071865870777825162412987438322965706748321415788603661912498229133128648322031900672291846869837609291211651216295145899886070153861094141684499115030896672755455159405513597046640683412933442082519033202529186456068554777725584977273100109252913602419805350835875700260587099640688759284817087530535807804438836878867045076453394943988443377734872832909335510116244122454853374723520019867012090369279116176837160287091023777922781976757162484452083354076595946755817070168840803845457970189877060999904860086631716915873167261437024636194333429799484925500439766151082089889345888546008870394536077259961176232934190246431311819487251126758211768761930481384)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.