From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo3:
  prime  166970519984996966905585648135401893674665968392426774076300777904457329145362383388850626497657744105798780234537552010234457920145200761677464811830080465804952269965962126918318928692512653094579245480367129023949033210147462751317556033742211974560339688824323765851498000833597188878964089027800285660647567979616424739503216774713974226942799604119522734080281382371916935524303072426922985033944061674833518673384701769002263276688885000109144743940763444132619265485365141394551150024146436123430103634396504229108563064137346973908459965497101435603512793728364842321143->
  prime  87055928826637753486906310954828384063594678487579600375959464222361051458390495306605793264337433034283023750579409964710633632072726321715487243396800332992140055468879186204014474003292829511797847287240565889247774822907094020551755158551746736098494326954185359542887941246032513612897298339559631679692314712698817633857489197212464678913102900139261906998815080032951915780563096725555310906626691008282594719438998719880591972202986966056469358090825923525664104807727733481240758516458878363777892263261867239236773571807457764858255187967570463552406225811494655091074257239097083.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      87055928826637753486906310954828384063594678487579600375959464222361051458390495306605793264337433034283023750579409964710633632072726321715487243396800332992140055468879186204014474003292829511797847287240565889247774822907094020551755158551746736098494326954185359542887941246032513612897298339559631679692314712698817633857489197212464678913102900139261906998815080032951915780563096725555310906626691008282594719438998719880591972202986966056469358090825923525664104807727733481240758516458878363777892263261867239236773571807457764858255187967570463552406225811494655091074257239097083
      521385025539
      ((166970519984996966905585648135401893674665968392426774076300777904457329145362383388850626497657744105798780234537552010234457920145200761677464811830080465804952269965962126918318928692512653094579245480367129023949033210147462751317556033742211974560339688824323765851498000833597188878964089027800285660647567979616424739503216774713974226942799604119522734080281382371916935524303072426922985033944061674833518673384701769002263276688885000109144743940763444132619265485365141394551150024146436123430103634396504229108563064137346973908459965497101435603512793728364842321143,1)::nil)
      71989418754881476586851115309064530817977997756951705640982536036680024720247525514350884731279503820111091562124313277372817651020601045682616178215349337503424381459034498016305813173820477157917024842676590528418569549098115981798632900287876927752583517231779792026394870410876743282660250301243471831655523100924507024397134148751715145587497643702936310391656577819854301770785661138860546611570163180156227719347501327461276958511497970292065917459290005632060789951731406655668212516806594633961605375893766747744185878991013940674193362348213062357941099510287468347334462172530992
      46618590777218040417702856156062881006000972106809339987934646261433324299715682766693057773945375543806378022184862113106690170888790254257378980484257224901493192359826108036770182441731802383020875216539680651831959879413301732717087833476680422523102946420338258187558545774637530873865014662378932184947039459397438107020687292420755718159583469642308912746031177918044652120285308809489705977923949884755585818764052191876772808981136243587017586077804193429833282888329106399769204260226085270979041010310574822917616311222566669750824877221458503613433649280038671101318548426803572
      30541787961312973345500217201897490720502107967202520002368704879257178144229924247730288436364073435424474528647500531004583306128478514566665940487472367204306219880790395401652331707122222989714393630516007448488794042287895137141566637191856561939562699112617193653688869872059689239320305170897386387569411792661616395630814674139950966250302919284189154759049290455849264963985868633257618289187737377852920758307182921308934503143476591087931147332078228078080730289801022646613764452881093075186174211184609580109628459805572583974179458372986580921890516542744066389845758430535280
      24122590066342522929439793887761823867013443971588242912478324205451571842548588885862798909768330324759871695005260570147946107880516220626744307284378586754556559064878938597164984841036586233203771449737582038106471629341567841007554196628623201453657125874044623507585577379345983383741411941196119378398914633842024631996702306483681201614678252006340663020010701828054141223759734059691047346138866001592231356796553223787032113706529870647256891323265782968297933378210050572518421321710247838182512556142824079123991467217716806921949332841365586105990037920921038426517318976889770)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.