From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo14:
  prime  27896268830648238702487999831605625496835416269044490616732969087421782491476467103875883676882714202455221433874103133554478538385750613792428341249246974715854892267287262883282582749690997192505004403631084115249731214490675512004399222249200192952115280653277323871617108445552694908100771908974107564940993818968533632033235969415020462269290691491817060991497783205527695623043641110113525472799509737112619898037724177679507253240164397284168686504929212472535888015955194489857492370201798818221546320077483346370096924064499050515754387795102122171053089858021697723151903199219994030165915217018342721916902548950082323353922984255699443399672883155711078097392698045051632617564422105635785955383786007568388488981571816585696384929968665854162031240356473951815263->
  prime  30273644652933742901191432153254720112926724114325000196072186178990041638965074583402394235594012872216860314911721950802258308384061052601046669347190300395089477896090018000721691016785163355244665888917332365719543808051999860488438132767721531795880449101110923966604061661499586673558935892600698959840395194208670005222372405200507336104804182802132694563315207285869176899430666292808992546043003507744973533565358525897462330489254117986902114206678738372305946914365612565578571545565501135843406447014288971686677434218347005044893647336065731689687827732216573402274133475176956788532491076678979083212970950803859621734247993878113083127278694505576905361349906230718249996371509688693657312425894747845728869743751941475236391584254443998673679194752364161471491721499.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      30273644652933742901191432153254720112926724114325000196072186178990041638965074583402394235594012872216860314911721950802258308384061052601046669347190300395089477896090018000721691016785163355244665888917332365719543808051999860488438132767721531795880449101110923966604061661499586673558935892600698959840395194208670005222372405200507336104804182802132694563315207285869176899430666292808992546043003507744973533565358525897462330489254117986902114206678738372305946914365612565578571545565501135843406447014288971686677434218347005044893647336065731689687827732216573402274133475176956788532491076678979083212970950803859621734247993878113083127278694505576905361349906230718249996371509688693657312425894747845728869743751941475236391584254443998673679194752364161471491721499
      1085222
      ((27896268830648238702487999831605625496835416269044490616732969087421782491476467103875883676882714202455221433874103133554478538385750613792428341249246974715854892267287262883282582749690997192505004403631084115249731214490675512004399222249200192952115280653277323871617108445552694908100771908974107564940993818968533632033235969415020462269290691491817060991497783205527695623043641110113525472799509737112619898037724177679507253240164397284168686504929212472535888015955194489857492370201798818221546320077483346370096924064499050515754387795102122171053089858021697723151903199219994030165915217018342721916902548950082323353922984255699443399672883155711078097392698045051632617564422105635785955383786007568388488981571816585696384929968665854162031240356473951815263,1)::nil)
      19329142067176032890731388452335130837778229686066379588825606649675794225566132454923285263781185452106106659174380229073625625382642488852724751880033943560622268895630134229418559302405794870430226436404900224849849116006320169567481493979972448312490515746845301724155559956601988261815393311467017898250934047082043808750456888292290972183900932490300950504728682038886286199090320717741597846642979937773898107735770392062741618025265497989618219168199417458722536678686234123228908584196075642241276241063113078787555412606361121840383533800725499574859281871119126341056528514586076164837372408749332474539932347026851670205090710476318914967780417302578273970315928055798693776890488916444809218251659674642845318936669143170011533878555705335830968262619669715732283477311
      25534325617051731900201201120069649232424603277426885254392609599108427286817226715040860192513221236675675487989992849249334117828827551863424629978457184765094213602468084176725958561377491051397042059991086911071537971600747832439900091960032648132604071588082059397620758293960790959435373754851531776547942335584578106461243333190210632384958534437555416233279725950048112722392191942895306474797983578549000109006628443116698215237788876551299312805193202517673110023637768809137507361959247716130898828956726892254021116607578114992639566759076075483272443427498561403372785132818008618091982426009240357701148166148740824931215666698692793145025102611484825880935268092099072407103171184831464477104348958232714694372222260691296545750709941955377883604138756856759143354747
      0
      331229577752498446474352615561081323876482973605643685380915498856416045676205394595157943106376417630693928366352087618662099415910122727480043249556106893224542383299907863974315777867884281602274094315738598072388712118252226101202575704801443207336137276204432384795856263917292228635976975053583738801872603641430730982183713247651249025148599336259426143898648943813142171046946552957963608466053129721927447333754917342413949278377219296114373063542649761712739323415484076332840189917243468955851552964555384637154124536113225999707205467419944834969237790818530882162135472113914884058184204536527623541056298099271010833452925049905351962132778845353522622923690796018928713326512356085783397425139460585896128341377974603753794669308884340019922241825109872471119726385)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.