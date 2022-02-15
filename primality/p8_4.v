From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo4:
  prime  19067066331166402133202658667185374869464541102853212856377014235282872071218325741032677134036373895026223568769501792724200357110544789576468628039510937435313492887349167765168337907142707977105662475904638668332039225636767427618154473695093960348298624715859861132769699157656952646715169680871252078071645378097038183636614035747774862786756741004470153984535264039980364748013481151070768690945731114822053487600833164769987772842691864593525605407765424703001753600304132853846773031513087215748412625127469889648378434687491208537029748670809277389745704189989579122166230597951969->
  prime  10769155332108108590441394425860968467773050673055906034133163148144707277312395251838220176012280121406391176535289690537799258497464139331947786991227935507214802036746359350438137923305830036301186589040843538428609082796548790188444119360883849180560456434016513007232857163041277482675314696432161263936860215450613425578303187783417168046294247442001694730015405323958167404383716971832874275631173950177469833389309826860012521379449018973956045804878141361245712417892781179572532883237557559956176422195838667384991853900005898322292154061844229080242687038869413792219711235717340059009.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      10769155332108108590441394425860968467773050673055906034133163148144707277312395251838220176012280121406391176535289690537799258497464139331947786991227935507214802036746359350438137923305830036301186589040843538428609082796548790188444119360883849180560456434016513007232857163041277482675314696432161263936860215450613425578303187783417168046294247442001694730015405323958167404383716971832874275631173950177469833389309826860012521379449018973956045804878141361245712417892781179572532883237557559956176422195838667384991853900005898322292154061844229080242687038869413792219711235717340059009
      564804
      ((19067066331166402133202658667185374869464541102853212856377014235282872071218325741032677134036373895026223568769501792724200357110544789576468628039510937435313492887349167765168337907142707977105662475904638668332039225636767427618154473695093960348298624715859861132769699157656952646715169680871252078071645378097038183636614035747774862786756741004470153984535264039980364748013481151070768690945731114822053487600833164769987772842691864593525605407765424703001753600304132853846773031513087215748412625127469889648378434687491208537029748670809277389745704189989579122166230597951969,1)::nil)
      5255207467651214460508823748116290236662412286072714204384202439855836281292513318842170556706926148794000559044947978018383125832386345627931981100560374263001827420548408294309970072905004489378547507243221362834067856003671208593185979171178585695870693742307339019357837410573422161486458523008044624235013045812217196270138061083255857747011486137317296048563290983098178274635832697419546998779783813932318723883246712638580007524430703247653997475200909145994689053744141564398550847367037136297102314182986810119795560179927016099705316606119524079043460727851548697613024125968648717887
      7517769503173232453618567022688072134576706768079590629753386995568072615352555709257237179863258289579907069021897476058741611119063073898774219147916488472759581359752376227498871667597848114344717380367457524351218351886591266892563256814512348341620012459421755074542443484740277713418684721313071795956991904355399656197000592748464635973287982464276031289412861918471950712315033008475883761424378743618225684197777050621052291518966179652200522449963617310339332813946457202460147401726181811228650212716690812635170822852057991303097242369237898567580648113879668662635355580007851470033
      0
      10340156044997170762738404824122924958716328295830699410747039703243758614127419951696480077911262181801692635594390221201998083391647363876476224949306620021696977517620634010894330677518767677761236581838596865426689390084968677139461130540030017210754365939568717069487234820768440536541152495952810393299459229647386630018321527909296749091188834561573156364196959129592613729191702790605334565389984843932910279270305361466865492122968179384363015347315200840197348142837085971744571701650540900573416280216800951385853509492184132914504947510091953581583883405308496831117856183000789968441)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.