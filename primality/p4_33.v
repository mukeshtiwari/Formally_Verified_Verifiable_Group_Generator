From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo33:
  prime  332068970327037165770596506833141918717505776097738283083896867276375427827505094266177848072222096979233882961798191039762337767375561476725748128671625219378606747236404114233023222412023195772610014054169991490145964457595653652281998106230489644377194405073879488012554378188474962990693879684932687436155941243561762008231760165961084482684601->
  prime  10032135662550119815095491067936050506374567001688771270247608257286578050096756402875498968109901771839634838158885149502259986290183087773361576715298469502647088440759004694920192951514022133283520548207935127938209204270295100757701050298016871993237049198333958418272273049205827782554571275365237634257999868602197991638305004337100848405643940599.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      10032135662550119815095491067936050506374567001688771270247608257286578050096756402875498968109901771839634838158885149502259986290183087773361576715298469502647088440759004694920192951514022133283520548207935127938209204270295100757701050298016871993237049198333958418272273049205827782554571275365237634257999868602197991638305004337100848405643940599
      30211
      ((332068970327037165770596506833141918717505776097738283083896867276375427827505094266177848072222096979233882961798191039762337767375561476725748128671625219378606747236404114233023222412023195772610014054169991490145964457595653652281998106230489644377194405073879488012554378188474962990693879684932687436155941243561762008231760165961084482684601,1)::nil)
      7497774771513906843820018507983749292600244741519349750399691003534361827546621837229826193663787581733002697963036190513825392966586614946594586119663021830870262586197049150630637854954977339261269070379215413496441811789216233019751248542824578575209642212625830871247274439863209124395042161252636736255081236092250487828783988548484480231031722693
      5770513149932795754555617032939915160738081886355774817094613050028395579483255375412374581357736817588404669526119745502253437443854319924385114545904271733712933923977404836676638674363297592345394105807141739926401678507178216929259514951364433832436131569317182489187814280340354372073064798755343348330515816234956046931384684325934364756669514808
      2347417434321172259577993460489506575684230365979134228818502010931798348695721791400459651837561923159671441414985081535030945209748511168329138909869150162035246950238559865171073411351083981427846135386814220365407144332198882862225971793842606764725793780840342153072006998183198002444286152125861136024001446536815753396692769561028019413209667295
      5424362140587522257041563387944985530635822275006659234169635114913491983983592015229701740734473124541907962598703777178391481063027069429067779011963911235058168134303091408300581494392771141778951648257931015986531143944080834620172758063020131234443958104638836685845154639064505099642165895795478177074003110519905123241098427867670112884702247969)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.