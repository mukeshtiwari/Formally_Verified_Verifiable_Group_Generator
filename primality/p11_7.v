From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo7:
  prime  8488307498165366845591126816364377400871276340878981621397893794291951600873843501788146978927301007155877469479239306580105795148605167555500856486186694762473802438904690833427331917221953332935087267191581927591732394130365637916777719265360094162518851072233380979216545523521638293786336900999269946097142443482820287087385891899801632404842545099591975327065148637305062794778151804326528478167934516799568873330870936135466935559395624546896468901617146320304285230207600544493863848042477851100371201761880943551282034806430913781430109366032705217265341656193032638473819460645161789346967872440439238698615322196288809447011423188138262469517909829588584749008050681509729708928351096730978160057940017092357612319704449062587867668262790560027346892445486838442688558177988053019288542205319832192818279499688977473124464309930016143649->
  prime  3282351486638309006651331846003373050556387055056385057115332965764408278889088952885541211105500513137838885015463785237059003103980439850421782588436639206580344715841113324121726732779912481841455193241122234985311949430468053244619487198890134535151609013578018978964032743011737092861298662395378020780274097424274441905407093458070192450940170648757983161391975188887132876600911485783596103588129381808587844029091186680706184279578703242581435375582271350913400479152618904822408734701169828277642254553638836633994991810972825371989386553621363978802867980876157544890314468516100105877917520472559648080732246476617742994633139158556929819285676881739008108640436638381689222482277433537523151964974560405102383863044111778533403554133249484402549112553255616099349384959093314681695890419349472175734390248595792006368835773558305152979609826131.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      3282351486638309006651331846003373050556387055056385057115332965764408278889088952885541211105500513137838885015463785237059003103980439850421782588436639206580344715841113324121726732779912481841455193241122234985311949430468053244619487198890134535151609013578018978964032743011737092861298662395378020780274097424274441905407093458070192450940170648757983161391975188887132876600911485783596103588129381808587844029091186680706184279578703242581435375582271350913400479152618904822408734701169828277642254553638836633994991810972825371989386553621363978802867980876157544890314468516100105877917520472559648080732246476617742994633139158556929819285676881739008108640436638381689222482277433537523151964974560405102383863044111778533403554133249484402549112553255616099349384959093314681695890419349472175734390248595792006368835773558305152979609826131
      386690926
      ((8488307498165366845591126816364377400871276340878981621397893794291951600873843501788146978927301007155877469479239306580105795148605167555500856486186694762473802438904690833427331917221953332935087267191581927591732394130365637916777719265360094162518851072233380979216545523521638293786336900999269946097142443482820287087385891899801632404842545099591975327065148637305062794778151804326528478167934516799568873330870936135466935559395624546896468901617146320304285230207600544493863848042477851100371201761880943551282034806430913781430109366032705217265341656193032638473819460645161789346967872440439238698615322196288809447011423188138262469517909829588584749008050681509729708928351096730978160057940017092357612319704449062587867668262790560027346892445486838442688558177988053019288542205319832192818279499688977473124464309930016143649,1)::nil)
      3150503982984375818446389260029784992601173589846202817310058692960121081124297555544215091116646310699980871649626077447134071533645157892234789538969969014781701127774988705923558312643812427967654940612802032281039808066173568938688327634733531047551833637576475650006743631911601250984802761205231739591697578979123687692058294554952873219303337862508361963870974561467635040735774128971393526657834212929097282480422071768288447340938047235668115347127377588758826711277527855252678253836659993805710118322144942891552396750559793095081934465907492110584007237531371110243347024636425958539748551593984686426363293076285796589074878211438628817746440853679132878903429520274347609569597780289158483894382663974269494785115586947965546200937801638574371800201634601264406762593335676129411743470610942626802548287911153825294115259740797900797180109280
      2964870972578692612276999436245842750909192780761093036555185674574484335844305557899780786100857003766622285334976761610561515152528140534010582815113878946172799254834736456247855650945840362114502420659688234753908505774506152470846059614643077425538660231344264041489852839510043457982691017853528031587415005625225579541911836893752961839812521998842333087316363241548250377764114403006781134913913507665488901224204546091459560324870979418256488241638534215610850094575143882976005104634314133543460935177053784900653348622318728473937176536588855609325701864919427624798632524706579930191418458112373551055726926230422211901240869052998175432214980233111243462557390567100596906200401395143991580780518129058802546342842907959915616440434519924859516187532759931365109110911473293646515912816497221271442369768248103245068503556391622884838744691845
      0
      974103082715264789177803004606151624979509926767752853838196608046918233271585747327141329197010516757320078372012248510314758175194919690259633303802876790677304202969487363139992184029151101715321247342521734452993308438841882030512848915645397011306998030489386913707269874813296882867761489471359125409852073143565330535985566633017501458271498844320263011860806200017440808274441307138333770813385335369356696199807582093549296538477709527900964891692934365181031458635563135916397422049840186056947713342421817839059983935019201472893670661876805936043510065374335734305425013118931608525031018692576025823807365559655052253776939940999460537813265333601170983505397679073826260174989675632895123607624921262284230218636028771006352603874545514982621582407359918070569308245189788106179569577906917474429038003954851199954981832366151578988951795458)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.