From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo19:
  prime  7277927986062105083664028084482860042478255801842206410611889706315850519770670508923775419161392186553129353214309951830150459166961479242082460784436386188664387484479033098169124592772357335486041450901241304034011577430980352481297527605319792843410105727291889929411944714492196201126612230951365134990321787591952056125526432789597453461577079537613603315217338606269294933211413203719783230225914045412706069563138648587760005021405186767202259435278911607764798650906731572840688683733329270180629349389427654432493274582743241184822104215872558219899100749616818163693340513113866890267641069849680250259398555288419084082436575070851598171596775454556691925480480633608469643107872935033511331195674805001565170545240309->
  prime  3856515816390420986992899169742791673628887923349770439331955460259118663622320137314637204410268428517010819233437128995182087108899552158545559309986565550283749612925563806455033768713329973215369476500960557077190462788057040937019709497838115669380267744046154138475954208651698829407382808283280774110291592670674658924467452523745373809662001830345147487907146110609031827411609105556087703749680111825883328325951733273734592087689773518340870773158279693339370976050956159217801929225530197156658234337050428923513914784302512132052927467200479840150883420071825364528343957221720214202964942202675643854222539264794646810296929734471125812235225564824122521420089213047788775903573007580816304889698069479624468780638652591169.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      3856515816390420986992899169742791673628887923349770439331955460259118663622320137314637204410268428517010819233437128995182087108899552158545559309986565550283749612925563806455033768713329973215369476500960557077190462788057040937019709497838115669380267744046154138475954208651698829407382808283280774110291592670674658924467452523745373809662001830345147487907146110609031827411609105556087703749680111825883328325951733273734592087689773518340870773158279693339370976050956159217801929225530197156658234337050428923513914784302512132052927467200479840150883420071825364528343957221720214202964942202675643854222539264794646810296929734471125812235225564824122521420089213047788775903573007580816304889698069479624468780638652591169
      529892
      ((7277927986062105083664028084482860042478255801842206410611889706315850519770670508923775419161392186553129353214309951830150459166961479242082460784436386188664387484479033098169124592772357335486041450901241304034011577430980352481297527605319792843410105727291889929411944714492196201126612230951365134990321787591952056125526432789597453461577079537613603315217338606269294933211413203719783230225914045412706069563138648587760005021405186767202259435278911607764798650906731572840688683733329270180629349389427654432493274582743241184822104215872558219899100749616818163693340513113866890267641069849680250259398555288419084082436575070851598171596775454556691925480480633608469643107872935033511331195674805001565170545240309,1)::nil)
      3346885317870704428798111468062167422614700276112797268304963980120655458642353880878938196931011894064677865828152560858731847581210549728764117575067780026116617640555008673474659110692375439924665406098500330100529113074442040237547741943203985963780519451497877024589766290157702031440996955226268279050242774658214466446667648229057891088390432080551595516200530204542805648349517693767208732519624977640695604176057052437471089151557579731906740507724766539491391779858110685823956436969847786762048017844989953342614212866747889459174727844699439387255904362304350604227642425043992989485994514076221795264655203194863433619883354989656228355544575871749612382781024431197203584050504042002628426599587894340365106345711111930517
      633772045270187440908508837116740859154406166742670427661276307933552348820201579411795323155321498885156719145929991400352878233625792770610322375551458227620917002101627007395503780439183770975899183574103834008869702930294748147167243792739465030158764828498533992678436677500971133986284477777857037166928061083295732817788536206683905794394738735938559317680441494889852322990219955284917900615060495234824565890737906765712261135181048721160310694769622851215300922292030343542371667936278089273801659602368043979529751609963099050884250263547140310134912484689687496530626855889573978387888266804095433324583817154448703681224232409426959995039624426147073790245395553922119156182190655900622307393650187569195155936107992256662
      3357734117842766888646127540383198849220046424184565502825877359344480735341141045323061692305333501232729653092103459411679101043088734126199766518839793338812759948588260907122958471691381693620348499154795796060806602213673692571439173364953784634482678554197272568791943624774133673800476763719457975711784458514782377387046911699414189101297858064831609120116326531416744468493311757145409165870167663508747313151370036595772792106659097109017284794060621224854017604729145622402012998829086125813668650869587167409220054254688797238691592153812746716712767345607873025373502007571536641664540241285927760619504147441711090515705243812231253104173528310169042933762715101421974727619621505517365019688823475744041839618255065146793
      811507390231028874080849602457168047904797332726565149183897132128092922736642455139686921065863936859697574834435456966809813561141028423123994646105316886469864117171020882720455369840416880610662981768017466748855134932866900739185486688382703715542081902516214084312510350662120499602590475760523644123671657281133593148020795810382736410387226482251682686794624731475628732045839064479920232875569298385008769360377922218744833443641632753961216166759856929010627823035321799733945717551519749524042886715268709912082634773964708814882673875456330390485469577289775115043156154944349501471499480582769576943759624409466789837457798521791769771607009178789603944497540483668019988970099039839555251484809342074459801168248428796534)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
