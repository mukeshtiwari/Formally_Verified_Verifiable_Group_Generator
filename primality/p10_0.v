From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo0:
  prime  300050801049466333477722963796263901544645716193436751695826895931821771730185499627168957319163667186444629608175678802674611965769109529556467082411722278966360868871695745344514472946609225174848220369135212852405427535058592246816545977198728560592185821465426568721846970730136640502183388337655805005787646270652557389724770524812127567373571848221217166632064277396461296755431346422026612492626110154874890000977836925055406160819773205023852062974053363679648085973540444485801340060949909020907827679044405859821024714157186300451888614025283537802756584498615726635769534205711433133319920104746364216208050655366453892527936030125077864417815745794551593396426661005672528828321929303125525794562437902146654462910039558950246568249301623257640099351188399809871623624587864404907800219711318752119805016430211414585414807608345403685835463883470464631676642458253990910876749320026494117836813422584076860371->
  prime  4513964250988171520838864267350994134837650154414062492512019822398326733908910656391129793909498209152873007825394911907436862413030483762647490787801949964769932911305790792962875731008789183530416627233270142151587251837421461761108117680977672465548843498125877299851465827664175619714846894151693930507069350495697073371019447775273647123568014884639991054812774989152363748388709175572968358339067201169937845174710578700533530283372668096378830435381658802299872207718329871876112077738218875676204449347654560165390372681461099395589328636274158827149234601243459044109291889626132973973357884228717372408691094133268341962920871675643244412635534978197661109720995606687609079132908142098068856423865108921860732767012185253336939254458455604130003947574796774992226936935075677853934049557268608015007290772136874501757251157127285543588534314404615327565151686030878190481051513826068602295357737714861646418039263.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      4513964250988171520838864267350994134837650154414062492512019822398326733908910656391129793909498209152873007825394911907436862413030483762647490787801949964769932911305790792962875731008789183530416627233270142151587251837421461761108117680977672465548843498125877299851465827664175619714846894151693930507069350495697073371019447775273647123568014884639991054812774989152363748388709175572968358339067201169937845174710578700533530283372668096378830435381658802299872207718329871876112077738218875676204449347654560165390372681461099395589328636274158827149234601243459044109291889626132973973357884228717372408691094133268341962920871675643244412635534978197661109720995606687609079132908142098068856423865108921860732767012185253336939254458455604130003947574796774992226936935075677853934049557268608015007290772136874501757251157127285543588534314404615327565151686030878190481051513826068602295357737714861646418039263
      15044
      ((300050801049466333477722963796263901544645716193436751695826895931821771730185499627168957319163667186444629608175678802674611965769109529556467082411722278966360868871695745344514472946609225174848220369135212852405427535058592246816545977198728560592185821465426568721846970730136640502183388337655805005787646270652557389724770524812127567373571848221217166632064277396461296755431346422026612492626110154874890000977836925055406160819773205023852062974053363679648085973540444485801340060949909020907827679044405859821024714157186300451888614025283537802756584498615726635769534205711433133319920104746364216208050655366453892527936030125077864417815745794551593396426661005672528828321929303125525794562437902146654462910039558950246568249301623257640099351188399809871623624587864404907800219711318752119805016430211414585414807608345403685835463883470464631676642458253990910876749320026494117836813422584076860371,1)::nil)
      883423231150826837001066922146374868469863058324686133724280490016314745416708626793795567186000900219378342531998589636020560346158520059653794249890851565672409878041288615404025944880821922871906276709344720042978494011453555955347565990613755267366587379407745587459501522275529068566501915214614639496111249628107965686386499568753903410529285695807833617188788263540073387329915970232059866604062275426712473306074792514755089077952770908585467458871091107952842479100719655924964142272870080261764712399280247473547032575862267681426670294263328049550578589818534960109843140886731378128191563361703592031789542514935885872749615470777477862920919068362433218145613393209342379501537666676553484376558745102849348970185373608787298150042702744237622649290013543101575403620094771497780094918330396308772116275363007684365855358248560731474881273712048406603946479786152301027686560588939051435244839285748059385146183
      3547194103812931444319237938800122615561173492052349620085230881145091182213596573484290880652959216813232833473953881887170278749646027409209635288413614209601831474096052076158821863892277397712994007042577334824657578351114155196496504654694066026022310286052247813686450626666456106922640182632188307867952573035001761815886141075745052244170457059050384686103103757633527288002250493260634242452955838383304851907211802175012826376026489352332656518561922851293437661736547240135674605402179129906319442348261693672553720634241521066114011332696713189221313675603440365507374019216511760706728048411823081074251903212417718694655851280307003351386641383260320762347203595767045986875505541210140996456632596256566682358185041759788172207721523350259453420577919633412666723699552255036550479466351587973570446278301990950666021887785004811796643132851342308051675716833417133734667718402968901852696432095725649001558919
      0
      4418041757039307896500276298702599055484962531952301472250544862279696057767705649886521803703308181255224499006999948943892650888254772170420102704913084248803882035173413935156215572347970891188285642867302521915798748681999273098979277782863161130651954781455746351700504942386297703225858330032605703025077118942698325654771958590421652599116637391213220525239224513396056644457951255139396801782332334174194201220060329413783938820796712836918473540280214666337048315796728218241472279196014511409008637919725627044585091076344419208637489519267648874030075326905696634334915266578447608784047446639706451015076876494029115337892493304498035532481959299446145336239700945824449073537590953279989205715727954799895623023714220514629023932102652465186686520741171158526463428307823841766851436042264967056938648462084843005357129178678795032795187951714915450149625270529438752742852518528320870210454237947684385457535337)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.