From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo12:
  prime  2371671384083359459572599607683850550431718219053552906639373329474873281714341883875284724614481690990883430543220666030487317765064282036436326202533643408455615147603513545529276354026662741735131160574518126026959419769454717304178413189682900880260026571368592867807879743780171721735580158198868048643032873201030398726720682584121624687774865914241537642578576062598084041361356363914353235576739251467422115725701948950517271009731202868088780669134015813114307161780794992361416229561255691739512483745099186411083705179679174856433964150227275228475363318363263286235588231976488811147605419453583089017509591338442750055043926001100559792292363827313029022410637046819981150379555129181951992276956840585775751197637882094125296506327242181182106998766841504489238854763472770699866220313139924067->
  prime  72815960812596021971111509888159714830264877677741859796852376202149418896787339397338631973878619608808061602008428398762445276178389841638406005746797287778186326306709457417014234804893837681919339712062194971203850404260150662374895837903482881693879595124308801029913026503600956226323485008642078797032976911575598095320092003998449255624694663297822928969826907289942288705980163123029488321613038812460423087035261515616255279733757413757568826117969292822284874650653525050312038291871526880400502252603253373558979166410209493712114565278259651008565260523208056277568607527547755594957712053306179749474138123989707015352099416118948927420756359303325914109289879270094167133749662199099211129341367100029509261716996725601179048458196468502546977416417196414932421300537307804792218968244092723981293753.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      72815960812596021971111509888159714830264877677741859796852376202149418896787339397338631973878619608808061602008428398762445276178389841638406005746797287778186326306709457417014234804893837681919339712062194971203850404260150662374895837903482881693879595124308801029913026503600956226323485008642078797032976911575598095320092003998449255624694663297822928969826907289942288705980163123029488321613038812460423087035261515616255279733757413757568826117969292822284874650653525050312038291871526880400502252603253373558979166410209493712114565278259651008565260523208056277568607527547755594957712053306179749474138123989707015352099416118948927420756359303325914109289879270094167133749662199099211129341367100029509261716996725601179048458196468502546977416417196414932421300537307804792218968244092723981293753
      30702382
      ((2371671384083359459572599607683850550431718219053552906639373329474873281714341883875284724614481690990883430543220666030487317765064282036436326202533643408455615147603513545529276354026662741735131160574518126026959419769454717304178413189682900880260026571368592867807879743780171721735580158198868048643032873201030398726720682584121624687774865914241537642578576062598084041361356363914353235576739251467422115725701948950517271009731202868088780669134015813114307161780794992361416229561255691739512483745099186411083705179679174856433964150227275228475363318363263286235588231976488811147605419453583089017509591338442750055043926001100559792292363827313029022410637046819981150379555129181951992276956840585775751197637882094125296506327242181182106998766841504489238854763472770699866220313139924067,1)::nil)
      41392686172201145546162550733506424610933008365448299468564610113257070396526347473419134998908907366736868422299005237014708571744006585774637228858158048771455402007715606124435076439981572915417120101473455994462505500730782487627143476742193654401990297813232664988440231965310891621296402162575036152972849979872010317398720728870913748737707003007455858806361141135733379816955136837350590045092128196957034551047747682071405662754919699143987099508736736954027630140688540501000712068561448798569734919178466064696734747263722572698160961970959454386537084823566709022468634810370517604621799275218629418413873167329865920047717802217439984526099144877555052527906913586565668315723617318908489144241895121303578781856595568239681651249517356277225339928458091271369861000451168988151929128752271420400472478
      60497321629697466429517747061063141266426846372075214507067451324204387415099241240966185484794176173108471483661251301927035354481868379278355682610114359488991383655684022498283475728073095898912204175678889081700350998264113042523592264110237830768813222638659966361375501073314839955622324070604638272968284158365826244054497246355668963918892161995735165356694469112674765471751744655453401488343709097291414166952329998825289695718180315271185051979920853623117986304073209048838485953888764192670205100005684578370352989113581973704471691864149070798117354104566761508806524071468223239616557622664566285945329145916345604146680745069023443362114336010111313742803427174276028172843552867985091273344689235055970161017226251234976322388000993548967041057403035998513467393370087753537809633684517206163567835
      0
      18455110377070731015367909513107333874798816210250143493568456228654443519241964459174209629295076298805973761796267753855087801250968598778112593208136261498049153440045856277293929719993260968096047981292233345771793547578696968171796657216523446971454372670275852127922035560992312688594711796976706472207867173331578543846065662882317236248071243029422862402448361450963429184347611547774780298696325213659228964070858528945175005214019029842036943855084365746863301888626949817648575203818687399103288416729937911164834895311769559565266038036040894075115744936069237372763327443305349340469473332680496016443184259968199476133904941199591495361370657291553779171413925536146974907226990165881243556136970654423252186635978015654533992760755917647817029487993408260552977238313297175044895493687976219700654456)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.