From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo6:
  prime  5996496656161807515342051173371233819025911407347559008943092921970150598276085655527189634641006196165924793093687235100728176543613945146330730218281748505224199697299509843214517134024254726527838695154131874941720349883939996248491728248662604615636055279100621121575030492559079401457863139223147822322631492745355009435014834722058589448116497825087185353382280754540439712920972937142938861962784007699566958286825156251063684949178521758481493303377729660913068766799259648869971274755614332266972851643470980451213633475411350275748316445151169631904223518725941003798657938937228188220456940994365902407611406355438564621900461940445393312239885564546613492705829366690660782503520597726921427506219515217027852919344796824294841373723676658733846517323233541180070179926215180625883564937524990246479414729252224207134454315464751808672228450495123->
  prime  79578939807367701379818949641032233706603719883483029269821068079330706837714131030589635524963839113003781063333498289459825221218974227808832716669092593213167771931776833017272610046598868709059779977627212970243146277030905870418568648282575276382408613513026497752859159696266702707363288595114519126474468240703340677665349243712956156046923535231105800976304335102688549868253871821416304417948253991111552662793667048653483562766268923756392434822868144245778058324522922123904694888413002281588226395049797393137325119692733896563971681915945402057580161163638954328160986446980003428459025947693614885181473171215646613983781315865707189677153806835416844205155292678806958755407230892247799900458520498517826661825922660135469612434129720094410658626945039122560730363502768298334046980290708321008923657039124335131481076579123728103038066489893757005222847.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      79578939807367701379818949641032233706603719883483029269821068079330706837714131030589635524963839113003781063333498289459825221218974227808832716669092593213167771931776833017272610046598868709059779977627212970243146277030905870418568648282575276382408613513026497752859159696266702707363288595114519126474468240703340677665349243712956156046923535231105800976304335102688549868253871821416304417948253991111552662793667048653483562766268923756392434822868144245778058324522922123904694888413002281588226395049797393137325119692733896563971681915945402057580161163638954328160986446980003428459025947693614885181473171215646613983781315865707189677153806835416844205155292678806958755407230892247799900458520498517826661825922660135469612434129720094410658626945039122560730363502768298334046980290708321008923657039124335131481076579123728103038066489893757005222847
      13270905392
      ((5996496656161807515342051173371233819025911407347559008943092921970150598276085655527189634641006196165924793093687235100728176543613945146330730218281748505224199697299509843214517134024254726527838695154131874941720349883939996248491728248662604615636055279100621121575030492559079401457863139223147822322631492745355009435014834722058589448116497825087185353382280754540439712920972937142938861962784007699566958286825156251063684949178521758481493303377729660913068766799259648869971274755614332266972851643470980451213633475411350275748316445151169631904223518725941003798657938937228188220456940994365902407611406355438564621900461940445393312239885564546613492705829366690660782503520597726921427506219515217027852919344796824294841373723676658733846517323233541180070179926215180625883564937524990246479414729252224207134454315464751808672228450495123,1)::nil)
      67373067533888584616781232126224825529731312870940679376430023841379505751820821535980978270905689468473609608928222556803545119557387137382091790804039223989897073743517619123643653797669064935108145038560254856116306560343605167166581652145862679039658510189381941386497290500753819007811371118947808285337302916740981102493255779767170731131673636391306341296501771441152181680819475564997197031146582053751837858109232304127120407205618283675007528136347469510908256890709585033014551038030450467169992496773072513740370030970434140464568234894914068578551076872959247558485728600549456269300776375159383092438019190891982656485373851898349766231497603823376389023487851315893233006719750931373843400158603163782513210625202996788073150159386825054520123400409829602885272061536600376654730885727235988484670903315108699087624815049800159362696022346839599622355156
      55085958204849427881219525072832653998003088026416909134962403034057070569780714831206526979657573308853057287098331835516778151351259272467020676184094814955659472813353012792774160903026282406519198544641199462560993806280413665112320066023432046628522572385310246883451089916451039719325831768858733199787613267166212949814056408891196119477915640519931984472415171396972962393020980755146730741379692875501526181457582009157045628390356154861089492654932441874800700681387963586837544804523695616601450706290261388805293477354960102846090555310910912875767145348968993513129934971308944094974835111428161881121913975121394648904137109693224411562657495659211869950010210615526529978336941965581935545526922844579882626375312539598258879595079210137128650272686354452133076744949337371515471309610716173713695756624571894848188785275322042029751174859057292997822966
      0
      58104408983719158701649080511261863709355641994580806826286140212906998853654467347522662167519218608191072665450571455787228965666341714519532227272372620311183191346412977587288292367937278337609395142682411542065874144676044642325317837307442880573467582043195494733367887667879948960655572384721588000326788801259297175403455963107978170313325792567202283705099241555740594021771765584923377135555346985277953657573422055033235378586744143521791512812979835527289221955702375044639868936132537539784423816545310336067612606346553808526815607886747965640230969761036938330589866101427922821374677297052320870547839605313920508292520309467730340715957891041153102055672578497093272051627257082500197424446471013985850018914508614496341956778058778176559418501916976285728733395962616421863079119117538454208276263756147536327093384818925885296899711610179126083934831)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.