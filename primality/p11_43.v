From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo43:
  prime  167465208203205832386860786941542257557390158578149906667287462514753136436626065965426740728853054368785648597204694653450058144514727588747503332918288390668005037314932125962604087680659602815178282604226517094278962022195753684857375128837160092222653929640189486425575226876211661106461266936945355175663708235189818139707410304307740712550346862834650377330642071368066578831281043994512816966967385890600051850513645648354692418107872433148290000888030232120427910130960293279392526547151606817094572956274864043904987292580343144082782062812238007->
  prime  81164332958772150748518516096152801918351756709087767841819182160650645141066148138018300537962388718867249368655594314772613474690106592635634780473897545815429373559724998004674497517500860282129852574908885862150568554476078464889867151367318348756354416518100170979725890692256389338591856266653397108113380754870252927816895568852818124716223308242295902557314275023531898105480401999582252181114770621241428517858878282791166479365508481784452102297694203153270508024802894525856079827906530666658419778054092660128746805972338805922592969268294281194471614449.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      81164332958772150748518516096152801918351756709087767841819182160650645141066148138018300537962388718867249368655594314772613474690106592635634780473897545815429373559724998004674497517500860282129852574908885862150568554476078464889867151367318348756354416518100170979725890692256389338591856266653397108113380754870252927816895568852818124716223308242295902557314275023531898105480401999582252181114770621241428517858878282791166479365508481784452102297694203153270508024802894525856079827906530666658419778054092660128746805972338805922592969268294281194471614449
      484663852448
      ((167465208203205832386860786941542257557390158578149906667287462514753136436626065965426740728853054368785648597204694653450058144514727588747503332918288390668005037314932125962604087680659602815178282604226517094278962022195753684857375128837160092222653929640189486425575226876211661106461266936945355175663708235189818139707410304307740712550346862834650377330642071368066578831281043994512816966967385890600051850513645648354692418107872433148290000888030232120427910130960293279392526547151606817094572956274864043904987292580343144082782062812238007,1)::nil)
      22865962659490683090703925096663861789271037809441048689791736455971388682559635854826241316564907939566443841642931951676194630796931127554697622193293678750232756297534511361270546155460487841853563778856786505776537524369260732910821347769057386738981596022902459143733010846853765374254622821198528597032409882743872843334477875317129794701568296666361430001537342531355062417136382120334666845013362868200788478572022931620002158436664971234022029777135200775325073632494279674295285626804906028465880864445626066566042120023855724705782590424043045218821633286
      37709321816792652749342736378369912368762154899981161420325466201928722941753825747299323858566877021298424600536278337051519924415876252891973905888220016691994973944643508711241311946062087989392263584947674447718777510862827780130892772614173146982321255874284670918329421454248223694245106218085490400933189723978838914694296049797286284553327688073168898922594429008519967561103943416502072149064317825081773963174337671196901106570193838213734816096835951679359681118302842940361014133623292734205990605648175965269702936773965885241303720078159338075276164050
      0
      76931695163366502083390788180147344169480607266137524440970556648702516417068535067766993280731519789886094861308929024852636463015285048043348614926115646308268516011674650004314578935588744990319914817431981143374457525311699185889587995972583717575333226513196992785365143396526787220290328907893641601961569128701335739155756253722069933045564737204916700103319277604195021233719658091960852799863663768217999181927789700397521703510607273223069868592343717431949038590300959071474390722167063903245924487676202438358979004327125188032863662297631583670360894118)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
