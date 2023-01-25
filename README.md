# Coq Installation Instruction
See the file Coq_Installation.md.


# Formally Verified Verifiable Group Generation
Repo for verifiable generation of group generators. 

Run 'make' in _CoqProject directory to compute generators and 'make clean' 
to clean everything. 'make' will produce output shown below:

```
coq_makefile -f _CoqProject -o CoqMakefile
/Library/Developer/CommandLineTools/usr/bin/make --no-print-directory -f CoqMakefile 
COQDEP VFILES
COQC src/Sha256.v
Finished transaction in 0.047 secs (0.047u,0.s) (successful)
Finished transaction in 0.027 secs (0.027u,0.s) (successful)
Finished transaction in 0.057 secs (0.057u,0.s) (successful)
Finished transaction in 0.06 secs (0.06u,0.s) (successful)
COQC src/Bytestring.v
COQC src/Functions.v
COQC src/Fermat.v
COQC src/Domainpar.v
COQC src/Generator_1.v
Finished transaction in 51.48 secs (51.393u,0.088s) (successful)
     = genr.Valid
         138454106708200479055735335430888877165820506315681808529812588774891294266745965935843260905810124292112533861018873505541666292973867778507479111324012276358327291576815142910454131034197568218833096994765060449736987726137450505727390912803873697812682423871774182713509275008471752297521355610521695631738
     : genr.Tag
Finished transaction in 0.083 secs (0.083u,0.s) (successful)
     = true
     : bool
Finished transaction in 63.875 secs (63.792u,0.084s) (successful)
COQC src/Generator_2.v
Finished transaction in 51.361 secs (51.249u,0.078s) (successful)
     = genr.Valid
         102469831306215617781528906572847226693904307485739300130034645449135192789390308052087414564151228873441394591233561760912933102036228956601258949517417972024163761928741329990676466410461313046468961302321734855374139857073309659521504765942247678350704168525388693094421920249884964626193856064170107448094
     : genr.Tag
Finished transaction in 0.083 secs (0.083u,0.s) (successful)
     = true
     : bool
Finished transaction in 64.447 secs (63.943u,0.447s) (successful)
COQC src/Generator_3.v
Finished transaction in 51.082 secs (50.757u,0.313s) (successful)
     = genr.Valid
         88263658766223357461869144483248908802431230135321993360469791817434515043095308104988988885613316192808653647560362493809139862324204760674673830428720363991237057673925805011298607088991781235425078687556099730304327702471847840027357950827996311819356543334664389981253439309485633438223355769536120472886
     : genr.Tag
Finished transaction in 0.082 secs (0.082u,0.s) (successful)
     = true
     : bool
Finished transaction in 63.961 secs (63.544u,0.377s) (successful)
COQC src/Generator_4.v
Finished transaction in 416.781 secs (415.863u,0.883s) (successful)
     = genr.Valid
         16779584886618334955777146143805151742756109597848073032897659526710040302176218585670602669216587991633935024592787306349889100902129684576531517671064338120830768458737964024941626899266181419534731022507702381832220695652481201002313417792528591777912496057497664476810455186127730777145720725703338677122474655371704794416925100215075257492292453624627321349273605377338405654300066568869264460444035900045343943151207471750966197679881151399230919361519925420099999305148035925485570132525240424489924786140236333173248767301480930310664404386723788396232966052596334360090754073589039580595341483241910869439850
     : genr.Tag
Finished transaction in 0.323 secs (0.322u,0.001s) (successful)
     = true
     : bool
Finished transaction in 488.913 secs (488.178u,0.684s) (successful)
COQC src/Generator_5.v
Finished transaction in 413.334 secs (412.819u,0.517s) (successful)
     = genr.Valid
         7397663020529711748206327096495171056013349351297608836944581506776048299910727642018586975845411776739383886069050283668821048481626107184005913661785643385036737596310220141611324379597898168338084415315514945719018373740779993806917733907530535236684877616590789694426081749803454970748757282080960157265510732047192013417745603316937655021638539157108532588624321791236022232330371996545235390513598460611657625080679893233973467700124099006756332896043933323158170849561410748839052823646886645648103667336693441857536896810350359149834341507095181106437695481549438875894694601062306932502363245043364720122144
     : genr.Tag
Finished transaction in 0.322 secs (0.321u,0.001s) (successful)
     = true
     : bool
Finished transaction in 485.221 secs (484.627u,0.572s) (successful)
COQC src/Generator_6.v
Finished transaction in 417.792 secs (417.312u,0.484s) (successful)
     = genr.Valid
         17000091980252583428757806982638937856245893569533792216699813468191566634688128634050776893335947220947031435842901649795772466193775260976330643619179865466997471285306413279441538541328081656290102268160274755294414079471402076954782591372589274675093571750842213809016165031347652847970867397746301688224983069772073832490178172576260017477008355450432674058720853288885702484954444657071164813330071988886337091404537365227283011682049166650944586632286313933806893049897200661578473701190683228555851424768513111930423324951216677475160773117624980727524747216080485677785692737362530025677011447036821713540195
     : genr.Tag
Finished transaction in 0.32 secs (0.319u,0.s) (successful)
     = true
     : bool
Finished transaction in 495.599 secs (492.449u,2.686s) (successful)
COQC src/Generator_7.v
Finished transaction in 405.835 secs (405.245u,0.573s) (successful)
     = genr.Valid
         19505007897628087214258470741983733303993129606909771160933535007624517213905478669883399507508368338521633288116655756851871582957570975665522208849109692771478416189849647516623601185277096525404613089202268761028314488416628441521995648895965894383947550057509046815947139230214991308459417898812040648095362629463239815796837419841946171750790842682733367933794859041951588095792472952772187723597083481033010341517250868974535354067787123216189678903435534409554938991048675677096549033814900474097699209573422225276935134621669497733391117821219447658975257788692574807159800602790330174406663975472198869382895
     : genr.Tag
Finished transaction in 0.321 secs (0.32u,0.s) (successful)
     = true
     : bool
Finished transaction in 487.974 secs (487.221u,0.744s) (successful)
COQC src/Generator_8.v
Finished transaction in 410.604 secs (410.136u,0.47s) (successful)
     = genr.Valid
         30827113638062155707616269302531551119452708162605460531443522853399265094233230090236106474498610375088818881076937033907305380556951808525873535920749157105046303837536400957943237319508356497271947437278408440860865578536217653463247439380042444965023833640988275702519504511399551304181130117912437679538658396981265574932497402871300874163564126307709025599418598053644899380489152058952873644130199699802630122529043373387575803101121529968419553822680328682440160187107789650220640886602154339302225594385286571930972897568894793232717531235783992916417706832642343335576285265690498010286215611726811463907643
     : genr.Tag
Finished transaction in 0.321 secs (0.32u,0.001s) (successful)
     = true
     : bool
Finished transaction in 492.23 secs (491.645u,0.572s) (successful)
COQC src/Generator_9.v
Finished transaction in 405.737 secs (405.263u,0.476s) (successful)
     = genr.Valid
         16686255796188270469452539079851735482599464970095728845376833175044739122871243427199534360628114649000541180209352807279464906205869949161498141911328904969470630729113553098750547922591310704595028004997153534924113212998484168331949285437631969721323791545627286096124025385227828302583519400718140112333266887611575180549759041245944334854043622278279872761414635392575968374689231799056303753969701579382272273478745221727429281144967043356266411949754822424536441553774980090741788351724931604116702476051827592394461684697135364574264113516123841060846295360996479772006006264947007196630074887221145679917094
     : genr.Tag
Finished transaction in 0.32 secs (0.319u,0.s) (successful)
     = true
     : bool
Finished transaction in 488.461 secs (487.889u,0.573s) (successful)
COQC src/Generator_10.v
Finished transaction in 1405.595 secs (1403.775u,1.768s) (successful)
     = genr.Valid
         4287387900415874329539416709976769266459844797692946850755415061049853969319540434254000367372908561163305788123715331746181952931541577688878686605993064449816575775307400434277728575572844256140961810807167967475008910118050149173691595814863249029683210571233391135692095930504883097353773675029750447458648565889607516441739549398590419378630385561755690018707618481919584673291517946074890885633559908927469486214697952958610772113903851819749942559038101483475130120011622816821220963461713750348003626557633182785359819145157202281708787559969804326599766245155181476364432107381838847593953877465069492847591267620616534670348397979155312950958449441222674271271613478097938270718517831996227760019288273525360891505079303702445984462284560738211594759025717202810336102260198678784414582391155551558673657742352410700356853958784720389419009118656191948454137538595843290747283916485507903283505003679857626459847957
     : genr.Tag
Finished transaction in 0.741 secs (0.74u,0.s) (successful)
     = true
     : bool
Finished transaction in 1589.213 secs (1587.26u,1.901s) (successful)
COQC src/Generator_11.v
Finished transaction in 1404.323 secs (1402.608u,1.702s) (successful)
     = genr.Valid
         2815857067680651424347728195758246993191714291494761217484085964025213854469287867033561128449900900542462959417353120442070851755032021214983970103765146890716305532795232886202363258275657863077915583611655753362163656499220264084336345455815303397349442140403382571439497917600111644650834845541746126249643813462066176659367193455120967628954142480075772577080948417949213511906413145103570460433944152933121864621552213123281686253383669446690860954251216167486044861167685492759490205462427228551444743543073926251592860014822346807308315112641756207739293679496794973286349904658615276240292724715580842054385093926991100921590637938925586397890638618258362890968509121690608946555141641898453203613149349214698377732472649750557446967482753177687967393915835032845286305409022430101066346395788534519697210466132849239485539531264233037800600251881786274602063793159587693118604019689435792492692309345753911927683445
     : genr.Tag
Finished transaction in 0.739 secs (0.738u,0.s) (successful)
     = true
     : bool
Finished transaction in 1584.587 secs (1582.653u,1.892s) (successful)
COQC src/Generator_12.v
Finished transaction in 1417.487 secs (1415.836u,1.591s) (successful)
     = genr.Valid
         5142269046611298751053334471712018380952381659994149061069643310780863411117756830385169625171306902268731945265611175832982085711414921325430792621067001642054430322541316695452318115167970016625546426097672467620839422473921709026039725510992923909031023192174059668984872166791847785098121010517945765446961570007177822942898941331888153276962092525360573272974634978013864168046512739478574948414329466141821447534309755925230066981468451347043551719324995849899067726237010049836515585927730058820192474169847466483361570985526862054236113750881396542483192524341448209408531022129289703356623973794545446814225059247328981961060656844942121203760003864474654437004736370165730970677136513883966628087789535547496889264530799006158784007444380513118730444715144564668024953057128445187848415738918976578866440346949147032367775690198477927956647715787727147792313887321249651999990491718645651559760096877183540600160369
     : genr.Tag
Finished transaction in 0.736 secs (0.735u,0.s) (successful)
     = true
     : bool
Finished transaction in 1601.835 secs (1600.034u,1.772s) (successful)
```

