From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo18:
  prime  14614607641333881026037888894837267131753844178506829569160380516924329379560674321073019072745394728208503074007424408454303494087303056841249622462727618018603941696144718896380031135162962276169812180795741988382141511478121881538612593197985612648433989389579603987254231162898361404523071166987759940032138356177108233089441483098808041737804160811196925308450217461198287251185756232348498064327043421950510476727614434237798512495288085309051536995321770263458778301->
  prime  47979368970968507483278315118065812327966392295751891368776275013082512630622972117104217374677883011696244753669280953889404768510972376324784773256405741775911672784018671367541975601573584522157797014227706086478972955000534973302163464070243263672406869085370683048188505982427896521739372360822118668402049357028004674246595986935745853387145215921897988865365041143446215422693913570444723491768790532166666217722203189292489491525567017280447400747925168980694605562998695223.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      47979368970968507483278315118065812327966392295751891368776275013082512630622972117104217374677883011696244753669280953889404768510972376324784773256405741775911672784018671367541975601573584522157797014227706086478972955000534973302163464070243263672406869085370683048188505982427896521739372360822118668402049357028004674246595986935745853387145215921897988865365041143446215422693913570444723491768790532166666217722203189292489491525567017280447400747925168980694605562998695223
      3282973457
      ((14614607641333881026037888894837267131753844178506829569160380516924329379560674321073019072745394728208503074007424408454303494087303056841249622462727618018603941696144718896380031135162962276169812180795741988382141511478121881538612593197985612648433989389579603987254231162898361404523071166987759940032138356177108233089441483098808041737804160811196925308450217461198287251185756232348498064327043421950510476727614434237798512495288085309051536995321770263458778301,1)::nil)
      44439053132761859995105543375652938526453385477394387014222145704559707263006680499044761050622107610187559576094608135574119845901824684751516191684529604726219331422036037212158942477592374264978446113792591184701289943955524851838104587211921667533751520748961856616174104720901535434692023292421887928570506932287013609525340355374597462415181441064480376894994097883702372334598878137454485853869480727582446912819970492287390784763491273937398721393502209167285855582081063929
      22211982233110648352489053485782297576202297370832006473355426847671749751697504112501078676148648382730332730566322339321129155546011476549744542272645584934409684905014232607661500079178508277869398144347480991411079490222621256571430682190534298125583485009486704838369615765805142146567767369671395280400147867533967618570604097722922351243851602632354835149738963889676192434147619374581737828530875026385461923615546067994769364079785405339048236161957253981640502422316458371
      37419623546367522028450927160854493501389000992800999416958570966691478057636190632053694535781650983809342306431849664478357652478853308135711450763958983103474638964522005802188377674367409609980295910317407481290211940770559603472115421817297239952297747969679902376996638905050820291139763210158593977853544055498884548268934650993025906130384178845127435614037851202670469263728835085882601416051904095918518518255948928765752100091096474624317815880522637575473724576757554042
      7733210361360201098813459275813779891626728070538335152987096205992116836647859209097380785442020116094133412213177829702918506144472985987740462222391484490322846144525324688668586351345386111789468413817368798172155380386121494428385025781575439296508397947655717097186221048595090803889302149432763131782153623352857542739412706385828935390619034173181785541882669588560421967361694653558865339163461199969381856899422259033225458971016397664119062195266453667762118677333429684)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.