From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo26:
  prime  5529038248100166865427123221437141795909756427237090799322323042848849511417285176193395894038481194166659227719570536427253023419831580750591176795043450158725682345497523371089791629002754923177015315481652408960672557080676267176180517673168681240518888884672906698595668412184963612880559886881315996302019471239644069775379019121587693237767624106941712251700936677247820115108019->
  prime  14125028483383248190939806266682244708868858834906168627937939355242912997968227022336092297104213868256370162395959129840166871677620319511954528767120707077046341962360177458599719584821708999484256867197953595215852912580791382352472656008247068717524190843406866071971232627023162552988491485793137882426211737153288206754540235591100072390284687783931335374845194122726220729739705317533.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      14125028483383248190939806266682244708868858834906168627937939355242912997968227022336092297104213868256370162395959129840166871677620319511954528767120707077046341962360177458599719584821708999484256867197953595215852912580791382352472656008247068717524190843406866071971232627023162552988491485793137882426211737153288206754540235591100072390284687783931335374845194122726220729739705317533
      2554699
      ((5529038248100166865427123221437141795909756427237090799322323042848849511417285176193395894038481194166659227719570536427253023419831580750591176795043450158725682345497523371089791629002754923177015315481652408960672557080676267176180517673168681240518888884672906698595668412184963612880559886881315996302019471239644069775379019121587693237767624106941712251700936677247820115108019,1)::nil)
      12879596272592307575529820927171317514886654396818738599860820197795091049454451269471039276116098734751144538987889470430126550482713818311503467149118943676854147981028388232589549951730052790372745766738120157943835440118806432880193781648772100648236225805222003901329324395399717231807900741259655409618880901313336985339953410150130797155226036772509775878792344079666010341912957241040
      412825716159742439948349463061064126749987905352093930820062116324039014198802852494472368962530906746141924184316279483777126232430041146308950945187496670933594636185771600595202493521645671398062930830369665604058737142323584680057633934270393832855072263638712380137501961295481260615995139140088662985898007036312770907466596136092023598809680614182223312625521035854955242607192668203
      7032795575122155485886983222238662858469637507130778005794186436546778364117758784434785357982759002698090066722110596961947250243977797015255752237067394258711565213877683674080376585057799183481903903890759549763374186890340591211125553559305617022631447561513377546292064567833652542411737102628716263061567342419043988109496749668233290063129732791396873632622440335539295887239480334238
      1012389478818676513815114538815861292889060039013042910952465505675878856104722959564524373232582519015799729305313154180495166749535427209632366610126755184314907729776938276022605174678776894371353428084475500046260482926937589234682856021919261745086492285190550735731146674983798072521548385369405145792328431616139739810358982905913116060295562724758689007828338295859620869733564445322)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
