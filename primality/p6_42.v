From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo42:
  prime  374321193299972937578193093534026229616279310077386642689457864874755297071629270420866477283610221086364593294415251986683261872895109061564947406831921426732184467668307149028161756732737443437936345913607425574157993260328694669149155273579720640499928370446533834543846619640761->
  prime  31672813449883910140241230416288095392751857542887993384525787778512544706418839087391196108875395247001653697013652131601217520113146758135256420468486283652126236900411467458986242905446668006446260401144600973935653319448381267307282625770013508501330102496270080719846494614831874483.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      31672813449883910140241230416288095392751857542887993384525787778512544706418839087391196108875395247001653697013652131601217520113146758135256420468486283652126236900411467458986242905446668006446260401144600973935653319448381267307282625770013508501330102496270080719846494614831874483
      84614
      ((374321193299972937578193093534026229616279310077386642689457864874755297071629270420866477283610221086364593294415251986683261872895109061564947406831921426732184467668307149028161756732737443437936345913607425574157993260328694669149155273579720640499928370446533834543846619640761,1)::nil)
      12386037117016069199354196388029424612444824232010817370926438407263026603319325042617231191757549382663189729437502228822338827192343199101574138961321370960105372742251509918566911618801361542337104896137801728840062457468272037481574973095581602418054345487726434379129642833330204835
      15540947250774679026808358441683892550644972245579013885614624557975301022679568467866645963732669171041047400374667076798221660451498305442710418793774821966773868153347756456339343129769923593852949961416146711132938729571176948100717788150838802235451192933581744321815084411814612884
      18014837463329156160603705214943659488106642305091862458518501332918057719521368389724803672188366392191466917403181691680738053462882609835018399131931356100348725407715390701266237260834886082173067364068202574928397695226591683021988379281323075490469393991792358815575699301535098100
      20073666666630729889718817213497191068302265437961761024236262807429927108884751990109813702015333157897525940507467758560595403557835252015022045408693465578061892159406476306415445037560278557700989960774868973138610139659444640564015112445795897938651990887871025601361019750624971712)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.