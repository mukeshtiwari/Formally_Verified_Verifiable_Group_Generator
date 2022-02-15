From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo80:
  prime  508429271160140406256568047010062419414090263330368814125594551692682486508163099464127114562480408571644118805791884678929829504341060872838740115386877195944644351690503453125209181021589787080020217160491383922649663635888699325531445247559643->
  prime  600041508964096410849094553560806617457886449236032416928623276678081458548604830644855800023328893267576749024142038981484491395106487638696750199646033549929058067815091514358968592128664618472648382399951868958064225646469351315682355610707346124338407.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      600041508964096410849094553560806617457886449236032416928623276678081458548604830644855800023328893267576749024142038981484491395106487638696750199646033549929058067815091514358968592128664618472648382399951868958064225646469351315682355610707346124338407
      1180186789
      ((508429271160140406256568047010062419414090263330368814125594551692682486508163099464127114562480408571644118805791884678929829504341060872838740115386877195944644351690503453125209181021589787080020217160491383922649663635888699325531445247559643,1)::nil)
      343142959446120500385599370002175615611109862102352467123646631387851455669671509853094416574622043348377713041463457144344008392904575289362889943090250087674811933052048175851318122389830085104337146668965285494032127197226636232496346750646989984948785
      16774714029277895977761026944773044779531167969574065317586510973373738497480452915586292532574443856998431920135102331988016057517673521686691544004807828020194945479041164415972167593925867787455495218683395133291316745345223344650008542519284825045180
      0
      428892367100646797425879390469940200471589743884716455049673872076278391457166358141729632902444724140266437741024284396644232271243187353920012665187854127065067787731914223559850805688199774811550263601323576010212804674670598630125765943784180692771172)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.