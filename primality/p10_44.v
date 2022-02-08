From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo44:
  prime  2497751933419655035553241868543560928741669419306299453903573150846171940483671536904157512794843984938498524081813851628125759150439756052949698638332911914083646418855892038129250483416282538158772113939290760453892584513364090180051658981138761694454708265176662551220667379709171955677581953873328109545779004563701250023237686449889570783050876849757613714054185134226082131875960683493520191370387829200549992811502512518749253505226698406666772009163710924912800529332137600044299977443449987507333032097119658615916720679084734555463968172818961->
  prime  404505930113446293697776414126892605287855879117816583960775864633235853417449638058554500882099393672819958978001589643471710442895417613263097795080738418662018370240874003790955857288300124489736826308240260073986996276770287676479006068677460178893551094128830146845084640809650315569330880665019439210026110614021401006094856946255924894649358513422001120488471782912555965071950154415749654814632300638457498977077622994629560696584432581909394576124880532181835124116006046624387258690604920217720487411098790570715887336864657816031511167312208691211.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      404505930113446293697776414126892605287855879117816583960775864633235853417449638058554500882099393672819958978001589643471710442895417613263097795080738418662018370240874003790955857288300124489736826308240260073986996276770287676479006068677460178893551094128830146845084640809650315569330880665019439210026110614021401006094856946255924894649358513422001120488471782912555965071950154415749654814632300638457498977077622994629560696584432581909394576124880532181835124116006046624387258690604920217720487411098790570715887336864657816031511167312208691211
      161948
      ((2497751933419655035553241868543560928741669419306299453903573150846171940483671536904157512794843984938498524081813851628125759150439756052949698638332911914083646418855892038129250483416282538158772113939290760453892584513364090180051658981138761694454708265176662551220667379709171955677581953873328109545779004563701250023237686449889570783050876849757613714054185134226082131875960683493520191370387829200549992811502512518749253505226698406666772009163710924912800529332137600044299977443449987507333032097119658615916720679084734555463968172818961,1)::nil)
      192739326965807929856955950028807452233605892794472449890351671718287944321519818256444796044800166871357498698061217691495575715403303145226766929486007496122148799993857596406914458671602329043834292635697536396639762839060018023967978773049621254599462958678695268596764886487259938434806902735565353293025642224284492169671340886903111403605627854348269257971830412465960986161816145456072766367998538605620858563892748601356685007594320518228103590565797470905392135051482599993086666310695203896433437192020780606383047653103593349752472408366442899623
      141402963479195320591881421515453438187475834228786714637162059467960282140680935583960128516367533104044996217791886643132628660229542039248001206835776975951207789809894289969444752066193001372446174285724022311343834350722020250775045402252088548206253256112885120445282050514350056122169279851144547569437566584470481513031803050359351825452206075858216384342965591511466794364753474826755793610218952721058034958192032695223881735598912213066612335423269714700417554137145727740946023734448962275812423063471667184336571866773458117433561343438070796379
      150093945294598614847635332606098419899416742170431291315623476132040904974217096108427770809574580951620619292357756336491854121478514663410303483526988890407137953180277777181401971096270193387605316626935375038635766749184370994622938390468482350346160467177673262835847807728017785734078640718012846233415532131718687480598302506985986509965544494709843982804163787183398327444031833954978844728504163803091028518179066608141191629671010945003676916124993294563500054952093683551155483853109504925817410744400483719886180475329732331436323535088061101566
      25981584433615968116440991185737725902819855606886349839196448083782100747085175990391333311524310988174963127446043770480831422898300659725752204949782369036943085370443362269690875671980427467195216292927796992833292047607521675315208380809403029953785765496955505890388676472404170892910917259572368723033071715563936059225511561135400392566760246450980188319905531927136845698922072990154785896318974413631456728674863542281870558210722060164052489628331160346617913722215529347463544423110152495920383020015553297698390067029944639955761997203143388075)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
