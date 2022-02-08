From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo4:
  prime  10354617462272889380106274437413999747489974091762630251597175311930001236718943382110633218321462107009220211167054989401514232250398863247469019534756205043596277706663854949134172464228276317824954589640800311153412257969091841810043424998957395578636985541274804759236473769301405692070169302239511424119804903481002123017396066749413337012098797347506479305318903932435048109868481572903303620612045787036682939564827201312466197571701924626849590665920412943871490983588506075581788417513133018696935138737401408864820074414806707688729071105593097244863801013009839763215551892976367->
  prime  86738414593323067938822918219487469288777550112239916414755695792520867339729930858057002794370167277525337735821229896448752799515889692067313018272472291822326688745293886843937848019932925863287630057138801075265547654783876973188586421923316325879588199564353206659905464160051244981653705228639999811250721984683030264885277460832502583875209514371983199929659198569192731370541475648468935484702290194893026748340850125351527433769813948586441013467533116470587524386803121022362625356204974716572784865921647713131035753373987721298569708989169806459069277653368510944260618894951489855739.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      86738414593323067938822918219487469288777550112239916414755695792520867339729930858057002794370167277525337735821229896448752799515889692067313018272472291822326688745293886843937848019932925863287630057138801075265547654783876973188586421923316325879588199564353206659905464160051244981653705228639999811250721984683030264885277460832502583875209514371983199929659198569192731370541475648468935484702290194893026748340850125351527433769813948586441013467533116470587524386803121022362625356204974716572784865921647713131035753373987721298569708989169806459069277653368510944260618894951489855739
      8376786
      ((10354617462272889380106274437413999747489974091762630251597175311930001236718943382110633218321462107009220211167054989401514232250398863247469019534756205043596277706663854949134172464228276317824954589640800311153412257969091841810043424998957395578636985541274804759236473769301405692070169302239511424119804903481002123017396066749413337012098797347506479305318903932435048109868481572903303620612045787036682939564827201312466197571701924626849590665920412943871490983588506075581788417513133018696935138737401408864820074414806707688729071105593097244863801013009839763215551892976367,1)::nil)
      27789844433994258233314574846979296853915677957173849195608408665695782364778713932860788977118826513201811252269850091593983513228297023658190122254058298109068879303116879603113650915390533885048599851020653736639896679757685364988878551604434835802479924885869913534426455996740444527595034306239259973649951534826747653429369989241167420358233631235689681148538047133887006210466427845346387913521681503616947208339799034191202238347359587829943815140002747879629317850038710620338438363152337041726024090087162737096443095414588270676295754447362711482689782410299996356790031658326791332651
      58649065425999900821013240997268213618287997529269704579488326997112243579603051236005257993753226287975459176117763573856897217125002412048345185346135556913106681783766889119946825754763798017682582903951242193085704620296327278273365373613773990007691078813485073497598778512178059777641265216599260722087899704285226450858071105443638224586563730191700193811650296135713324781541277393276322622735236148736981990895549523468068213637450569919988205773680297032840928974608577669705975472427022254830046397684807106949761675548409402489263195789055397431044703445283855026877883477796571044902
      45308602213144402306948961320353301373826870589258117462304582680080024223063665996929937583623432362461201380888965402940661979330693191396557614554306353800879275748155944987640607129110189968957836320714096609795739125816677387499145515695734094536553601329993191302898559259083520903590924991554690038260146254955261376912829864149906810028332756598368939752630732827231269223502520501602677496956906881283562623410192242635974382916009177025372507487584438913412577747332222490885428012460203749940628217700408875039671455057745346707187349484089996103739558481040193835365914930607217044700
      23718045330115372325639812846159126332118901674460622011538464194592077286683848556612057850286390370850039702976951190343126872369687067272211205702766696603144194836396478957296699407034139984021068087560858536213353135088122477397676371403062686296316122532513377108311802789731255682129586832428223832334585633065129304232998202819106770970480812045189008303630685743782319489909020743500866956881964045072262650907572197899989472153757366895101785602796111548880282831088777517780865213394541205013792296607196968236569066658747855082587642340476947918287249867392801277129664877766833837977)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
