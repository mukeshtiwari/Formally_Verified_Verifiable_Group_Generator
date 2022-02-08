From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo35:
  prime  1340783292225013673983261560029238736951719860285278113312176356134467077858414884922814854006688750860184507839132084853894340196161269322066853453316445777163535971442761798826715469569578361690337528034109616787199006422242549972526600799125662216396359423968952022928793507533888655986271124166217410237661541727763697164903378844111->
  prime  17679568491279030305143286930545541985445378077721677202134357431989082888641058672592236664932197868842392920366795670883450769826582497280773529635430654017678385319444131142344705045812518591208951312200373270959955702626173298491521343178769420483924570480884185493666389467951814635788455723029282887004473978584608257555820712913589299.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      17679568491279030305143286930545541985445378077721677202134357431989082888641058672592236664932197868842392920366795670883450769826582497280773529635430654017678385319444131142344705045812518591208951312200373270959955702626173298491521343178769420483924570480884185493666389467951814635788455723029282887004473978584608257555820712913589299
      13186
      ((1340783292225013673983261560029238736951719860285278113312176356134467077858414884922814854006688750860184507839132084853894340196161269322066853453316445777163535971442761798826715469569578361690337528034109616787199006422242549972526600799125662216396359423968952022928793507533888655986271124166217410237661541727763697164903378844111,1)::nil)
      10219717499944810571082314793753234256778369204338603440653522607690485401993266455807761882255355638025482496196690676844642853258390688685331387780055245640078133877719267463722999499415369594641434282994637283693878694413021349974617656271284055438667586669731614124840244396700355166511233953457613495444431776988132632842723463286319328
      9226636763084894904442764907464168933975699940410711972133282587472154704117186184323888492817104198573738474355360887385088215092000476678589251460832400360090737998049102101131055719961293950917754436452673623347562688007148877714940722879191276055766924156439909721061228392777971102898123869869804751287362369246359081903477372138581879
      17586450330450096362220119381890386014097240864135266984723576562830834726637002345371717379907502785728672391411431406941398314295461734943151391561380558021653909138622707006854783457133075356608903986441988180646197094248525100494292948596121725504318583842450297992631036890768062764089370859609183542260801560045820548538636499696294028
      2507634305678249433496366119583350537533024372543803788230221059104217501882537916493397165798581369603253540519712067768985843999153085638944218234056016189927927028204414960097777639327379898469068946972966129808024243011288224749922316155860083036292287241593461112494559569616911051647915386080400365176655929869818320434207719270772472)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
