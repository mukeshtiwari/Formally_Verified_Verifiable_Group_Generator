From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo36:
  prime  7693668437232894021284445260710265832821983349411423089970083124182836374717623040682700242763791743090844190020898972599539454046635810445035912190303870277691273771548167383947178624336127324858345231204473470494840060238465520880087883089311512614839981800736329165816712911613930974979586724015502752780012530109497352976200069->
  prime  1340783292225013673983261560029238736951719860285278113312176356134467077858414884922814854006688750860184507839132084853894340196161269322066853453316445777163535971442761798826715469569578361690337528034109616787199006422242549972526600799125662216396359423968952022928793507533888655986271124166217410237661541727763697164903378844111.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1340783292225013673983261560029238736951719860285278113312176356134467077858414884922814854006688750860184507839132084853894340196161269322066853453316445777163535971442761798826715469569578361690337528034109616787199006422242549972526600799125662216396359423968952022928793507533888655986271124166217410237661541727763697164903378844111
      174271
      ((7693668437232894021284445260710265832821983349411423089970083124182836374717623040682700242763791743090844190020898972599539454046635810445035912190303870277691273771548167383947178624336127324858345231204473470494840060238465520880087883089311512614839981800736329165816712911613930974979586724015502752780012530109497352976200069,1)::nil)
      519849748850560542506302550114883852688216823690025892935816780492292569177272214518411786392827449002430141563753443848541924731523504978058233972017895320746479002906755160251869100631986492830863180604239587718776144658090793756699533095545741037304183627056299287995316184934815643337071881458623321250316002449667131224885228058640
      237285714386181765332719964336360840145967447206485122795353190810495752158879420573827686513831381179693937124471481876291606231014455268379787580917980735673328668481469793548584190725964106203937042508723766090541169218487860650658225978581325660918139340523562792750073816988274397888453493247654965331562334896591676301545016420935
      744467950725724508905652799295502844664098537598998708947513259610064101574747318442906967639453694444330161377227240099568302400630923858510486297698552550987049032176886095388566314678748953955812357967860548934886847185846653609417719289452701188453329183993333760890755792295067770493149476559706726479164368716048372670746966797144
      1314965683041876166322093956041783535085791894808724918784058410598315503451339610965295160638742083729867644765969578018511666547122850377987905923529977144746229523098198189842935983782422835378970830004619535226205702245221227256589840050950820910794059445164164637812910996560718670653808354976106716210781361883387666043470846753392)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.