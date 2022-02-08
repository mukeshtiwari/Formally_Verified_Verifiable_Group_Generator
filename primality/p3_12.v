From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo12:
  prime  2101460028687299691565021880390078607360765232903932657646079862933431776295587474661434077342935932577926037828117497747081955838865726217676864344799721840050457595801606311306094366943654009661311937339000569323400839->
  prime  1002205200821231408604583019954951998557815186458981619825334301351720015001352326953309864391542232669806128774541105530707533590502807430273008914683009312950727114683255573455044659732298020875999527807696463526129325131859.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1002205200821231408604583019954951998557815186458981619825334301351720015001352326953309864391542232669806128774541105530707533590502807430273008914683009312950727114683255573455044659732298020875999527807696463526129325131859
      476909
      ((2101460028687299691565021880390078607360765232903932657646079862933431776295587474661434077342935932577926037828117497747081955838865726217676864344799721840050457595801606311306094366943654009661311937339000569323400839,1)::nil)
      63143162213140443627368120363264040180508271802009222242004612405716245471151315624124242272249704978124435792394656020928244610827459900819272822289433849166996701301505252846059965747526164287003455575250764910136983935111
      133994556832302055478458218210501750584062957714674572295719512780581067316330411487847780045428799399874417750164889450234627355730433415343964598810590478694898616781419464628511900871439668978123378466906481747805613872198
      0
      422206001406159163960843569911722107096687101001045548249847140383360755940087100226065845175917102536485515849531483669101545163982172729397521895282686243912641836349451173254195827207941126357502966476000116874048037826590)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
