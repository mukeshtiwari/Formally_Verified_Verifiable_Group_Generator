From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo55:
  prime  216182352325922265917850732339879955165292085161491682865866987423930555864436987053723272488481181569039509363942496070786308152303542615598717971233148339981980473264929858726643609503932201->
  prime  4926579627155442518001900339293524298261841328745233960830242776403953437594654497967299656739997677900753960135370144125445754465240083922385874311582103374417147945997981122121521829442354308197.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      4926579627155442518001900339293524298261841328745233960830242776403953437594654497967299656739997677900753960135370144125445754465240083922385874311582103374417147945997981122121521829442354308197
      22789
      ((216182352325922265917850732339879955165292085161491682865866987423930555864436987053723272488481181569039509363942496070786308152303542615598717971233148339981980473264929858726643609503932201,1)::nil)
      1794661608852588621975638695700187508966335254042385270771733170474091968404527778688054312496640449690625540841153210058248061120422240625938546679565750618697766009323563788191442933606022914527
      850679476302422252747215192569659137022088529626522428931029561013983336230524486668776062683764928102717174131407715766071820838074281116513862063277837766287268870947679290540300589390628305115
      1101817034331933587515873653933327261367102879517769843243993331816604145439757664974871411316229954367307286606350113535022126531846392437382989826377574686451436919835522398059034471895999475123
      9989546623883743214384424840330885316094655954691784741317235819188466988982301241635550342773882964305427059035643313796094437547636447133823325928388118503736649968332210529530023278250062562)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
