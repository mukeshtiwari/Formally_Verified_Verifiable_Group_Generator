From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo69:
  prime  5557675995137669174935523381497223338011287320247712509764111592389846230599677433092582153956156658529234500997274639855418509844698522003601116408842155750954654415930811979720755695229738734966706286877667713818805941039101021696854787226961748193169547063291817944370387613606822519724050000898342233648247427971543361->
  prime  171407897855437694509150184698953838162775819580517862526766312293430300997974541504339836388561899007528165247682595396296868284151746171152364371890766672916430617379251632105585147170188494647162237650663099295220748508095179423579496505309562463819791717462517846609251311705611374200747360017257931372956729614525465399104811.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      171407897855437694509150184698953838162775819580517862526766312293430300997974541504339836388561899007528165247682595396296868284151746171152364371890766672916430617379251632105585147170188494647162237650663099295220748508095179423579496505309562463819791717462517846609251311705611374200747360017257931372956729614525465399104811
      30841650
      ((5557675995137669174935523381497223338011287320247712509764111592389846230599677433092582153956156658529234500997274639855418509844698522003601116408842155750954654415930811979720755695229738734966706286877667713818805941039101021696854787226961748193169547063291817944370387613606822519724050000898342233648247427971543361,1)::nil)
      103743809303978977415687273378627436260470507348650482455429485833247221718565325408330527836691572049793908444790739139121604573173505322621334107461703446751619423361725326686980529861313528079314684044938131288610280826554006507316950847946614672108510356698323438363012747003833284241299119231962309826499320031758728435721261
      45873192406322241045147392369844101034768692628964148156383412483952676047147031964097446802343686325752097546422371144910035681933034493069605243949800187269941776258112305141092487805035485066969019095335464213234719170236927483874469115405672251730706488126820101122008827140192033060536980083793937359629929012564914963518532
      0
      81895612700637201508033089400242120177535383442048597057035045219379879736027004280174035009744267174988776495611538036013395896085676448033527444814951833638199999058720245513645120793893597217479285781949310236203263583422197733059732953128223384592509477960484280739111105994310670600612560553319307501304639051908263178805170)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.