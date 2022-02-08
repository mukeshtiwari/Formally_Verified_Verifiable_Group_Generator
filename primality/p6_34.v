From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo34:
  prime  331026991425545347456334024203834971012827426591867337968296483053017574304976377080747452379477062377482703608044305057381117086596778645587206511772001008063173900449428671363924403864132454617020942342613207608932730906429074847152277919613020198977077988776081942991227037531152120774478725712433794559520861559130603620989857169->
  prime  57562283538988080469181923468804863109420561210059811399307075438089225995892342210571174494267266376820467330402824206428002450188313838681159340332033255292105309549137997640571823166253320708605534120827582622235093572363566000377338294837103392740176707605035494017053264630730505430671759249079898033089912379350755406888530452685549.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      57562283538988080469181923468804863109420561210059811399307075438089225995892342210571174494267266376820467330402824206428002450188313838681159340332033255292105309549137997640571823166253320708605534120827582622235093572363566000377338294837103392740176707605035494017053264630730505430671759249079898033089912379350755406888530452685549
      173890
      ((331026991425545347456334024203834971012827426591867337968296483053017574304976377080747452379477062377482703608044305057381117086596778645587206511772001008063173900449428671363924403864132454617020942342613207608932730906429074847152277919613020198977077988776081942991227037531152120774478725712433794559520861559130603620989857169,1)::nil)
      21585856327120530175943221300801823666032710453772429274740153289283459748459628328964190435350224891307675248901059077410500918820617689505434752624512470734539491080926749115214433687344995265727075295310343483338160089636337250141501860563913772277566265351888310256394974236523939536501909718404961762408717142256533277583198919757082
      0
      28781141769494040234590961734402431554710280605029905699653537719044612997946171105285587247133633188410233665201412103214001225094156919340579670166016627646052654774568998820285911583126660354302767060413791311117546786181783000188669147418551696370088353802517747008526632315365252715335879624539949016544956189675377703444265226342776
      43171712654241060351886442601603647332065420907544858549480306578566919496919256657928380870700449782615350497802118154821001837641235379010869505249024941469078982161853498230428867374689990531454150590620686966676320179272674500283003721127827544555132530703776620512789948473047879073003819436809923524817434284513066555166397839514164)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
