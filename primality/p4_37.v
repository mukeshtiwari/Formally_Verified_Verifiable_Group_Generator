From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo37:
  prime  215577638956981077477482885600795599068329998453608547765928834574798251507556835783583120971441085228031910172511544929435194021137152695874368697649387123337671049673084107317415801365316982135406848749639196929934855939968893419463074787420357941831167951740425181020537213985797283097028846237808101091383592660860803743->
  prime  7693668437232894021284445260710265832821983349411423089970083124182836374717623040682700242763791743090844190020898972599539454046635810445035912190303870277691273771548167383947178624336127324858345231204473470494840060238465520880087883089311512614839981800736329165816712911613930974979586724015502752780012530109497352976200069.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      7693668437232894021284445260710265832821983349411423089970083124182836374717623040682700242763791743090844190020898972599539454046635810445035912190303870277691273771548167383947178624336127324858345231204473470494840060238465520880087883089311512614839981800736329165816712911613930974979586724015502752780012530109497352976200069
      35688620
      ((215577638956981077477482885600795599068329998453608547765928834574798251507556835783583120971441085228031910172511544929435194021137152695874368697649387123337671049673084107317415801365316982135406848749639196929934855939968893419463074787420357941831167951740425181020537213985797283097028846237808101091383592660860803743,1)::nil)
      5444720725443895061687952471411937431484227488832994542955732080856836630821160510561794658424079749515671562700237943133007764675310594580083059969771606055407328960079582653840168203950891678533432923692103095583434070228982483403835023376798249230004226186776970061903665794074458634943708759669928960969551608667726326226302685
      102538690625070678421139942042579243264266805647712480643088428205096332349804334180754715607058889480563192715183987343828462066787643142426172628968963349505191266840244732448811239952081695285369289491164759661914562079342270002320975424018085222221728713369243169423904029900225409621069613044649441871982516189667387855980332
      3457744180061658447775987594249988490022309989424487755224565806933620326274273755830753605992311571109637896110942614305172833655524254727624798240030758126207782711936062754196300867684078773063809438741890483422790981690515540597358569237132133164650404905085155918979613246511253928975406290592640137707215296889364395676604085
      5176573055928180097293325156178080706651288610011523656436943140545154551298662595040975693615538872780833831545889342215983844741233715099777028122775855192892597740910717488432042816226508912278526382538466942823054361784914985621975208595495583550458060927205214435869983607393290868757939538808788051101653908574314836875343146)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
