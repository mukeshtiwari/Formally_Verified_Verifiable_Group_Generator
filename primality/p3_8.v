From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo8:
  prime  84465429248621074834104389010385443415917570288230024512813778119501863024390860748784591790158011973382717181997113077615160259364013723781926661628005045693989205395073770540247437745706184351892244035944575803729492005429973834930286257168519->
  prime  5002421283552346782378394774431432342254386378998174257830092462603834523016250150633581546096370818996842250144505685264698401390211885235434679755061074344630225340300151184478135597941166876028678317529790224556901555599137084291129123203585132255359376093641.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      5002421283552346782378394774431432342254386378998174257830092462603834523016250150633581546096370818996842250144505685264698401390211885235434679755061074344630225340300151184478135597941166876028678317529790224556901555599137084291129123203585132255359376093641
      59224481874447029
      ((84465429248621074834104389010385443415917570288230024512813778119501863024390860748784591790158011973382717181997113077615160259364013723781926661628005045693989205395073770540247437745706184351892244035944575803729492005429973834930286257168519,1)::nil)
      2710749276603390202277573447787448336999945634427520414506491292366762174820515593233823941172721314744814759655782340423366670384913577197675287307168291375451608072790039045105492249754968783995034764797766965077840684060014923854954730752065558179643470557731
      551475424110161802925139849761162665643560693859390604910557852815060542837716285163202162375043281756074838162951355010333280896593263521231075823961504923868456918463779181502632134744107266591232429605590827854443989853898311666083771693054471147282877031786
      4635451449267582636226150723306202652129401230676871135204212255526024964027806822324196936248993642371891064815627896063287953071737623458761075849274024092693645867891170937488203699374538222415869119457322198023891834425179660748781345294483840065570825331049
      3138247777261472008729988335259687096330597340504802200716386059480012115218908736077434148213652979866700599899871950009723473427324932996308194746574895215159309588729990663678191211724083935406475081793732845807101271725118537734201956167470067050259559120315)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.