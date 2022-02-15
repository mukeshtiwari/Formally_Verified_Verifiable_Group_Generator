From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo20:
  prime  137265144931307901436513277702434732454012822552379919297358247491638591400086965060671265532597024643333098176212479598114660643440913961816102416340575324941403970061->
  prime  2644138486811784105371555268382000251261649000826494385425011921431434186139875207963608959490987584685597236693935139749864610649504336524415929771268742545944950507771003.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2644138486811784105371555268382000251261649000826494385425011921431434186139875207963608959490987584685597236693935139749864610649504336524415929771268742545944950507771003
      19263
      ((137265144931307901436513277702434732454012822552379919297358247491638591400086965060671265532597024643333098176212479598114660643440913961816102416340575324941403970061,1)::nil)
      1920070472032591264356989818676816349432767948759865903026300521926901836223916448427917236524163464115135673896863956614888357991407097068619591813542330016196826514478873
      1358670618691073971843095309590046532062235642182511233642028948918338551157022126153177960350431885934414470133035229166996217802468614882630522966184512661431308812395318
      0
      1433135397089645170276028445301797483345476296818317547451866300257000914686387461763448289280828926400995687162383963506704953627153862603296653600316788084414792188499601)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.