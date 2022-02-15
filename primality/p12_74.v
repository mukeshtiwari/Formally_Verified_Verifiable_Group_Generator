From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo74:
  prime  125873088172807446369663476392299789527746484662159676174358077864788990549306236946033269502365909850582498260457391238303899481506786116657586674206329881857751057956300038081135621775745187585549487169514906401655206789370749883488085059512643766542994161112310232103386754219201453167206241->
  prime  5322040041034471639955741445342827401022649118000773268328033890201143309415217004315232667829533034392478608950398958946727173977588423798399422172160283505060621363802491698961414460069765178815290416077229883138586181267010485037718234573164410681522875816798429538266023385777029780556650987243.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      5322040041034471639955741445342827401022649118000773268328033890201143309415217004315232667829533034392478608950398958946727173977588423798399422172160283505060621363802491698961414460069765178815290416077229883138586181267010485037718234573164410681522875816798429538266023385777029780556650987243
      42281
      ((125873088172807446369663476392299789527746484662159676174358077864788990549306236946033269502365909850582498260457391238303899481506786116657586674206329881857751057956300038081135621775745187585549487169514906401655206789370749883488085059512643766542994161112310232103386754219201453167206241,1)::nil)
      5322040041034471639955741445342827401022649118000773268328033890201143309415217004315232667829533034392478608950398958946727173977588423798399422172160283505060621363802491698961414460069765178815290416077229883138586181267010485037718234573164410681522875816798429538266023385776917886724203186763
      14406462054002124060149776
      0
      3795584547076)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.