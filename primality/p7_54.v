From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo54:
  prime  583877011750465488933640792687003122891594359415036374730039152818733283259162052700663347917057768343706305597533206005065000288407777761087885579331708797333982379->
  prime  9473404515651302557948321861346625668916118481508965179994885254483947520879904305067176629772741682007023174409263039555076527529578354936296899217730040960567010067771.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      9473404515651302557948321861346625668916118481508965179994885254483947520879904305067176629772741682007023174409263039555076527529578354936296899217730040960567010067771
      16225
      ((583877011750465488933640792687003122891594359415036374730039152818733283259162052700663347917057768343706305597533206005065000288407777761087885579331708797333982379,1)::nil)
      9473404515651302557948321861346625668916118481508965179994885254483947520879904305067176629772741682007023174409263039555076527529578354936296899217730040943330347249531
      27544082901737469648
      141572
      5010657796)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.