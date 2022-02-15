From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo98:
  prime  56464570186447940004872160209138196917133205540383191844303834827929285898770812337413420557420935036451934358197382181843660323798983102446667649->
  prime  81824841381708421986900422756829690127706744943968737096487081987206133650196600639138109260489967887628181486843479767993263316453851192974699932897233.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      81824841381708421986900422756829690127706744943968737096487081987206133650196600639138109260489967887628181486843479767993263316453851192974699932897233
      1449136
      ((56464570186447940004872160209138196917133205540383191844303834827929285898770812337413420557420935036451934358197382181843660323798983102446667649,1)::nil)
      0
      13310
      11
      121)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.