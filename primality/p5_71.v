From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo71:
  prime  1528638076219101732679581092598562292203451496487->
  prime  17490676868098962025319766638638643964158174562791441.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      17490676868098962025319766638638643964158174562791441
      11442
      ((1528638076219101732679581092598562292203451496487,1)::nil)
      9234548701364719405134795000789057852813271569906057
      7898158122123853858024540971987767717667133667379934
      0
      14900568402632218654723214018586438403497360441492147)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.