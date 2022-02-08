From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo65:
  prime  65121245028551751282943653398600388122451015510130345644525570045781110256371889901474799856139686159978001221262398234326000349->
  prime  24336851207090246282456570373511342647569903712383872252889517935235332462536666749269595456358463029929664155707778036021089461806547.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      24336851207090246282456570373511342647569903712383872252889517935235332462536666749269595456358463029929664155707778036021089461806547
      373716
      ((65121245028551751282943653398600388122451015510130345644525570045781110256371889901474799856139686159978001221262398234326000349,1)::nil)
      0
      221184
      48
      576)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
