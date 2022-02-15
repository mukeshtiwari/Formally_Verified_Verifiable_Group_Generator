From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo35:
  prime  2330825607472928026250056252217065685270391147006645677657976868014183112152797824053021808832440918721337960442550631819968979576196628744921690010405433484373278358826583854067721193701452013927357568102517589689519484858079794399443472580850248421688422329516712738632748395483007256023616693601463654579232650561093051230218556161922729158533->
  prime  54958536998604169930950076371026191792990552855269698433497436570906423601450819893346201230460124422530427769274901347683048569427140309176508528755349716128037530422772020696088159596737308717757723827093192018874676077956533866555108190276775957245795877942118796100925210130894060175476918178395970606150418635093608795702559958172221716184635753.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      54958536998604169930950076371026191792990552855269698433497436570906423601450819893346201230460124422530427769274901347683048569427140309176508528755349716128037530422772020696088159596737308717757723827093192018874676077956533866555108190276775957245795877942118796100925210130894060175476918178395970606150418635093608795702559958172221716184635753
      23579
      ((2330825607472928026250056252217065685270391147006645677657976868014183112152797824053021808832440918721337960442550631819968979576196628744921690010405433484373278358826583854067721193701452013927357568102517589689519484858079794399443472580850248421688422329516712738632748395483007256023616693601463654579232650561093051230218556161922729158533,1)::nil)
      54958536998604169930950076371026191792990552855269698433497436570906423601450819893346201230460124422530427769274901347683048569427140309176508528755349716128037530422772020696088159596737308717757723827093192018874676077956533866555108190276775957245795877942118796100925210130894060175476918178395970606150418635093608795702559958066997094020835273
      13137846356232616428550224
      3778548
      3569356247076)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.