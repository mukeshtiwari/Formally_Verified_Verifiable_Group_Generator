From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo92:
  prime  383608051283200490308980283415994871585107931290653573863062831387754931707001687080117899537920097043112851634509808164371653218716711559772201031009238577726654048096408024776890163883->
  prime  4481309255090348127789507670865652089857230853337415049868299996271753112201193708469937302401927221062429963935238065503246781097698412952356606202669759429211879057508260898294826090636691.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      4481309255090348127789507670865652089857230853337415049868299996271753112201193708469937302401927221062429963935238065503246781097698412952356606202669759429211879057508260898294826090636691
      11682
      ((383608051283200490308980283415994871585107931290653573863062831387754931707001687080117899537920097043112851634509808164371653218716711559772201031009238577726654048096408024776890163883,1)::nil)
      4481309255090348127789507670865652089857230853337415049868299996271753112201193708469937302401927221062429963935238065503246781097698412952356606202669759429211879057508260898294826090614821
      1102248
      27
      729)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
