From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo67:
  prime  463896941412524415085334837739139699906400172715066142428004893567526535690487984495785932266887237452546228969093->
  prime  64539198077076046724332123965620071609778017628810861999153617149184656728039245295128198760184309893727119348720516513.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      64539198077076046724332123965620071609778017628810861999153617149184656728039245295128198760184309893727119348720516513
      139124
      ((463896941412524415085334837739139699906400172715066142428004893567526535690487984495785932266887237452546228969093,1)::nil)
      64539198077076046724332123965620071609778017628810861999153617149184656728039245295128198759336477651343615764826986593
      9501955807025115933281263315351902213136
      0
      97477976010097357444)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
