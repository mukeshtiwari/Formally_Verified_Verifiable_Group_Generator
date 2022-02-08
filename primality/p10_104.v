From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo104:
  prime  61618173516379359947068322270001115328022527361135916842860864077587698736818184690567134923663444691->
  prime  181673913668569610039457194151070428413065715266080636583908648435693817788084314887280919112598096401475567.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      181673913668569610039457194151070428413065715266080636583908648435693817788084314887280919112598096401475567
      2948382
      ((61618173516379359947068322270001115328022527361135916842860864077587698736818184690567134923663444691,1)::nil)
      32480678432873906066684661356035316132526953561530025054498713943535818897810747247975887962293403002643176
      53997426072123356035752069843517178635932774022780125117039195980964330300383694859290552987903204987805410
      55471801822622010351262342193680151692463445512750455471614822501561578227000491197150700108968016738005393
      73170952123855771713832119024004611884506805001115995047149854778871035667096189969412383072798223434687614)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
