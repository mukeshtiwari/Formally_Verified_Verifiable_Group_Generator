From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo88:
  prime  5971134960038331698578938450239960282347143223183637961226094160931266911852706829655877941718786273859921846235863774333205849634187016507823835289368570915717853986125308070106506457768806413693587792934305677539->
  prime  969873538154146102805081235657126028780799432312048763128070796277582890691499612220515286439557298104245525767349497962759855704676408814857202781474065674640567578907455992741346325511632000311937721742629013152101041.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      969873538154146102805081235657126028780799432312048763128070796277582890691499612220515286439557298104245525767349497962759855704676408814857202781474065674640567578907455992741346325511632000311937721742629013152101041
      162427
      ((5971134960038331698578938450239960282347143223183637961226094160931266911852706829655877941718786273859921846235863774333205849634187016507823835289368570915717853986125308070106506457768806413693587792934305677539,1)::nil)
      969873538154146102805081235657126028780799432312048763128070796277582890691499612220515286439557298104245525767349497962759855704676408814857202781474065674640567578907455992741346325511632000311937721634095738477835721
      13762346127466829996235398
      1918747
      3681590050009)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
