From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo63:
  prime  11881390718810936520586983549148612986385444943379804980739879158213649536582163151939080131136525234056429866414354964555134920444033749->
  prime  275042183054456462594766355722422201387093814754404728321292674494817033758084260279364206411091065937671460558763330141097022557157736930295943.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      275042183054456462594766355722422201387093814754404728321292674494817033758084260279364206411091065937671460558763330141097022557157736930295943
      23148989
      ((11881390718810936520586983549148612986385444943379804980739879158213649536582163151939080131136525234056429866414354964555134920444033749,1)::nil)
      179971600941111556276357519127079312518783938816939846876624346921590603901380394525887840270090858596033288969031509252410419195513979754378161
      115595644881563852196284558851199618478455346414583444905814132272804086814682367906104533220346909463557609747046501223605510920096442006960283
      0
      245504614615960178616194633960560700051177300827990744050027510898153879593111618566238248776408081399790491912331807677722757986593599014515791)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
