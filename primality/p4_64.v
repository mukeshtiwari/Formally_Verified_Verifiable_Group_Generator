From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo64:
  prime  1531017342173041254383385810226569631059225878169753357109446456458662244678516328352440432063725190951516134703837413393621->
  prime  11881390718810936520586983549148612986385444943379804980739879158213649536582163151939080131136525234056429866414354964555134920444033749.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      11881390718810936520586983549148612986385444943379804980739879158213649536582163151939080131136525234056429866414354964555134920444033749
      7760454693444
      ((1531017342173041254383385810226569631059225878169753357109446456458662244678516328352440432063725190951516134703837413393621,1)::nil)
      4285195747876870251036506275809817483393525892589489733641007252084425167663495331449546688283699432321618252485061114395977971370435298
      11453519225828962635454241606140681248686346245326269221996869545203492057238198942903896335206427112544650193246750977545246654660626930
      9461890939614730005597430498960139151946413852780223145770581225066801135686192301683968326797843646272878835366016606073411036920432762
      563009125915780096390393823766773982285208166896545304338206066717232182516307142206157160044882299032824723895304312187769433498974186)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.