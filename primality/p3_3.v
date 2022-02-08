From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo3:
  prime  188313033573937036815777527908607354453902521931166926201241394441260222415790495114033042412597815661945004798818155298118855094446543597425281341437538942536447303210208475921553753743095325799013622258238350004202177926764687193429411397273900381292400871799257834018279811176693767621->
  prime  14122265257034532280135427835256745538187753945338443060491356468045111746210210375387572485743032009284703533505759361058181908512435082260311634502332743064855456977773776819475262407482814887596529736727906326595641696239959360165355550400160342751808949843514640095416023610082844840350288488341.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      14122265257034532280135427835256745538187753945338443060491356468045111746210210375387572485743032009284703533505759361058181908512435082260311634502332743064855456977773776819475262407482814887596529736727906326595641696239959360165355550400160342751808949843514640095416023610082844840350288488341
      74993562522
      ((188313033573937036815777527908607354453902521931166926201241394441260222415790495114033042412597815661945004798818155298118855094446543597425281341437538942536447303210208475921553753743095325799013622258238350004202177926764687193429411397273900381292400871799257834018279811176693767621,1)::nil)
      18
      0
      3
      9)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
