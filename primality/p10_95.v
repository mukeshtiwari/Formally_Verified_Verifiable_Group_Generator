From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo95:
  prime  1075157264876073627091147895154689956971675405822896289421656187433942256903848923624217618805002051185124395736740565642875079115150565985883689454411713652197636283673919->
  prime  406900792993204196688034558956558497045629359061515861005651735727687484721059952088050491265178988654221921508114993396652198840860807638356953027573776856321285133449624696499.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      406900792993204196688034558956558497045629359061515861005651735727687484721059952088050491265178988654221921508114993396652198840860807638356953027573776856321285133449624696499
      378457
      ((1075157264876073627091147895154689956971675405822896289421656187433942256903848923624217618805002051185124395736740565642875079115150565985883689454411713652197636283673919,1)::nil)
      339241505388279364071509874613535603550502333981365451286110803705364694591146665052222166032077792000748415056762078105907563743462693641525734204425928737239998897413930311518
      39641030921519024644600089142855523900933331361095362406538658981881147973334556324062724596798895748133826751411808257971021878782396575569448902874322544099216747869039671503
      0
      157643432100925230769750227174915429199886490809938536628577055256349534366947637080858058914395830817950750051785985138139864775219631770980812012011378178675982365374295183714)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
