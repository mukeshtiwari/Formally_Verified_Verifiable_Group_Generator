From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo0:
  prime  1904702897417384023596608361976223365737884686998429930859279308637->
  prime  17142326076756456212369475257786002011777917105623348331929843623049.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      17142326076756456212369475257786002011777917105623348331929843623049
      9
      ((1904702897417384023596608361976223365737884686998429930859279308637,1)::nil)
      0
      78608
      17
      289)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo1:
  prime  169668642679413963386174432850997240855896992882646930329717->
  prime  1904702897417384023596608361976223365737884686998429930859279308637.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1904702897417384023596608361976223365737884686998429930859279308637
      11226016
      ((169668642679413963386174432850997240855896992882646930329717,1)::nil)
      1904702897417384023596608361976223365737884686998429930859279165277
      25690112
      64
      4096)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo2:
  prime  13418115009785801404945250604188407884542768044402141->
  prime  169668642679413963386174432850997240855896992882646930329717.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      169668642679413963386174432850997240855896992882646930329717
      12644745
      ((13418115009785801404945250604188407884542768044402141,1)::nil)
      169668642679413963386174432850997240855896992882646927997013
      1407009296
      752
      8836)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo3:
  prime  110706866190767643022880852081236697257723186159->
  prime  13418115009785801404945250604188407884542768044402141.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      13418115009785801404945250604188407884542768044402141
      121204
      ((110706866190767643022880852081236697257723186159,1)::nil)
      0
      5832
      9
      81)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo4:
  prime  47070349761195076660078284686222844469->
  prime  110706866190767643022880852081236697257723186159.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      110706866190767643022880852081236697257723186159
      2351944839
      ((47070349761195076660078284686222844469,1)::nil)
      0
      500
      5
      25)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo5:
  prime  863311808983274520279000697122241->
  prime  47070349761195076660078284686222844469.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      47070349761195076660078284686222844469
      54523
      ((863311808983274520279000697122241,1)::nil)
      0
      19008
      12
      144)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo6:
  prime  5615902144141379137->
  prime  863311808983274520279000697122241.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      863311808983274520279000697122241
      153726291310809
      ((5615902144141379137,1)::nil)
      0
      192
      4
      16)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo7:
  prime  312185343724123->
  prime  5615902144141379137.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      5615902144141379137
      17989
      ((312185343724123,1)::nil)
      0
      3584
      8
      64)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo8:
  prime  601268677->
  prime  312185343724123.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      312185343724123
      519211
      ((601268677,1)::nil)
      0
      75449
      38
      361)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
Lemma primo9 : prime 601268677.
Proof.
 apply (Pocklington_refl
         (Pock_certif 601268677 2 ((53, 1)::(3, 1)::(2,2)::nil) 284)
        ((Proof_certif 53 prime53) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.


Lemma  primo: prime 17142326076756456212369475257786002011777917105623348331929843623049.
Proof.
exact
(primo0 (primo1 (primo2 (primo3 (primo4 (primo5 (primo6 (primo7 (primo8 primo9))))))))).
Qed.
