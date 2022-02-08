From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo0:
  prime  7511454979644000986230316731712538633859->
  prime  844113965010316097277499590036987774008311032817.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      844113965010316097277499590036987774008311032817
      112376892
      ((7511454979644000986230316731712538633859,1)::nil)
      0
      2058000
      280
      4900)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo1:
  prime  324388810920302428859948383->
  prime  7511454979644000986230316731712538633859.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      7511454979644000986230316731712538633859
      23155715384676
      ((324388810920302428859948383,1)::nil)
      0
      78608
      17
      289)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo2:
  prime  316196784624223274119->
  prime  324388810920302428859948383.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      324388810920302428859948383
      1025908
      ((316196784624223274119,1)::nil)
      0
      215622
      99
      1089)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo3:
  prime  5807743453652809->
  prime  316196784624223274119.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      316196784624223274119
      54444
      ((5807743453652809,1)::nil)
      0
      5832
      9
      81)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo4:
  prime  12963712740031->
  prime  5807743453652809.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      5807743453652809
      448
      ((12963712740031,1)::nil)
      0
      35672
      14
      196)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo5:
  prime  11795920489->
  prime  12963712740031.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      12963712740031
      1099
      ((11795920489,1)::nil)
      0
      192
      4
      16)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo6:
  prime  302464717->
  prime  11795920489.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      11795920489
      39
      ((302464717,1)::nil)
      0
      500
      5
      25)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
Lemma primo7 : prime 302464717.
Proof.
 apply (Pocklington_refl
         (Pock_certif 302464717 2 ((25205393, 1)::(2,2)::nil) 1)
        ((Pock_certif 25205393 3 ((1575337, 1)::(2,4)::nil) 1) ::
         (Pock_certif 1575337 5 ((7, 1)::(3, 1)::(2,3)::nil) 304) ::
         (Proof_certif 7 prime7) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.


Lemma  primo: prime 844113965010316097277499590036987774008311032817.
Proof.
exact
(primo0 (primo1 (primo2 (primo3 (primo4 (primo5 (primo6 primo7))))))).
Qed.
