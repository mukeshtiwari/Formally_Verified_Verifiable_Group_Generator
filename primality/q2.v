From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo0:
  prime  67192814393039522645737495320583597397336979277->
  prime  1343856287860790452914751222519946200803732236971.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1343856287860790452914751222519946200803732236971
      20
      ((67192814393039522645737495320583597397336979277,1)::nil)
      568829907472889752598618903725557131301721299529
      539885868114899402095059196422141040639467733562
      40094118342983999931846570473375995449207177700
      681960388709536806606801150137869806040202391591)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo1:
  prime  1335675506031992985438915017890333->
  prime  67192814393039522645737495320583597397336979277.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      67192814393039522645737495320583597397336979277
      50306241365955
      ((1335675506031992985438915017890333,1)::nil)
      67192814393039522645737495320583597396579395373
      8234810772496
      0
      2869636)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo2:
  prime  7870648315474267213421->
  prime  1335675506031992985438915017890333.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1335675506031992985438915017890333
      169703365275
      ((7870648315474267213421,1)::nil)
      1335675506031992985438914260306429
      8234810772496
      0
      2869636)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo3:
  prime  2322084096665869->
  prime  7870648315474267213421.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      7870648315474267213421
      3389476
      ((2322084096665869,1)::nil)
      900
      0
      90
      900)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo4:
  prime  25800933341657->
  prime  2322084096665869.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2322084096665869
      90
      ((25800933341657,1)::nil)
      18
      0
      3
      9)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo5:
  prime  279636521->
  prime  25800933341657.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      25800933341657
      92266
      ((279636521,1)::nil)
      48
      0
      4
      16)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
Lemma primo6 : prime 279636521.
Proof.
 apply (Pocklington_refl
         (Pock_certif 279636521 3 ((6990913, 1)::(2,3)::nil) 1)
        ((Pock_certif 6990913 5 ((3, 1)::(2,6)::nil) 313) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.


Lemma  primo: prime 1343856287860790452914751222519946200803732236971.
Proof.
exact
(primo0 (primo1 (primo2 (primo3 (primo4 (primo5 primo6)))))).
Qed.
