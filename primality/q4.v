From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo0:
  prime  1056577323731826791386705045434642761237645146241030558477953->
  prime  14081255345622456359933385402898207805059511032562442425688613821451.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      14081255345622456359933385402898207805059511032562442425688613821451
      13327236
      ((1056577323731826791386705045434642761237645146241030558477953,1)::nil)
      0
      221184
      48
      576)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo1:
  prime  39836267531268212170067678823534754395768081133872315193->
  prime  1056577323731826791386705045434642761237645146241030558477953.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1056577323731826791386705045434642761237645146241030558477953
      26523
      ((39836267531268212170067678823534754395768081133872315193,1)::nil)
      0
      78608
      17
      289)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo2:
  prime  718508513811810547229906008586834696347861256381089->
  prime  39836267531268212170067678823534754395768081133872315193.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      39836267531268212170067678823534754395768081133872315193
      55443
      ((718508513811810547229906008586834696347861256381089,1)::nil)
      0
      192
      4
      16)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo3:
  prime  22444043112662655604875133511495154558752983->
  prime  718508513811810547229906008586834696347861256381089.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      718508513811810547229906008586834696347861256381089
      32013328
      ((22444043112662655604875133511495154558752983,1)::nil)
      0
      625888275703256843876050937167438036271769836956537
      359254256905905273614953004293417348173930628190732
      673601731698572388028036883050157527826119927866060)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo4:
  prime  159008181907780153062739481570839->
  prime  22444043112662655604875133511495154558752983.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      22444043112662655604875133511495154558752983
      141150240468
      ((159008181907780153062739481570839,1)::nil)
      0
      78608
      17
      289)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo5:
  prime  4029297871621016537010019723->
  prime  159008181907780153062739481570839.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      159008181907780153062739481570839
      39463
      ((4029297871621016537010019723,1)::nil)
      0
      192
      4
      16)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo6:
  prime  1888189342768024404463->
  prime  4029297871621016537010019723.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      4029297871621016537010019723
      2133948
      ((1888189342768024404463,1)::nil)
      0
      9000
      10
      100)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo7:
  prime  162741453571->
  prime  1888189342768024404463.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1888189342768024404463
      11602387107
      ((162741453571,1)::nil)
      0
      1272112
      129
      1849)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo8:
  prime  9586039->
  prime  162741453571.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      162741453571
      16977
      ((9586039,1)::nil)
      0
      267674
      23
      529)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
Lemma primo9 : prime 9586039.
Proof.
 apply (Pocklington_refl
         (Pock_certif 9586039 3 ((11, 1)::(7, 1)::(3, 1)::(2,1)::nil) 420)
        ((Proof_certif 11 prime11) ::
         (Proof_certif 7 prime7) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.


Lemma  primo: prime 14081255345622456359933385402898207805059511032562442425688613821451.
Proof.
exact
(primo0 (primo1 (primo2 (primo3 (primo4 (primo5 (primo6 (primo7 (primo8 primo9))))))))).
Qed.
