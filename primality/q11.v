From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo0:
  prime  26350865678096846136746349376317654316485830891353831893494537323036336747697->
  prime  105403462712387384546985397505270617265354773959498348592134315639767444006447.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      105403462712387384546985397505270617265354773959498348592134315639767444006447
      4
      ((26350865678096846136746349376317654316485830891353831893494537323036336747697,1)::nil)
      22848106517656945577988996691254724847861027476293427327182258866077453275791
      42878741310375357507591617880420294015764569007324025523098887579372263948375
      58487165793251695408015516384013013375882790385936711709928856160363408123091
      75296280253854243900853407321479259151114505133478798688998962338361995812623)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo1:
  prime  165035458084906319912274600763329706616982145895848796923810895204003->
  prime  26350865678096846136746349376317654316485830891353831893494537323036336747697.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      26350865678096846136746349376317654316485830891353831893494537323036336747697
      159667904
      ((165035458084906319912274600763329706616982145895848796923810895204003,1)::nil)
      26350865678096846136746349376317654316485830891353831893494537323036336733697
      784000
      60
      400)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo2:
  prime  17010457440208855896956771878306501852575094355022084976761653003->
  prime  165035458084906319912274600763329706616982145895848796923810895204003.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      165035458084906319912274600763329706616982145895848796923810895204003
      9702
      ((17010457440208855896956771878306501852575094355022084976761653003,1)::nil)
      165035458084906319912274600763329706616982145895848796923810895175173
      1668296
      155
      961)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo3:
  prime  431577131814046830944787992062312328471477432566058161->
  prime  17010457440208855896956771878306501852575094355022084976761653003.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      17010457440208855896956771878306501852575094355022084976761653003
      39414640365
      ((431577131814046830944787992062312328471477432566058161,1)::nil)
      17010457440208855896956771878306501852575094355022084976695916739
      210482039306
      2495
      249001)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo4:
  prime  1319985355258954816381372390181407827555904840183->
  prime  431577131814046830944787992062312328471477432566058161.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      431577131814046830944787992062312328471477432566058161
      326956
      ((1319985355258954816381372390181407827555904840183,1)::nil)
      431577131814046830944787992062312328471477432565722021
      92236816
      0
      9604)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo5:
  prime  2219540844643793063153988381694505394387377->
  prime  1319985355258954816381372390181407827555904840183.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1319985355258954816381372390181407827555904840183
      594711
      ((2219540844643793063153988381694505394387377,1)::nil)
      1319985355258954816381372390181295933723457039703
      14406462054002124060149776
      0
      3795584547076)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo6:
  prime  58087957200832061323039042700432434121->
  prime  2219540844643793063153988381694505394387377.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2219540844643793063153988381694505394387377
      38210
      ((58087957200832061323039042700432434121,1)::nil)
      739846948214597687717996127231501798144967
      0
      1308
      47524)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo7:
  prime  518181589496542622481681788797->
  prime  58087957200832061323039042700432434121.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      58087957200832061323039042700432434121
      112099616
      ((518181589496542622481681788797,1)::nil)
      100
      0
      20
      100)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo8:
  prime  46688930282975317189->
  prime  518181589496542622481681788797.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      518181589496542622481681788797
      11098596313
      ((46688930282975317189,1)::nil)
      0
      54
      3
      9)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo9:
  prime  92016939031->
  prime  46688930282975317189.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      46688930282975317189
      507394951
      ((92016939031,1)::nil)
      0
      23625
      30
      225)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo10:
  prime  38149399->
  prime  92016939031.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      92016939031
      2412
      ((38149399,1)::nil)
      0
      78608
      17
      289)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
Lemma primo11 : prime 38149399.
Proof.
 apply (Pocklington_refl
         (Pock_certif 38149399 3 ((67, 1)::(3, 1)::(2,1)::nil) 1)
        ((Proof_certif 67 prime67) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.


Lemma  primo: prime 105403462712387384546985397505270617265354773959498348592134315639767444006447.
Proof.
exact
(primo0 (primo1 (primo2 (primo3 (primo4 (primo5 (primo6 (primo7 (primo8 (primo9 (primo10 primo11))))))))))).
Qed.