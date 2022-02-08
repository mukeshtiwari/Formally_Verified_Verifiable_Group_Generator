From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo0:
  prime  272872758933380512806873121353198615987350986253412795541416877->
  prime  24330426677535940043912034992336602917947852561475343645478016569707.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      24330426677535940043912034992336602917947852561475343645478016569707
      89164
      ((272872758933380512806873121353198615987350986253412795541416877,1)::nil)
      0
      23625
      30
      225)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo1:
  prime  8997387197750610419641028796927175520661461067756227595913->
  prime  272872758933380512806873121353198615987350986253412795541416877.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      272872758933380512806873121353198615987350986253412795541416877
      30328
      ((8997387197750610419641028796927175520661461067756227595913,1)::nil)
      173081127628794381876968769165411795617745471027795891960905207
      194430524319963533318407945631450452575262204002694082491057250
      0
      121819343932741236397716983336325993672710732588619046731264218)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo2:
  prime  605347148893664308594385678986278237856970537203->
  prime  8997387197750610419641028796927175520661461067756227595913.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      8997387197750610419641028796927175520661461067756227595913
      14863185883
      ((605347148893664308594385678986278237856970537203,1)::nil)
      0
      5307052604923211614710138079437513686015158676684339260623
      4498693598875305209820514398463587760330730533878113798035
      8435050497891197268413464497119227050620119751021463372709)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo3:
  prime  10868772423399603357411379076408971187368979->
  prime  605347148893664308594385678986278237856970537203.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      605347148893664308594385678986278237856970537203
      55696
      ((10868772423399603357411379076408971187368979,1)::nil)
      605347148893664308594385678986278237856970201063
      92236816
      0
      9604)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo4:
  prime  165043466204021067169909202301500245139->
  prime  10868772423399603357411379076408971187368979.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      10868772423399603357411379076408971187368979
      65854
      ((165043466204021067169909202301500245139,1)::nil)
      7527737844627563756970068909298114722252616
      7034053288673528543058386670626457369054146
      6217012250011104165767606672074020806604598
      10626441491956003476669541396868232237008973)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo5:
  prime  272877214000019404921->
  prime  165043466204021067169909202301500245139.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      165043466204021067169909202301500245139
      604826851552395762
      ((272877214000019404921,1)::nil)
      165043466204021067169909202301500151059
      9834496
      0
      3136)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo6:
  prime  31503159119599->
  prime  272877214000019404921.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      272877214000019404921
      8661900
      ((31503159119599,1)::nil)
      0
      192
      4
      16)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo7:
  prime  269257675399->
  prime  31503159119599.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      31503159119599
      117
      ((269257675399,1)::nil)
      0
      78608
      17
      289)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo8:
  prime  1553329->
  prime  269257675399.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      269257675399
      173343
      ((1553329,1)::nil)
      0
      500
      5
      25)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
Lemma primo9 : prime 1553329.
Proof.
 apply (Pocklington_refl
         (Pock_certif 1553329 11 ((3, 2)::(2,4)::nil) 129)
        ((Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.


Lemma  primo: prime 24330426677535940043912034992336602917947852561475343645478016569707.
Proof.
exact
(primo0 (primo1 (primo2 (primo3 (primo4 (primo5 (primo6 (primo7 (primo8 primo9))))))))).
Qed.
