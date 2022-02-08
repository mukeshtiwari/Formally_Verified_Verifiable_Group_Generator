From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo0:
  prime  23486306851125893749725975161384059843256911->
  prime  1290901369765283624059937656030717865883653573059.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1290901369765283624059937656030717865883653573059
      54964
      ((23486306851125893749725975161384059843256911,1)::nil)
      0
      247086590306636318667722441974629591516793061933
      322725342441320906014984414007679466470913393345
      1048857362934292944548699345524958266030468528826)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo1:
  prime  335840116270228558044637904031161417641->
  prime  23486306851125893749725975161384059843256911.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      23486306851125893749725975161384059843256911
      69933
      ((335840116270228558044637904031161417641,1)::nil)
      0
      3584
      8
      64)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo2:
  prime  104686683895272379797605651421581->
  prime  335840116270228558044637904031161417641.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      335840116270228558044637904031161417641
      3208050
      ((104686683895272379797605651421581,1)::nil)
      191152540727727698868771903303529143127
      0
      227324434613352913662738403485437211756
      6862047533067749932626268262659199990)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo3:
  prime  9805796543206478556987095089->
  prime  104686683895272379797605651421581.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      104686683895272379797605651421581
      10676
      ((9805796543206478556987095089,1)::nil)
      900
      0
      90
      900)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo4:
  prime  861896505511677542902399->
  prime  9805796543206478556987095089.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      9805796543206478556987095089
      11377
      ((861896505511677542902399,1)::nil)
      0
      19008
      12
      144)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo5:
  prime  4205712944773->
  prime  861896505511677542902399.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      861896505511677542902399
      204934696407
      ((4205712944773,1)::nil)
      0
      8192000
      320
      6400)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.

Lemma primo6:
  prime  34607263->
  prime  4205712944773.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      4205712944773
      121527
      ((34607263,1)::nil)
      0
      199794688
      1392
      53824)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
Lemma primo7 : prime 34607263.
Proof.
 apply (Pocklington_refl
         (Pock_certif 34607263 3 ((5767877, 1)::(2,1)::nil) 1)
        ((Pock_certif 5767877 2 ((73, 1)::(2,2)::nil) 480) ::
         (Proof_certif 73 prime73) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.


Lemma  primo: prime 1290901369765283624059937656030717865883653573059.
Proof.
exact
(primo0 (primo1 (primo2 (primo3 (primo4 (primo5 (primo6 primo7))))))).
Qed.
