From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo61:
  prime  3853891068959043953877866176382579885835958532338719053237952955021376277113069972050917150557481799995581390493315807472221122020161252808510974269->
  prime  6537428644205536480798148074455121529361367341618283565669551118708905985016030968210236868308507598138692263684282686635658380570272678132965804273854139.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      6537428644205536480798148074455121529361367341618283565669551118708905985016030968210236868308507598138692263684282686635658380570272678132965804273854139
      1696319
      ((3853891068959043953877866176382579885835958532338719053237952955021376277113069972050917150557481799995581390493315807472221122020161252808510974269,1)::nil)
      4511159093146150767956498751148446983849405640707273482163719241553204819734786954314145159998867448154127775243289455208634485236996039479790154630509379
      3776237116084113604106213359272566415977624099634021073440876048228495238194969247134189840275663418597139806571526700183073854682866773973637828361226055
      0
      456669900290962566758446803732920418321821299704847487864768093634319420866336631012628104122129339090364284839584167811033778637191734732757203073047269)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
