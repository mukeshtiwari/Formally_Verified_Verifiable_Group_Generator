From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo49:
  prime  2354899596955055799380965000850931719269328632207273694399639794409932150851054242407650819490129162961197338086659682489168770710730959984329768477411424051306047335026250899828807353443116469329257285512447763->
  prime  187694917475705767433860434427822661752642569301448542538428890173649232151432427336859400916641254804659273461511632238073780315199128715085832355203678386748796200637468525575395216980875112081039489933447449514809.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      187694917475705767433860434427822661752642569301448542538428890173649232151432427336859400916641254804659273461511632238073780315199128715085832355203678386748796200637468525575395216980875112081039489933447449514809
      79704
      ((2354899596955055799380965000850931719269328632207273694399639794409932150851054242407650819490129162961197338086659682489168770710730959984329768477411424051306047335026250899828807353443116469329257285512447763,1)::nil)
      187694917475705767433860434427822661752642569301448542538428890173649232151432427336859400916641254804659273461511632238073780315199128715085832355203678386748796200637468525575395216980875112081039489933447449420729
      9834496
      0
      3136)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
