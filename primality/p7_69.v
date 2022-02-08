From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo69:
  prime  734552515987812661072171025771831165337364497400567819->
  prime  9610885119184540857468285701297521244902759938277301659771.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      9610885119184540857468285701297521244902759938277301659771
      13084
      ((734552515987812661072171025771831165337364497400567819,1)::nil)
      0
      77626969
      1338
      49729)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
