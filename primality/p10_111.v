From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo111:
  prime  581539161585638202962799223063598640408498009659927112509->
  prime  15308436889580340054792726747924218996149252441684812835747297.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      15308436889580340054792726747924218996149252441684812835747297
      26324
      ((581539161585638202962799223063598640408498009659927112509,1)::nil)
      1584
      0
      12
      144)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
