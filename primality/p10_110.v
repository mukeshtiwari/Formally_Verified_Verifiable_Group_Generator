From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo110:
  prime  15308436889580340054792726747924218996149252441684812835747297->
  prime  263679865035838775666976226015085728232425958431051665249711358281049.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      263679865035838775666976226015085728232425958431051665249711358281049
      17224480
      ((15308436889580340054792726747924218996149252441684812835747297,1)::nil)
      100
      0
      20
      100)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
