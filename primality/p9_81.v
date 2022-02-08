From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma primo81 : prime 2387947357.
Proof.
 apply (Pocklington_refl
         (Pock_certif 2387947357 2 ((59, 1)::(3, 2)::(2,2)::nil) 2796)
        ((Proof_certif 59 prime59) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

