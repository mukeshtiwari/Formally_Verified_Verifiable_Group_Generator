From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma primo79 : prime 66576253.
Proof.
 apply (Pocklington_refl
         (Pock_certif 66576253 2 ((47, 1)::(3, 1)::(2,2)::nil) 730)
        ((Proof_certif 47 prime47) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

