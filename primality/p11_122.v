From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma primo122 : prime 2156196199.
Proof.
 apply (Pocklington_refl
         (Pock_certif 2156196199 3 ((367, 1)::(3, 1)::(2,1)::nil) 1510)
        ((Proof_certif 367 prime367) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

