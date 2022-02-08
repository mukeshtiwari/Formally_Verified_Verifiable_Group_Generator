From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma primo123 : prime 8574079.
Proof.
 apply (Pocklington_refl
         (Pock_certif 8574079 3 ((62131, 1)::(2,1)::nil) 1)
        ((Pock_certif 62131 2 ((5, 1)::(3, 1)::(2,1)::nil) 26) ::
         (Proof_certif 5 prime5) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

