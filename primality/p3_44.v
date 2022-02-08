From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma primo44 : prime 64035967.
Proof.
 apply (Pocklington_refl
         (Pock_certif 64035967 3 ((281, 1)::(2,1)::nil) 418)
        ((Proof_certif 281 prime281) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

