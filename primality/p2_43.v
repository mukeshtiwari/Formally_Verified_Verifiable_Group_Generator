From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma primo43 : prime 401928217.
Proof.
 apply (Pocklington_refl
         (Pock_certif 401928217 5 ((1109, 1)::(2,3)::nil) 9814)
        ((Proof_certif 1109 prime1109) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

