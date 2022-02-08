From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma primo42 : prime 6701029.
Proof.
 apply (Pocklington_refl
         (Pock_certif 6701029 2 ((127, 1)::(2,2)::nil) 998)
        ((Proof_certif 127 prime127) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

