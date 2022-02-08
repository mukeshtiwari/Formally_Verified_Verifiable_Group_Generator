From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma primo80 : prime 208870589.
Proof.
 apply (Pocklington_refl
         (Pock_certif 208870589 2 ((211, 1)::(2,2)::nil) 1028)
        ((Proof_certif 211 prime211) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

