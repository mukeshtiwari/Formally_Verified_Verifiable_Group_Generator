From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma primo80 : prime 2816249641.
Proof.
 apply (Pocklington_refl
         (Pock_certif 2816249641 11 ((23468747, 1)::(2,3)::nil) 1)
        ((Pock_certif 23468747 5 ((7, 3)::(2,1)::nil) 1282) ::
         (Proof_certif 7 prime7) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

