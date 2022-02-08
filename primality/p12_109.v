From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma primo109 : prime 5734669.
Proof.
 apply (Pocklington_refl
         (Pock_certif 5734669 2 ((223, 1)::(2,2)::nil) 1076)
        ((Proof_certif 223 prime223) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

