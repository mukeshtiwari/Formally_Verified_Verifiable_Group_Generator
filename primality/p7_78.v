From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma primo78 : prime 49295413.
Proof.
 apply (Pocklington_refl
         (Pock_certif 49295413 2 ((456439, 1)::(2,2)::nil) 1)
        ((Pock_certif 456439 3 ((127, 1)::(2,1)::nil) 272) ::
         (Proof_certif 127 prime127) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

