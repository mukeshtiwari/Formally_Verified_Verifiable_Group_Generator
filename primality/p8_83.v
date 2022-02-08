From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Lemma primo83 : prime 1659108721.
Proof.
 apply (Pocklington_refl
         (Pock_certif 1659108721 11 ((6912953, 1)::(2,4)::nil) 1)
        ((Pock_certif 6912953 3 ((864119, 1)::(2,3)::nil) 1) ::
         (Pock_certif 864119 7 ((432059, 1)::(2,1)::nil) 1) ::
         (Pock_certif 432059 2 ((41, 1)::(2,1)::nil) 13) ::
         (Proof_certif 41 prime41) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

