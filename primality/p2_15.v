From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo15:
  prime  31153782231441930359540429388935178022282903389240481912608809942651469716498748618891510005962462687022032371182528519854914486134852663551784297283409553515548966678583935804809520860173088803269658303->
  prime  482839261601452347264044669957045415651881271678801191199192999165739444912854309374785103582169681101976241228462406200016508867806085358149145634463488500388382475499371706168897411467788618400156432681935229.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      482839261601452347264044669957045415651881271678801191199192999165739444912854309374785103582169681101976241228462406200016508867806085358149145634463488500388382475499371706168897411467788618400156432681935229
      15498576
      ((31153782231441930359540429388935178022282903389240481912608809942651469716498748618891510005962462687022032371182528519854914486134852663551784297283409553515548966678583935804809520860173088803269658303,1)::nil)
      0
      8192000
      320
      6400)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
