From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo114:
  prime  2224424442783039323682545799822955619261761489->
  prime  157702795295546355891797783928828805431555932027233.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      157702795295546355891797783928828805431555932027233
      70896
      ((2224424442783039323682545799822955619261761489,1)::nil)
      0
      2058000
      280
      4900)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
