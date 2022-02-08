From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo77:
  prime  27510328986274436925985828009->
  prime  18351644895677318134126252882148171411.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      18351644895677318134126252882148171411
      667081986
      ((27510328986274436925985828009,1)::nil)
      18351644895677318134126252882148077331
      9834496
      0
      3136)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
