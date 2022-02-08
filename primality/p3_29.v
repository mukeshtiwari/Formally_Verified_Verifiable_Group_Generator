From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo29:
  prime  11480454402468068119634641470458562678228687338439025002826878096695870014508056701745508502726170190569->
  prime  852527063472876270495948840954782405922584093065143556719148912262602929753375764784109725366431687316289117.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      852527063472876270495948840954782405922584093065143556719148912262602929753375764784109725366431687316289117
      74259
      ((11480454402468068119634641470458562678228687338439025002826878096695870014508056701745508502726170190569,1)::nil)
      852527063472876270495948840954782405922584093065143556719148912262602929753375764784109725366431686558705213
      8234810772496
      0
      2869636)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
