From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo73:
  prime  517887315990776888002183434152551->
  prime  75784523395175176424940543689850234846660103.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      75784523395175176424940543689850234846660103
      146334001732
      ((517887315990776888002183434152551,1)::nil)
      75784523395175176424940543689834623977966103
      23740460778072323250
      202095
      4538043225)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
