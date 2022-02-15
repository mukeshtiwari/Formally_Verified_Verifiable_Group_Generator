From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo70:
  prime  121409753711410990638314280277243519429771488261648406733672113842216631414279840453237->
  prime  5225266104063507663140468223029807704234355473237687820689198503098368630661959013595000632845088311.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      5225266104063507663140468223029807704234355473237687820689198503098368630661959013595000632845088311
      43038272826777
      ((121409753711410990638314280277243519429771488261648406733672113842216631414279840453237,1)::nil)
      0
      500
      5
      25)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.