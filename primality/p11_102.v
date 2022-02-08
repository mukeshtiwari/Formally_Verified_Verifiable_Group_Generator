From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo102:
  prime  4962039501995162731886116604191757407493807227533622990516861089462732647772552419543106843928965397874780788301491310496191->
  prime  1178821800409986819888720949424627423783488795430707746611109655324931157304815153582596776142300501378295511637731814259766501057.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1178821800409986819888720949424627423783488795430707746611109655324931157304815153582596776142300501378295511637731814259766501057
      237568
      ((4962039501995162731886116604191757407493807227533622990516861089462732647772552419543106843928965397874780788301491310496191,1)::nil)
      1178821800409986819888720949424627423783488795430707746611109655324931157304815153582596776142300501378295511637731814259766487057
      784000
      60
      400)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
