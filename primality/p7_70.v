From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo70:
  prime  27536081720940645564258922786560755405418715277383->
  prime  734552515987812661072171025771831165337364497400567819.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      734552515987812661072171025771831165337364497400567819
      26676
      ((27536081720940645564258922786560755405418715277383,1)::nil)
      0
      221184
      48
      576)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
