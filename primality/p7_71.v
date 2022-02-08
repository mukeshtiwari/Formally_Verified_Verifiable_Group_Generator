From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo71:
  prime  53316071460953772812439412794347360011->
  prime  27536081720940645564258922786560755405418715277383.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      27536081720940645564258922786560755405418715277383
      516468692580
      ((53316071460953772812439412794347360011,1)::nil)
      25997446792209137798381800156055303644736804420691
      26374011528473540132171507216939074676542096180110
      25918545456438901408449706781162745511241873368623
      8523115099685976438045121621677330901890035621889)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
