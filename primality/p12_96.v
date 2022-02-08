From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo96:
  prime  515456920762542147014348566233958334832657844333963413162593022339041988474423653507965609850689->
  prime  599253962655339488107286578520619419832090941352064935893293135357565595548628490756387133333616627590395841.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      599253962655339488107286578520619419832090941352064935893293135357565595548628490756387133333616627590395841
      1162568467931
      ((515456920762542147014348566233958334832657844333963413162593022339041988474423653507965609850689,1)::nil)
      599253962655339488107286578520619419832090941352064935893293135357565595548628490756387133333595881758919681
      36370126051009921296
      0
      6030764964)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
