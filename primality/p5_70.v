From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo70:
  prime  17490676868098962025319766638638643964158174562791441->
  prime  1807049280627644261645911690209694334280796037093173994477.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1807049280627644261645911690209694334280796037093173994477
      103315
      ((17490676868098962025319766638638643964158174562791441,1)::nil)
      530413165722091265342391078985371646969492576872213382078
      712965281432908135747007179594851753408596390197565689335
      0
      1245039117343922923594824054772492635989798291761036928621)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.