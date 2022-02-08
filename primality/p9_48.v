From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo48:
  prime  276597050465788864197481098435774426171356368489135900920026087232570630705196726372384060045342866140581511342855529746063471661005567001303572769666675778516285456705309378091523294612649684880024538043887087114164290857210592073273617740652629391->
  prime  885467095088574767277890068130361876983675257524217379120369392770668801799608522971922995198495618604316045865258635965245785188553293484151437453303937681362144366560737923386060379580069511181344254589369914989231718380742307099626283336146232872205893.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      885467095088574767277890068130361876983675257524217379120369392770668801799608522971922995198495618604316045865258635965245785188553293484151437453303937681362144366560737923386060379580069511181344254589369914989231718380742307099626283336146232872205893
      3201289
      ((276597050465788864197481098435774426171356368489135900920026087232570630705196726372384060045342866140581511342855529746063471661005567001303572769666675778516285456705309378091523294612649684880024538043887087114164290857210592073273617740652629391,1)::nil)
      0
      1642545
      276
      4761)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
