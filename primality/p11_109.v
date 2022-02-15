From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo109:
  prime  112427785329466546793569936617465259159522471654646281537132026342815762594153->
  prime  230007461493870568627408422010489246354770505474354019494717033723718236182399645713.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      230007461493870568627408422010489246354770505474354019494717033723718236182399645713
      2045824
      ((112427785329466546793569936617465259159522471654646281537132026342815762594153,1)::nil)
      201640075008067104466176970642658030850126705618263556511678628426951116161636013280
      135739867776667389571610277692470331965584266794643060268244449827923867663587584895
      113361196509092441691135116982310122810013280791029627923706972109008730707185407647
      67112313957841036379476979791858883231741624879883670831691418059121346150677699769)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.