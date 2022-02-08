From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo73:
  prime  1129418830687425452276365240731978477148498222030058867262942715288309641424440252256071767133281680457394097915704911219621347421240641532236104437059998414378039200951383635607407000650740385936234672204061673805056573361684292528652699190413537791378676651954589157370327843205760254449868193410161082295161685370053396674459228141->
  prime  239440180362226258158946260130901633090913068565038570036345644469267508910905606799043982847557116102008920940423188293293384517345279726758650848970030843843387444719321138100122233470852464713963955987564696042105535102739086760019307208582180866855282950285718743726866389550247130541639013841745565206265924725353071593836669517630723.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      239440180362226258158946260130901633090913068565038570036345644469267508910905606799043982847557116102008920940423188293293384517345279726758650848970030843843387444719321138100122233470852464713963955987564696042105535102739086760019307208582180866855282950285718743726866389550247130541639013841745565206265924725353071593836669517630723
      212003
      ((1129418830687425452276365240731978477148498222030058867262942715288309641424440252256071767133281680457394097915704911219621347421240641532236104437059998414378039200951383635607407000650740385936234672204061673805056573361684292528652699190413537791378676651954589157370327843205760254449868193410161082295161685370053396674459228141,1)::nil)
      239440180362226258158946260130901633090913068565038570036345644469267508910905606799043982847557116102008920940423188293293384517345279726758650848970030843843387444719321138100122233470852464713963955987564696042105535102739086760019307208582180866855282950285718743726866389550247130541639013841745565206265924725353071593836668760046819
      8234810772496
      0
      2869636)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
