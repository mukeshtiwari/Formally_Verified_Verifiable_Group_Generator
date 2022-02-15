From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo7:
  prime  3194209177084038882378730871970401326751584018777671396063564650774968674441556084216970150213523944804265912983872268672453583914423485371221325816797474059893025078927921624635112551248239021107086207073078751241101585148357730842491275574546916142483671->
  prime  30471072201145407649402078927428100255710913454361089285620681269822242745681014343373512889767855906313784961729998942449616807504937284553837516160926899044182334068141581003955524411934894264432617491102562435380499641643236104770234772728798766273771825373321.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      30471072201145407649402078927428100255710913454361089285620681269822242745681014343373512889767855906313784961729998942449616807504937284553837516160926899044182334068141581003955524411934894264432617491102562435380499641643236104770234772728798766273771825373321
      9539473
      ((3194209177084038882378730871970401326751584018777671396063564650774968674441556084216970150213523944804265912983872268672453583914423485371221325816797474059893025078927921624635112551248239021107086207073078751241101585148357730842491275574546916142483671,1)::nil)
      30471072201145407649402078927428100255710913454361089285620681269822242745681014343373512889767855906313784961729998942449616807504937284553837516160926899044182334068141581003955524411934894264432617491102562435380499641643236104770234772728798766253025993897161
      36370126051009921296
      0
      6030764964)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.