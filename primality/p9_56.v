From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo56:
  prime  4125828283552019417090094407332843815095581633782574773899195163457112066293667953940689022015952071188799761816024514413062235670743801963487449960580420265255445939971186835477378976304362656553->
  prime  7246625587279487722802884534025125427033863848211566963270832063140500293625900448094246105400800156215029926305018212169305554366351321532805412994490221029424697795192078096671601107675233482035594879639.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      7246625587279487722802884534025125427033863848211566963270832063140500293625900448094246105400800156215029926305018212169305554366351321532805412994490221029424697795192078096671601107675233482035594879639
      1756405039
      ((4125828283552019417090094407332843815095581633782574773899195163457112066293667953940689022015952071188799761816024514413062235670743801963487449960580420265255445939971186835477378976304362656553,1)::nil)
      3752789549826398133242243258616229659511334862812542661552351132357111151577661977328149953581337163388738950557942595891406755552444332841543288451313641176179540487846274311286735872447688130417251793881
      377257847183011744432830329267551910548490716561313481576033281961284679653620667608040783512915325612609492054540647202886843477805730034240658187225023043884058652006712415864794511513396324099093585002
      0
      4232192434751589540370481128058650169835959044786194110091774092339244918169208824352714257154656011307706686321552532975137856268158443391418244482843870815010348021601204153972889311820649985981477370997)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.