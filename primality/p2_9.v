From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo9:
  prime  3873058418109100567808333078481029893164158741935030445541726724451032852224995071021646064347754720318368596351906902870742571218462036773913485857226581429483474878536476938601704069962365962714242665050705196370492644286529787756358540203->
  prime  50005525876275188632142093184571073155259526380330952221073144288320943730052030586364065955967647272351615470099628603699402371261803669426632493115888947298517545667851766448639081114845201368377648307357853929175569714417093907740515763407469491.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      50005525876275188632142093184571073155259526380330952221073144288320943730052030586364065955967647272351615470099628603699402371261803669426632493115888947298517545667851766448639081114845201368377648307357853929175569714417093907740515763407469491
      12911121
      ((3873058418109100567808333078481029893164158741935030445541726724451032852224995071021646064347754720318368596351906902870742571218462036773913485857226581429483474878536476938601704069962365962714242665050705196370492644286529787756358540203,1)::nil)
      49817994898814913070658542132214203030487391602976636740111413461541355764895621482043396488745391270063963445400685147556238723979182321821017597334708355337081513168270417998542799079534030510746038035909528979265376088878237652006083295244337121
      7735782039880399393747391666174917787349933823518955553590158033683241180503467704776892754758094030156884460825814615771352116117905921130023292558487270915152085773148331481212795638721534388707269180195779673736711112683474476131911883645142928
      19324955174368953516423011438710828056533508765537072513172155044612526692354092507470827040920337866838480777391523063569763500505067119316564646960915293002376959941060567101288834063541009250256102042479417833031967949296912202495673301723698614
      31253824586421249677003583357400520039706429939146742609086275957774579061653313867325009314360223871795599945515846281820840781511682487806500445437330157019933505714173657826881997848959618007132386400771281992780730336379864517144689708694626100)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.