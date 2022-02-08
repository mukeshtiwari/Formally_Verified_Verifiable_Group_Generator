From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo71:
  prime  10383525514393396047720918927005572798264134730750784074798762120473844741161460138863300166423877178869036219384780928054046500239376643897332224201550796621446295639280307701678028681406192851248084711278776574257313028472427985005744883224263175517586018931179273132573422589250088429754946534674650401678157534490809676153686000393->
  prime  222424711307855776830262644131198121746008322821299690339295943415196412816842804428172695806535751419276514462903947678954093415153587139149259990195793549623204453906377078359645295067218007262580501501822262916571214314217082706325270517179602374250537905197920296354258804512154520181428581279067160972744872798700686617717979756849103357099523209.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      222424711307855776830262644131198121746008322821299690339295943415196412816842804428172695806535751419276514462903947678954093415153587139149259990195793549623204453906377078359645295067218007262580501501822262916571214314217082706325270517179602374250537905197920296354258804512154520181428581279067160972744872798700686617717979756849103357099523209
      21420924039675728
      ((10383525514393396047720918927005572798264134730750784074798762120473844741161460138863300166423877178869036219384780928054046500239376643897332224201550796621446295639280307701678028681406192851248084711278776574257313028472427985005744883224263175517586018931179273132573422589250088429754946534674650401678157534490809676153686000393,1)::nil)
      205794487074942527941129679716108891204788254430308225877945945518742012900451287720946632995407307157594653333088188623601057666378118419769993917063486516340558009103304574718433786232124508372268376928041082713921266112993193442052823168729698007478225271352578049304770889657859881638551897190907668146883569240417012082137406700162077025792596149
      194636334737284110247860756081075937709283370474097879153281314371860572692697746000738199723508929868568165684991472530413995715521273107267871922986304743276239089541183511568833822549809776319806814122040637236577308743725003183918272185424659845999150998536380503880709604323263444235019119318796564367646299081407012602983906349001058489838901965
      121351326991886320857841878073779717527889533543306494194984513913050247494942834859987264263297080742186515227797122259126514395960806952143872080433555286860115536764069754854448170266177270950992039626901641769342741334433466610669935521995601062592444583808616781441916280834835813012581336005119879346336367121547622360904229679142044855749988157
      164007706166145264613567564128276863112517489357028769007135742010678280021045500054165112733542975499565513480870039643218684030553587363385711598441329431995270909338017083589709175323559417661150838793552578266994606075477918385135207581829942852061331556383166968876033166935596798861967540687589513600285440266045270605271491091912467168825561634)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
