From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo72:
  prime  93254297971168269009783050334130157535693355032630114413799742408020824725759843860018652488035594834857414626519954907313587871237381255623509306309272007928327345226054160279888484715881493434314831116573099429962982086346771950929041603503747615905375032114262317122696878255725269503094242072431616616332675067516279411859->
  prime  10383525514393396047720918927005572798264134730750784074798762120473844741161460138863300166423877178869036219384780928054046500239376643897332224201550796621446295639280307701678028681406192851248084711278776574257313028472427985005744883224263175517586018931179273132573422589250088429754946534674650401678157534490809676153686000393.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      10383525514393396047720918927005572798264134730750784074798762120473844741161460138863300166423877178869036219384780928054046500239376643897332224201550796621446295639280307701678028681406192851248084711278776574257313028472427985005744883224263175517586018931179273132573422589250088429754946534674650401678157534490809676153686000393
      111346348
      ((93254297971168269009783050334130157535693355032630114413799742408020824725759843860018652488035594834857414626519954907313587871237381255623509306309272007928327345226054160279888484715881493434314831116573099429962982086346771950929041603503747615905375032114262317122696878255725269503094242072431616616332675067516279411859,1)::nil)
      4825113221094282561799529786229973535061215629709988532876788861136038824945360504831440607237090682144412365329767504549439079423180966049673881067292538594679076263741651584431699010626611105611692484266153181908858288563535731759909190489720267787336512617882712127190455009022944548779156910792349768465493345123729990403936489659
      7268753164112065645967991908403760287272027295756118249311768318283179832812063758746236070252651599314210518547872764694552338632574246234127878889616327150111522801300375882962840251770800394026980340161739597073588483573110270817086631714136641668735465808768384473718585938247528519609813701807070694475550387693130876201326950794
      4008331397870744448507744986801432172137862930456420960659309761277056143341258797995130655778285281619171095336778453740089989704305032269419426792616834250346806508253824081483144184496150824512144740229360723604887693434481511479442840542168698382394118096038873908129527129048047058346428593455474060503942019192015706979296411524
      1445784223534560658736131885423677723458742388226995161939603447108273452939406999566838186231896115273264239640365071230082031568020968835676388693919764750272477719305708371655539919926434149569721617950240081582677973127493863203820486560568639978298154834533703402337906800146475878704199409102605511202952155990316353571618670703)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.