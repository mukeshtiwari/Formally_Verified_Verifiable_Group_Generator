From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo48:
  prime  8626261979162835791859378200434558670067328384640739281245826520603742681380243826296975463855602884650348315907630486332102255598437505892428632718990024710221234409902870487628340802200814495445037796004196151851291194950501073342793998989435054216224450970708834565621510765692770523175436466182687891283363165067685017267159715921789312899724240607627573149936569288308743148817441250402557198660021700764272249986269683291979493830133988028351112479535766324811683783689779823699589658696284576109985563527->
  prime  20928605500745914056419630420984304517383848760396129607194562012962770306430678559170407021633270938594442566639297704414629887420149154920915727271177648450703247863585849233559499037259506088123978448775580493814010132629158179090619660648217856786692951723255829750384778038382023431307885110574430549065569615261776838697262038580438692889634252671061739156290971639262392481816988233418780110726101656011751985875305694058218349275672714231941076264241556080286855122445128441837832606246025586627814549830412971.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      20928605500745914056419630420984304517383848760396129607194562012962770306430678559170407021633270938594442566639297704414629887420149154920915727271177648450703247863585849233559499037259506088123978448775580493814010132629158179090619660648217856786692951723255829750384778038382023431307885110574430549065569615261776838697262038580438692889634252671061739156290971639262392481816988233418780110726101656011751985875305694058218349275672714231941076264241556080286855122445128441837832606246025586627814549830412971
      2426150
      ((8626261979162835791859378200434558670067328384640739281245826520603742681380243826296975463855602884650348315907630486332102255598437505892428632718990024710221234409902870487628340802200814495445037796004196151851291194950501073342793998989435054216224450970708834565621510765692770523175436466182687891283363165067685017267159715921789312899724240607627573149936569288308743148817441250402557198660021700764272249986269683291979493830133988028351112479535766324811683783689779823699589658696284576109985563527,1)::nil)
      19055823352149190009847288853763897415010770430527585547047056998067205781796612566039475116286586564977545114480129826816987176007736654843907529201761235651621835684199805881747331838398019606005663174890970889711170169118905682836736170733098727402655357339464679489059128790273362546925016568442577383748700821943259058444028852832924079199698076005632970441227383390224653949484967689116929991948159213632158193183738105639460284642312766286923591062965697008660630562815551963423989853402183867622529141688120781
      19342554534571901356154749929181397811605052951823139823767245165665419616209124352306671487742681777770375258743501259852388744819178113237607111057191972585085208688706100805984525133182994790017411021691676012286468545809617846353715556241704757606479572846925150519219305347912361874591198204109718682398352997840749547017636311686208995603723555443201660724136281732708899721078756437088762168845387655348085665882695493868192140917750899506973682988137668571721909060593321954653599587157979303642208898370357999
      0
      19628750670423396274904585897038225180213569579857454309850489074504520597087604305767153354855009127657944955215438910674552475826916114741889744744620834571118824273279466181504505245452421932900045964059058018422265266047848944971615693864213710059319905645794073285608489005890986189846591002989415230726252788439311623142614432158431085475665650884030046681522100500945934396310192234499034892900541435993957959985226954594508528482020089978211506350081093171765980860709587529878462515370722246302939016116636139)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.