From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo24:
  prime  120475137064788461039917469635599127185463859508584559137978634473385080837484341794512688346019656642941025563320561931671215352864872456973449254819482786245415141343416540984041836027523729527746526138168337322484824634566176402655941266702950053948326063795617726579526606596148657350207354101494136008763652181917007994107111055284149943315934637917724872563545855599776704985848899043260367633932703912815636691741739->
  prime  17795623446114033157128289274813618274819237615732042399389100055332657060666487095151058220967255522042104768009206844051018562202376040364462136327895441321882761358118744101834787683297585136002494868921121442585862030263172722596380278170772818997935495491088668869936405811622797997510968931954612448414265686132266904034821791762838607161092348270229896180085250354908463579402303951205881008451935472909524109423208886097.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      17795623446114033157128289274813618274819237615732042399389100055332657060666487095151058220967255522042104768009206844051018562202376040364462136327895441321882761358118744101834787683297585136002494868921121442585862030263172722596380278170772818997935495491088668869936405811622797997510968931954612448414265686132266904034821791762838607161092348270229896180085250354908463579402303951205881008451935472909524109423208886097
      147712
      ((120475137064788461039917469635599127185463859508584559137978634473385080837484341794512688346019656642941025563320561931671215352864872456973449254819482786245415141343416540984041836027523729527746526138168337322484824634566176402655941266702950053948326063795617726579526606596148657350207354101494136008763652181917007994107111055284149943315934637917724872563545855599776704985848899043260367633932703912815636691741739,1)::nil)
      10954142509295372528797505102489819841559855631755467769422899943852078287161943856828397304527934461731566304020471949848197892567383979485234501248736103129288442366709261729095361548346886442723512672909692138681342466890985332081130502251230570438609455767553224709324846627239927721313899029670297913340427338128934571346335889448025656995330957983042264499570056942724319845555236054297130393648539483513968611328409362049
      211718545543881488815437789949842958990812053358412255339619954984703422755032102916335994355209624561542969867015765937994867150772898213240816845036706158181049447496918258771176454628181100111121738701814523189899751716442870200846366864644473706177299678651089595663693548451905809844749743386511550641846084347656565695235111357913349792897501211357789233647875083807538397445391587104678790122540996628014113094233908112
      0
      15449038015398857836697924482137320279778702808217241202977170218246711232955954222146354486444240246782718875643049627572254193365022025219305509598792847117112533535236313453990322876254757578448860802220721304958680942284806015288660543946646822534584826983974433677710086608193072877587639063565842982010950753601363249604941027973340418502164541885265983334033007186925420802385444645055380725770138415118806872531341009789)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.