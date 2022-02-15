From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo82:
  prime  914472872815737412272052274051133220962695320178528230781108573381253760213835741442146515056305648355364277637071005355444966732154065819920025800758037972672859271802457238409294152770669168678451582999670021372703232386804680944010781611844456434481655077->
  prime  19985542495240704279847844613997956327394564597727292363415152858544183670635825613123310916569125918802277285374783598750538045575721411569514450887843132328463831431369955067073886535483476483276598542536150084696811339741532841588792798639155868372517131442037097304829.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      19985542495240704279847844613997956327394564597727292363415152858544183670635825613123310916569125918802277285374783598750538045575721411569514450887843132328463831431369955067073886535483476483276598542536150084696811339741532841588792798639155868372517131442037097304829
      21854713342894
      ((914472872815737412272052274051133220962695320178528230781108573381253760213835741442146515056305648355364277637071005355444966732154065819920025800758037972672859271802457238409294152770669168678451582999670021372703232386804680944010781611844456434481655077,1)::nil)
      1685443213198596589207225202105128701370442132561872123903204333661193625897105457640280338175798419815170450635804070501989200109632631146098552049251031265733603509357807443930884785976970714754193942177161445209352582343954311998922836500944731293589494822564429395153
      2460007509147867529115054136284792207786985589047154465844616782453359248271818434716842468094111965472469122928751226883427557050230504351199816816739490440050928324670608771621314222791943729982278150900946050573558344711976593905548378970192743910279165107011663423730
      12999392412947771322755400757772962177374860630774853456780001791044059784341887727497181171905070067132326182734265220872349459422079338840716636662704488926194259496874196736798125573108027596638038331221520663103589397928089658018968090888618192967454992976742608583824
      8509534545761147855280559328913633562561377065242297954523025588388217401277421565206836080815661604957946333800021994298151821438136204832252030879962024886742481437966428888765058427314850868204941043221785534573642379554540936285149793320606508580922933454944725229664)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.