From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo7:
  prime  1525074332948160176080677360386690908786098667259232669280008829461267616001825088028482831479330953445329527441216852385710221716339967529388264493615695592183807151757307574031532869685807916826231951890056020648949730734095287516153030765711961666015062489371645484613633668512066292901460188589041746077307526836465977884552757702165433898997920648162294887093824403402497399711225065906468212216092247972230015316820138355796588673659937338080421215210405396200764335622150495205386257398586490785658526954549092182364114052334836373890680899185856089->
  prime  166782427965780054695577387944651153576265872326808467522064944471614800894412327984512136033214603017648112405558853455404337446102395251647536365121653218637557218142380900728372944809282412202468424200159096869149189747227884525442848610532290207339893772789931067039861962260679228297913678864516757072845138525727165163955208806013925971549212734699779304323749292173244130913010787089885116861979875531482217081179681309990151726440202912099895075587270040225804865226859492739160577188206684964040131249065458912311437652263158151530168433706782598984752369.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      166782427965780054695577387944651153576265872326808467522064944471614800894412327984512136033214603017648112405558853455404337446102395251647536365121653218637557218142380900728372944809282412202468424200159096869149189747227884525442848610532290207339893772789931067039861962260679228297913678864516757072845138525727165163955208806013925971549212734699779304323749292173244130913010787089885116861979875531482217081179681309990151726440202912099895075587270040225804865226859492739160577188206684964040131249065458912311437652263158151530168433706782598984752369
      109360196
      ((1525074332948160176080677360386690908786098667259232669280008829461267616001825088028482831479330953445329527441216852385710221716339967529388264493615695592183807151757307574031532869685807916826231951890056020648949730734095287516153030765711961666015062489371645484613633668512066292901460188589041746077307526836465977884552757702165433898997920648162294887093824403402497399711225065906468212216092247972230015316820138355796588673659937338080421215210405396200764335622150495205386257398586490785658526954549092182364114052334836373890680899185856089,1)::nil)
      27377973448752686642925052000682381511237212875426183141697738085261400736604919341684559789475366447954470291370646151889843694141373459783301561038560045926514485599705600135375957748057105120923516427455634209768237790476050419115179998282284017345432979803882967282360094131760124668457618311185804848833357732494329376242391449177291298200995013989055738067022896881230177087413872148974265979217070803503119344994122036984097035779116290916586521593858265116626261590900725076930665524697706723505412767915505315648063436528804313806833513365634059918475210
      104561602847057796387901579905022587002451627039484321265307089509475652583254580215416841538765173507485173191414897297623369267925396974970105047396648880666723313140017099588646971748219619027505779528144404413286704394005117068761580988145646711573042437113689745611557251096317873896175764469080992437529566511292995641536106557679405878193603448048764676189465258308648232033033733938746523794509774126738505846224067900311530346951354253240814021752617411212973141755116640924181163055298223671650156215050241996565948723358499777084913727597348660394302566
      0
      165497716635743039239286465353206743694735512454194766412745152231988795849657308173309819033250465811849389162208190045330741777393040156682220921244043061872611180699814886864457690252114542644339435969015331203247961482629238087738326276132826624771312135204636072967583832874263885636880809377170513384095491579266717657550417321086414902538145379663612805984113508548719667816742707002546490376739287780204631874612695766104588045144829800710641272159704089099154740423252022531447591586578232377159532831078951179860013527334100827246811352504823116444050372)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.