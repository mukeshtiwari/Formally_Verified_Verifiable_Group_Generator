From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo6:
  prime  1052380712935557950839056867857649470386548921965890527591905536260716876546634499522222616424048674572466338664538744088635898016079536587543320698276007345213887363492850477155690848893814931127482038313077044704341664538916051181504902785553892612092554914181374389031172815967593781559704765776765715934916509487280726093037370451009139919960056796832492098819968063294434265449258490782270385452084902897133358260773269343439253755799613349356403078573373012605149069411153838821973432062616669258246610496659226016947593491090313403079062637364490213667114506275303673611->
  prime  5278850051298191043877645672031359081354379207119869373125340136153990706596202952956919432912519828668972118774208787839238793946150611715385813584584375272349416045678577757012092334208811757473356034828340703172582336518650421079700287377325237393195300982689934616942433055693495070462975209942661783926700780664581240571756663299049086223915266736755481457147316822235567929950430803316711568815399633918477306879084617250875314068397441517042402383416126905751026754826410461989698224792929548184952212388645667832075323441607218438649403762980213373254291850706251397034745677.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      5278850051298191043877645672031359081354379207119869373125340136153990706596202952956919432912519828668972118774208787839238793946150611715385813584584375272349416045678577757012092334208811757473356034828340703172582336518650421079700287377325237393195300982689934616942433055693495070462975209942661783926700780664581240571756663299049086223915266736755481457147316822235567929950430803316711568815399633918477306879084617250875314068397441517042402383416126905751026754826410461989698224792929548184952212388645667832075323441607218438649403762980213373254291850706251397034745677
      5016103
      ((1052380712935557950839056867857649470386548921965890527591905536260716876546634499522222616424048674572466338664538744088635898016079536587543320698276007345213887363492850477155690848893814931127482038313077044704341664538916051181504902785553892612092554914181374389031172815967593781559704765776765715934916509487280726093037370451009139919960056796832492098819968063294434265449258490782270385452084902897133358260773269343439253755799613349356403078573373012605149069411153838821973432062616669258246610496659226016947593491090313403079062637364490213667114506275303673611,1)::nil)
      2458368876632787184659626137162180262843486479932703499442274715807015859739269451826942077845892609110722101002831873318028830094296041136265926329774024516786486397870959042210101702901847563028385028165290417371589015376684957243496043452182217065914139249637480862587176969086406362344784400962028001460446930815818289012934515675445650803117799230804010835453111346554445385134488953809763094599589664332272500603169593323226320907784245784205048532636107005451331662869021181060973913347598017924686531328172454507027075994879670611333672503679374893550676256649316757295332530
      3388910102260503402223477232738643775867813728658183940558594316684551303020562589665249922171335858382122584640607993100051551499624836008882476012071641474927334098637261264183067175951543142208922535497053857300576748152611100386266381197210226603263569553104679428383067649208110876623605875327160982509887899619212570023258126122823588310496902031417664675170692134442443554855217936667751166198563525958871726469971646936269701203501611969398400291479643187881035743785408607566933933617263705226350628438461948550659589207518986661531456146118430702152149578240794970629122714
      0
      1423236415195927091015363642261937839291556230968171077400949880538596024966438451510888633366680531602678052012465477171059936646480310505784210196100873303712677792945682059495154150473265228737092105437739573705058640674558902493778213887225968824986550564871021767298226947684077499928864156544238669944849485544927421308398569977287661390723583377503162965136160585458562090136638633609981840525775087240249500966656317018345351422076349016754756155852470998181619862083324339955180091803572516384122695425543904302749667963663434185568865135494804763170039348554783850340836838)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
