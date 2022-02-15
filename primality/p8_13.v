From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo13:
  prime  3503328808584912468324136705932873881221536441183910958764946180422713885503724815484665524866330643802591217176183950676268263644850215141981312139468908370177072792979353351094177360728445592990684188551803473581377586544238990893585682323298489314292901843890096027245954654495854722613333453434592369304413616761851168569480420327150690042665951340551593749655273729075126352060223373400703690262290274727624437741916169171497324185588367528943093814151399488745540168707397222949525859410179645629400189687400491988953363->
  prime  52939936705060593820485766783644379470276152940537022085047741574930086483145688893628997777885179049629547922303680762269108842854752532480185609684647862308057684346295933798869868611432417372054357754883393073613637076608035724826022767348436220738817870663220661016395580221315646795902997227362639986927672029246591233432367320261725369053511350702782857934488696694807973458296921375248411518502118235642792332231200406307337818287867015714798860389108057112394273228404704800724207893244163973900441097380614547195883283130553.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      52939936705060593820485766783644379470276152940537022085047741574930086483145688893628997777885179049629547922303680762269108842854752532480185609684647862308057684346295933798869868611432417372054357754883393073613637076608035724826022767348436220738817870663220661016395580221315646795902997227362639986927672029246591233432367320261725369053511350702782857934488696694807973458296921375248411518502118235642792332231200406307337818287867015714798860389108057112394273228404704800724207893244163973900441097380614547195883283130553
      15111324
      ((3503328808584912468324136705932873881221536441183910958764946180422713885503724815484665524866330643802591217176183950676268263644850215141981312139468908370177072792979353351094177360728445592990684188551803473581377586544238990893585682323298489314292901843890096027245954654495854722613333453434592369304413616761851168569480420327150690042665951340551593749655273729075126352060223373400703690262290274727624437741916169171497324185588367528943093814151399488745540168707397222949525859410179645629400189687400491988953363,1)::nil)
      12833301246047434505422798409140763784240046333171830574646337472828583027220683180471013458732732372288005555156006179373747049858835650937111114226553691550305452374454896231579096706716907179779046492762850218566216556010986608303831946196495008879620153255667907199375904489881959285797366004503974338984820369508671671329545669324849833548578516285718160053063771989958066142603418671751487141196040791434638211908272478532095111047837481021256751926898547214791937182821702550661532669850639353957749587536152722772581607779465
      1164965369938485433120988745868550889098958455631435315060202502688786943583741373076680867120993749175395170548775987245522348525262742598300651461857157225165482439805511558978069657563521584477033669592813082922987747622995426818577249170863994699691049434152999738385148610354372896013607742854462975633661062649495158994135448972608160290076388250189363019009086586321675363375779653101409094602101508142499052452557064531054487762466523657673720447806646193545222933906816822408136275659239893686747210927695084250206635860211
      38190976873297598349689285314747966636937395307186855360739467614370215520198081576103523341467945918889511911987051813375478771948357449837955149801694480377695269597096598723124625156029794421722102331042864075803086607060580427842729836499240777095780121568176079843926055001149481779842939279335010601593824073791107182166621777719113888527070873202204024402973688383883922953418083467007419692981684477619579151561601985915626300816186795236899030833503230799309543404574185004005064884334615911490255962540415107293823345732922
      14347205246304942697051753098683358526964865185019191074536112211799081788854234764188767212114664079134701411864103880166916679663442494245992973406025358353990711912356811185395957879993385541820302810680700934602632188385423626888544217320482134990307310235662389922662488059642709993060785145793618009071375477832396142831858502428465147693402980614208948354601939589589311747001248949165038092820753428343764205153142386197782198383668289676252771195772774394096577761750337944079461190875035180499288782828176916249513171594895)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.