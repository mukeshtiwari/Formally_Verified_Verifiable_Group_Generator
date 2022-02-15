From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo20:
  prime  107961878217457063690634548265712101758287004893948773210397024984996352235989324952388506691814814430520244229616624933956559491813109374084608334410049801356874856895575927442237322236590960964293892414712844908364633496235640176369403782063369349195951930981077268414282569072248076977233343410950379857595040176215720220148881210436650861075272231505552207797030959567918016937055683974208277121325610172198825643575027860593757->
  prime  8432928683916437439806111488744862872901214789167658520447759158318597276286314716202115142752404601874869500223550888373169672219769221682516730422367680738424829630927266106245634336971656928838766484481090122531830624062497617952122325396745249708523516084036852973697097153681048503837621842634598809132867109455668726848509337523263433235350047678768681721439156526680721620411833583896464030388836902868924446459160996270204535867466665773.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      8432928683916437439806111488744862872901214789167658520447759158318597276286314716202115142752404601874869500223550888373169672219769221682516730422367680738424829630927266106245634336971656928838766484481090122531830624062497617952122325396745249708523516084036852973697097153681048503837621842634598809132867109455668726848509337523263433235350047678768681721439156526680721620411833583896464030388836902868924446459160996270204535867466665773
      78110244311708
      ((107961878217457063690634548265712101758287004893948773210397024984996352235989324952388506691814814430520244229616624933956559491813109374084608334410049801356874856895575927442237322236590960964293892414712844908364633496235640176369403782063369349195951930981077268414282569072248076977233343410950379857595040176215720220148881210436650861075272231505552207797030959567918016937055683974208277121325610172198825643575027860593757,1)::nil)
      3828594735294215638012495087688352671644331917193614624719106266922107050922679704866943693552990815740078260135539394076092096159057500528219490775021339179475490226543037308223941507647262729375376819288393675230174485003558947357865822764859614171011932175034087850935398505986817005714160695537751156123762984946320537941881698114485374364575958329627558571496620415938330801434559810133665787525779279427363618576155274203467581558217642366
      6847190681632289355246106584364839918747319706230203678913800064179638715807503699892080629981265208692753867190834348339650086757831642879082131628604168150685623926399975376023772153585895877600245590900034550765299664880353518234751337426724065896367891578428901366692460736689556973244790680110153024893327621093163489138924116446239482746154631834693325649141618263873046156768031972257063011812751289889079235106070050023371412078522329246
      1377663655009356404996088689188599228070618890542477464127147416963191914754933101228359347840909925777014244230673641217636243333613533033652731989030459194611184803417530607962063347641600477311499024502885508662432613337326995569442823233153235604766483051057227763721518517359873083605128063426733453028034951845885440540892462407699320881387375634099374784006999665559950739610259483589555876978231895314178724023648338010902548861374062631
      2943141591402322387852480905638113883756727978127639115136410090965798313752529300766320106272312653317405361000000744723762943917727541118883185976161672333567717037823041895169492138234895069475969387082332917788467154527313958659817709018619858513338299722695093753359261304233919809433355001371188323988063082251157968864529933010503085917968761629177694001995665770532015990444298821554020493216578854502925309595871916123160216105390523766)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.