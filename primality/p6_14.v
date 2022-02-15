From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo14:
  prime  2208309080398159731041103142452290692295752217561841152106896044527080208996872728459610533454589732960941839142258674441443905289999788963005735033550833264969964983296303647034331064412171483830109102880872036678360213839955425529078942537408055323861881433630613654664313974525069935192824003935002565972015661743179653928398024949123536857994261309014981823061723530948412286138404996517402347338509508305251100732660188161539326430090446413673752695740810215786319024261854129889368313330937->
  prime  3052885721432757512816697203695739076727031836177237548094786864340640143248562690949902420416431394690785889289572073516271892643781368251063130420072483650490787971017908162057199117320864116506869649714073070594145791063901737844377300426609915714645419438541956104509273537271981541167776434552699155987996718399485907723623687482652933659119768730187821315316878599351485016444832075149144551997522424472856111827340608782713856845282110085773648059036410082255918587231591991248422860237964116193.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      3052885721432757512816697203695739076727031836177237548094786864340640143248562690949902420416431394690785889289572073516271892643781368251063130420072483650490787971017908162057199117320864116506869649714073070594145791063901737844377300426609915714645419438541956104509273537271981541167776434552699155987996718399485907723623687482652933659119768730187821315316878599351485016444832075149144551997522424472856111827340608782713856845282110085773648059036410082255918587231591991248422860237964116193
      1382454
      ((2208309080398159731041103142452290692295752217561841152106896044527080208996872728459610533454589732960941839142258674441443905289999788963005735033550833264969964983296303647034331064412171483830109102880872036678360213839955425529078942537408055323861881433630613654664313974525069935192824003935002565972015661743179653928398024949123536857994261309014981823061723530948412286138404996517402347338509508305251100732660188161539326430090446413673752695740810215786319024261854129889368313330937,1)::nil)
      647513329485819734235229234780938743817285764278543260301842434158744014855878937517382654825759861381485473276396089380193535762760412439538289604419801687883443430318996905150745801002666585463630617226507436844168913163712650107268543853375061078210424924823477314962589284055514876186292240937241702053367712069255727623008050807200260693166875167433827155097832948518354966517880549948865467237565559482772500771537625540549199556237778532588585417575919275454802008482024943373851729809189265545
      1055511608229186903176467925340453177117537365715356903943497770831426949393576524063407914207467980317431633384683372656168578990318799292827802653898236790648874542933320992055038823681670751545630497271253143051823868920235114481174788937921653324500362305293166922442504034152451892444205358711407619195556552795382036123232163416938536738644883823914268517154779357282186145195595525310963075399164478663972206547496119271900403997750695508357452153694502235753662939006282624767809074111275834804
      0
      2607832892700698339286693066159772109196768157060954196589146051990776838682077074565709278527841240919600307507645459873451545211640028086726961537249010129974264230377794529474265461214199623369296109006489453841877122026778556259539473468689270339422799372559977741298269297286349911073190132457437708761003508473588011863810132154045033727807838641709030649651093359857857463675002986096513443532854665374863082183162916135488419805377486815252090780910518085270439452411772199028416201445804608237)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.