From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo29:
  prime  11170321933790083025328053697660515335125638742352786237940357783904355728057567691724794564999083052424411687860916369466969387537546915432217964365240455252283377616749452240380127429948614211211936600983216558669723715399980961060673928230237455189703111342281569677539964916933265195473572301870621765883523962361219830773570514780968330166152433566553667146250308179305760055363651084662444948518628031041169065255317288012312189211370474778194627564470713490049138961917932535279448752592016396760828144138312828447793086992796458419577404694373727118562604192748230487377389215527135683432953883289909551969154391147554593143864241867848563643621->
  prime  363060350325446182628142176077605136019749919049583514740799759094034100066433062241872986204761017160834181444720336129347677502765708406074666823494920551433511859909687315591945708397243887376850519726701528763258736894937292392053145848994814262715513777156221617857290418842166046167746614929883775136508917268127785297924004058163411611560363754614341806384968243939269034033348185293243658609902637762479881248758683577696276004194703476419358480155107856190919450543076190723048617917342074547160746442796723214003984151834765687755375238165780289896930990441486644441244171142771543125167775311857343439929595565028898801512637205759114703280126037881.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      363060350325446182628142176077605136019749919049583514740799759094034100066433062241872986204761017160834181444720336129347677502765708406074666823494920551433511859909687315591945708397243887376850519726701528763258736894937292392053145848994814262715513777156221617857290418842166046167746614929883775136508917268127785297924004058163411611560363754614341806384968243939269034033348185293243658609902637762479881248758683577696276004194703476419358480155107856190919450543076190723048617917342074547160746442796723214003984151834765687755375238165780289896930990441486644441244171142771543125167775311857343439929595565028898801512637205759114703280126037881
      32502228
      ((11170321933790083025328053697660515335125638742352786237940357783904355728057567691724794564999083052424411687860916369466969387537546915432217964365240455252283377616749452240380127429948614211211936600983216558669723715399980961060673928230237455189703111342281569677539964916933265195473572301870621765883523962361219830773570514780968330166152433566553667146250308179305760055363651084662444948518628031041169065255317288012312189211370474778194627564470713490049138961917932535279448752592016396760828144138312828447793086992796458419577404694373727118562604192748230487377389215527135683432953883289909551969154391147554593143864241867848563643621,1)::nil)
      292608994869826233004899189936518616432618312187557102860973369098170712927690914078483539836871436117434885588427709391430923848792694659707405384443339016343225237858000759498649071226966659627783710714308051343274925683733077051262634070278650739262930080164272562662865258639648166264624673630831289186727309056474899539327219891544108228385343937614863801774014312380834153238050665761345391004709779057204260986717992636805989402309443157115862147698136310416842737326102158681055064817017253802115712825885727782979688808982414795310312413173914460570736584511026046294023631981976312461972428941106377648653937040495379098665016353733946309951054627346
      153807039806451906331563086385194270293964738111884196544898811147914296749656906366222559786505267375520375065197116812767581379742498560707481758596432575203984713877284054750708088678940948317484915517155850373075081305046899351280294866473932172948573409661125669144984895002255692640314729057797675742227505254115487943228794970186746500654659956777471476896057655838929201404644179201614449484601724202819243169137500479977240817249256772456376650985056230393636494966202014978736383654842036211750552399893528514963348457477020347793782072144811573629279865409117611868895743356324521792910556921975485071915877636174682461526379103424054923518673697156
      0
      171339523382544197525326534917835426847770598724890566552087324798904070634544164752468931370596835316490709870625245730325359041169933137656719852961215242447394121453329923008555204058742575637093799557819803328070571451585137238500945325527403636920602704593961612960658884931704979644735451464683602411774166224257339034127457034463167977095510340470442174857041923245393260877662776529811547008918825951759042672971936467965920272810399078097810342928447378140481490760619137228682210683976128982189570295919368402836520198591129770164872571142893290454940108804000503310740226694858897599544560256400699348382480950288174154430917718126054345923501432479)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
