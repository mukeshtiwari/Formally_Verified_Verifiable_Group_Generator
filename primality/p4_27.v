From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo27:
  prime  5030827910136408479978637835040400497076994308403808856474098615698566917617264375599086388006494601336625330913059511966731430352792093781001121335361853442112351972192747914098551013416939849106139985478686765575839084554912175520452256959074768807061572480765300566178179527789280009171372461292526883305477394727232716019730794707769675243687825673847611139554114183729853399663725997->
  prime  508873273938207854158319195652171550679835051289353669641211549076525742283903908856223187233244935419800988847186882694946850911615273078042044424193186837523106514339268644258982533558136882676945507039848016198230603789537740042370633019162326425371154214601163040644525047395450685465571659583565995058474166898045542228566942199266655347953643098095888031197100926539457224925430683871147.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      508873273938207854158319195652171550679835051289353669641211549076525742283903908856223187233244935419800988847186882694946850911615273078042044424193186837523106514339268644258982533558136882676945507039848016198230603789537740042370633019162326425371154214601163040644525047395450685465571659583565995058474166898045542228566942199266655347953643098095888031197100926539457224925430683871147
      101151
      ((5030827910136408479978637835040400497076994308403808856474098615698566917617264375599086388006494601336625330913059511966731430352792093781001121335361853442112351972192747914098551013416939849106139985478686765575839084554912175520452256959074768807061572480765300566178179527789280009171372461292526883305477394727232716019730794707769675243687825673847611139554114183729853399663725997,1)::nil)
      434756546388043836726998536661379448390042254472717028160023417086368458638385306807635746305994419907181410907047521423448039755966315066436032399966922751583601034173446527204588096974161412951255890880370480359393865022335633452330468565729859409277124417254469619410030135007964867425761535060547943162387142120136947994251863011185224496425597632592837186199562023344468587679294109443784
      342506395539244875467037093997551646287918486779949301777338502263090423951787180728959709603415252974285814509474237901237664773332330578046037709169329757219554224083076345871965357493567570869956919311452274631269350998533882889444747847276347960056658272998342515952004316814077183419643922644057614682112057228931204884131342580897363554268044008199712771208268843009931822608872693332499
      0
      194439336853574557873986420567356144825955491598212262186158419738685317509613249182088790137902995195218196786541256963646632600809240091435129262909070606586587370328818195993084091462392714138729474585076474583670869644237734512219773061007323987312318186301823948152332416716416737510811680056279584876901782447617956542453331347725809366985787776158603318079182658307017647184537606266632)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
