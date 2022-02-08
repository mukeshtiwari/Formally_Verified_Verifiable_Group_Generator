From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo35:
  prime  1535418385602314291939172816515464117799323852203063804968118236374934248193253880352641782143645288725487275193392696723383383056099792413458660777999392413811023963786576246819751970739518101078409580813778754131444870351552805784355024991645093052507213326607655789287485930112310004834102256834083605843488840545270448458591->
  prime  331026991425545347456334024203834971012827426591867337968296483053017574304976377080747452379477062377482703608044305057381117086596778645587206511772001008063173900449428671363924403864132454617020942342613207608932730906429074847152277919613020198977077988776081942991227037531152120774478725712433794559520861559130603620989857169.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      331026991425545347456334024203834971012827426591867337968296483053017574304976377080747452379477062377482703608044305057381117086596778645587206511772001008063173900449428671363924403864132454617020942342613207608932730906429074847152277919613020198977077988776081942991227037531152120774478725712433794559520861559130603620989857169
      215594
      ((1535418385602314291939172816515464117799323852203063804968118236374934248193253880352641782143645288725487275193392696723383383056099792413458660777999392413811023963786576246819751970739518101078409580813778754131444870351552805784355024991645093052507213326607655789287485930112310004834102256834083605843488840545270448458591,1)::nil)
      330566567787357068296341135269108884014659711283327515329524375366732957671938349198988537257135324978627245435148414205254390716216703873487641098040321294752915702882056003807044368916289013417378819162103008718738420333992707003996648639886034293709948274337485950333195968072027836654189111674229748957367375078190602283425851789
      234087880444980247414479614023943251798626921665826693493472134415062315084965233034936074969287797996853420131526299796459401249796221668393615923520620584857011132815282690562222657898433391845851199255015721239509602924658340601019301229645967721829227724729072216781797941222917317188288979525655431086604107074572713451152812812
      160996456632145473784114144561834121625318446146368134010592678600114813581744996460143219099644397027460792526731085969115676378931642184888861959306297494095985576890385751942701021593106969496297147867721185351443810051285945819941935564751001296597834114993706334268445232091319111285930666345145764815459186955646911657731471921
      229850819387823627919516400889529136861989629534643055611254405666885648473257172048675097486305051697179027233693125903815565095159646773454889628508749354753681107663417078987914411396131713706077678598194896532636891183343522234714085706152105445820528193550448456792140756795086448677407350552073049922021572535005065380843879739)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
