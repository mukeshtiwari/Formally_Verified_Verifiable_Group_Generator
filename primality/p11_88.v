From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo88:
  prime  10745491882848681776109799468261626514400472916550130009090986422609607922117670770430735063068482519062483289141800374992184214745583337159753141419469165865906795962476267429132221362901746384658812231237841->
  prime  216877648839987831767173200832055813689965102535737508940254551704778233331522902339132911342734318516483058899777559613168770269528409803284925166698214956002701974794133568189317072400964500828548033158813000567387.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      216877648839987831767173200832055813689965102535737508940254551704778233331522902339132911342734318516483058899777559613168770269528409803284925166698214956002701974794133568189317072400964500828548033158813000567387
      20183129
      ((10745491882848681776109799468261626514400472916550130009090986422609607922117670770430735063068482519062483289141800374992184214745583337159753141419469165865906795962476267429132221362901746384658812231237841,1)::nil)
      160170925534404622128304074904341031183747970439576995618823085677526054269885144459042265246996967758753746758960049058475915777776028574535841741104036964346794795682429781684089601874194789883808836730619002557040
      185058069365851144414619285496984930074249223500081873094883386480845142450950534075484721489790327702548756349011441052381204972033570767209744379654257948550834672213743200618579940297712290769536414085480379283715
      0
      38398046485203737206845848618244252051141571518481529785753853149688431399787968323442874957812922432318716782724470401001192095323551574419114975224158181118178423685933871174999901991157489231247900638212039890870)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
