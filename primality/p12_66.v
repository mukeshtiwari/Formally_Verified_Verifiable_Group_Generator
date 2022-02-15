From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo66:
  prime  46648202689424829158832367136135773120744892273088005831761939170059190251255417854467114389397215222063857865516171944242808008698914470342967746137437226121815644315261944252904789856359886232674111308537770625570771943863253378001580501284629285316829522912989412546920477173508994894269205731335033967056844727209996883557653319690855784136541016603->
  prime  99184558529747771458397802540366520828406762554124034165011999658704270611377343390728926938040286425301828911884585492519827861798662392482740916678296810282702777942373605707975892554513393667867014894325930253723813594294731520002425992989052813394551075443704371264544474369854655162298269777692938369501319432803257584556370279471105243397210812569247264161.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      99184558529747771458397802540366520828406762554124034165011999658704270611377343390728926938040286425301828911884585492519827861798662392482740916678296810282702777942373605707975892554513393667867014894325930253723813594294731520002425992989052813394551075443704371264544474369854655162298269777692938369501319432803257584556370279471105243397210812569247264161
      2126224652
      ((46648202689424829158832367136135773120744892273088005831761939170059190251255417854467114389397215222063857865516171944242808008698914470342967746137437226121815644315261944252904789856359886232674111308537770625570771943863253378001580501284629285316829522912989412546920477173508994894269205731335033967056844727209996883557653319690855784136541016603,1)::nil)
      6681907658602942766573512435484986002407303879960265057372466561246588120719563901936960684131263050067781811623055561282960080489556979387024502825216299370259610690407547096128001799174793237304366757527216576487111110654935730586919188237150545802790455293677625834610125755950168242399154356258110853028267909256688208370377037717108101442770889306416111749
      82104858198451475714158549427067624696486582823013793839805322898685345105898877334912952407044171053208357041094420157258376691305193775016090483472539246498266403151838557791431920878577393123087772995070009774063305374807226192069714150850620949171072807993286673492873752344553449391072918355817895162537723126515710665782539924672643272710647298048295651407
      17755678677466628662647105287461858501260158254476858955308155082302621123811962538160980802750143665901918376406957555919416960963311319941756960351563008593610858127622429722325003925795594941770828476966718469033528009888653082324265792379901998296164934834048031463135253585356420639247610999923392894140125487936672167076793988550849101408313141965131663526
      67050779810375704896649544777803768845319522269132471882494435652398542606322712854062696489161356396182869599732629678061178804891396164247448270820290398200829738498036681704307351879792972946773286999878530209128628113652445704584565979188068309525135777953328391015873609915607501688552991787778003894509155858960184945994472472974238642627522014942706030690)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.