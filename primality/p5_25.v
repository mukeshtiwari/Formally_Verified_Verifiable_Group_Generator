From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo25:
  prime  14125028483383248190939806266682244708868858834906168627937939355242912997968227022336092297104213868256370162395959129840166871677620319511954528767120707077046341962360177458599719584821708999484256867197953595215852912580791382352472656008247068717524190843406866071971232627023162552988491485793137882426211737153288206754540235591100072390284687783931335374845194122726220729739705317533->
  prime  477129337140202740641755715882259544020881182584295470083115653480750358158368740587490861703883240255831927715573103446870996758398336772794312027224570364355548385146564434374039927855692508293580086553715891118109439513353471106271764436387120959374872154365704913367046140235482796697480419460989465211501360418749552267546785761362136145252861609894083158534850640098181737685823228613741321.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      477129337140202740641755715882259544020881182584295470083115653480750358158368740587490861703883240255831927715573103446870996758398336772794312027224570364355548385146564434374039927855692508293580086553715891118109439513353471106271764436387120959374872154365704913367046140235482796697480419460989465211501360418749552267546785761362136145252861609894083158534850640098181737685823228613741321
      33779
      ((14125028483383248190939806266682244708868858834906168627937939355242912997968227022336092297104213868256370162395959129840166871677620319511954528767120707077046341962360177458599719584821708999484256867197953595215852912580791382352472656008247068717524190843406866071971232627023162552988491485793137882426211737153288206754540235591100072390284687783931335374845194122726220729739705317533,1)::nil)
      457023004902248829967152082430020814106782137132834202710110181305114495374640246951140962618171735093935026694068133226387569265101060853712651775987376857192133394300542001758298484415852575198271909580049519768472712545226088672586034677794284671126133768146842662665668078529123201933122580312773679212889306518522124896002228658419351024746435536569144368727099569643771473801490536911734334
      354454219827585049549737008656264580636388552469680573592446736078541019036780164796786826205368368721994376516058631023493885605168006099284975873269628283423598814571549864061941883247035601889086462612415417640719965722158228999882103787153880241716416626304308184434457352191870465769825193800869787590405728436636434245933820692662588655513536051903324537123041130128418379839450507041292530
      0
      75245686848015725713547206410854416586365840794409561590979982803615934656604786104446038288342507389345814488155964250634641856169235893494625178341181732032359206459645502880023045486422004194877418282611685644098162598830430136038931914474582368467621802225792513592330764315328811145066492119299066872565177436271885667140938784347219551056636435097828464069957306767393278725689473590512439)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
