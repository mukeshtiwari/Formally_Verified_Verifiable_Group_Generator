From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo37:
  prime  2444787679555907838729997064522039518144441129455191148642578216957535599558725489343778943821131839051869193701359487261185284972710990813178449825641540458551012398474342960572832475741439819990823838010558961245577724863178060990550546688224145046000714999236796111199086829549790952020387939394633648862546105409881878027807823008704775864306772328235612846469901735386733499384719869642535026748989446972922491097853639192805304754387459401286157191751944608814688030440114288370728586422059032171910303538889298736493396955883396312050101661221339796742651605594902621713498707480543600421339341->
  prime  15796968698786023384967650002441448604055606769122293599851384080510729743657109603414444863931861345583423224540203611983788845813037367318453608585434731615982322551605583821968790740846080241032688330243008611939726767848451546131771461369946742749138113959703566467755676359180849188779264446131091974372923363655629666182791664396885887312302042216331536064697266146053184726957307655282399634624996020309181102862376199711512843870262475917200336635467925856439309903985081025456950664835205821880105800063261808289420609524957557998745787725903441882303709406419712509665751539524380125727478394971087.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      15796968698786023384967650002441448604055606769122293599851384080510729743657109603414444863931861345583423224540203611983788845813037367318453608585434731615982322551605583821968790740846080241032688330243008611939726767848451546131771461369946742749138113959703566467755676359180849188779264446131091974372923363655629666182791664396885887312302042216331536064697266146053184726957307655282399634624996020309181102862376199711512843870262475917200336635467925856439309903985081025456950664835205821880105800063261808289420609524957557998745787725903441882303709406419712509665751539524380125727478394971087
      6461489
      ((2444787679555907838729997064522039518144441129455191148642578216957535599558725489343778943821131839051869193701359487261185284972710990813178449825641540458551012398474342960572832475741439819990823838010558961245577724863178060990550546688224145046000714999236796111199086829549790952020387939394633648862546105409881878027807823008704775864306772328235612846469901735386733499384719869642535026748989446972922491097853639192805304754387459401286157191751944608814688030440114288370728586422059032171910303538889298736493396955883396312050101661221339796742651605594902621713498707480543600421339341,1)::nil)
      11643071493350655043110057566967338654224629216817195971143857961143870470508071791464427534099852518026067680260958598992892858203605780782867722215038261279492296961252948296881503628810691709629148144035209807589433736934285822628337598193577090976545185738092890739982923081889505337762978925979091433975227893541134847067819010495475429915558887595057308514163476224935161804206436438566037215548962285500975632723936216151916105064727179251977042724586049841230609208932210927947623635692721706777017096117118861979138109467056494985437867781198650342728447130278021242847450489089285413366641888445565
      4939174580482981806368270777314644180803754176729749763040301116417164734816686150427058758893386540497254813303653715363562324537532739348542909808204891596650841078718361991115598379780824900231070753817067577075644136231135082055128822229392479966961544557823525740389241221524386439789753241612756248756493013795185204168128138329161000913337787232279796315152135603997624545032973732343954572235775863514408185810397179999823959791056267123719955591775708561520198180075607646235843932236366215124555588697017727290344635905950671597921817489170481704268753232518060128115363884975362601075846018818904
      7096888332919783222152980471934025493123636961208998097864056729861416902995577296445262758915823346145505686696435510423313628969915625134844755335586990186145852645826162599864764830728236517987979343967511558395036551977661114238005953809862047249486017718780108327975699451079422576280471506990295456475689820191822648115312326849581969918885045984571880500495338972035440657334987712324576872956142011490959246023293733167523033621978594614752813478135936081297475312725279237002892890983696614886916801298722485383530126471470573911625565793115015879313969714083059153598563978080021035332955247413508
      5826372227660545287326594877765584508649966521361681866185032702296005406984240006240007427958519726952044559135920145274632103973843075662657553193824533018085433766897538486228175004130055434911773902751542353929115670378517186282416891538842907843307391052407182636514572100377640023683215229842336407222239425137284788645422833522786603705959360905625436598300175204265018540466817487785978933629740890257246245259590473165632220892111241544711002423657270631182472717318037607244149248332468981197742856158656925242630238612043590059694553710079666995485735990341025558343436006378996302675366685321703)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
