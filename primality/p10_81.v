From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo81:
  prime  19985542495240704279847844613997956327394564597727292363415152858544183670635825613123310916569125918802277285374783598750538045575721411569514450887843132328463831431369955067073886535483476483276598542536150084696811339741532841588792798639155868372517131442037097304829->
  prime  1236485528638047133089906298423439560019574317096789851232132092205270099518567894858326123097215251470378093368852486471097038341724308011901155118055901528832420374302313106137119639577483217874900048591706708680647246526335360463015635872189430029094486319503203108719344483.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1236485528638047133089906298423439560019574317096789851232132092205270099518567894858326123097215251470378093368852486471097038341724308011901155118055901528832420374302313106137119639577483217874900048591706708680647246526335360463015635872189430029094486319503203108719344483
      61869
      ((19985542495240704279847844613997956327394564597727292363415152858544183670635825613123310916569125918802277285374783598750538045575721411569514450887843132328463831431369955067073886535483476483276598542536150084696811339741532841588792798639155868372517131442037097304829,1)::nil)
      100526577286481019782888735792710435950716902938664936639711026779438512308764696948832134586452696960274825996839570362069865662629665342809338831046535908368018086728300827735057224905805378192432540818213923939081300528688360233053894408458066223216836776853767803301780100
      866185241281299078326707268043959367406945012265004197311917983772059576240278923191415104066726265581390792887359901516371578789000261862276814524287899999125473232783536271908497624487574795838623504481731991014864377591452850535533479031915631459466943621654882836605246190
      758021016897934387964745951493082472757497053434911253233613751584820164603672443187750014873814521165193156420113082365503709068435390496217753071611309389938540606143378172897781959646255440515814654209622053863015285990989397947923321883181534367019976973060246261213539827
      1094651356197970370804522798338827185181874413018418532256062643725801219334497605224736558544658462716505784796324530641918542119321265043832913956159239977083248695902727025394767763664919869924321471698139580874859031285990623946351389296095333429851327411235285328191054408)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.