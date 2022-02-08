From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo16:
  prime  10057528643567067072391855391371860218193293047668526706151595038097256743118253976868153813782771585394224574460200560305752342467544783366473335876391755300234358997189558808379958794744399848156613007037604422736060512429609617144122578046342206793546574364822615625666499490377667631314702784945042981997392773015982193238458979519118642319441074805655291631419006892722884275490148193589207213273917485540953017497686849657634656291423220008163513885286403644768832548638145131386177863->
  prime  538550486277085740525366680641788999103596262823506599534299459504993806823753145699359032266626070083104543288620359402692120682109620514924547716173149321061649221222509305512321653582178378669242156687842604024247832259068306169216331686647486183684414082928544724132239590295061512034824366866889288638743299974879635571066117012995757409667851269341919942690593786781113475850046064797779729243174227825044779923833571238749559702402245622860947837068954411038018101279185732288539751282251.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      538550486277085740525366680641788999103596262823506599534299459504993806823753145699359032266626070083104543288620359402692120682109620514924547716173149321061649221222509305512321653582178378669242156687842604024247832259068306169216331686647486183684414082928544724132239590295061512034824366866889288638743299974879635571066117012995757409667851269341919942690593786781113475850046064797779729243174227825044779923833571238749559702402245622860947837068954411038018101279185732288539751282251
      53547
      ((10057528643567067072391855391371860218193293047668526706151595038097256743118253976868153813782771585394224574460200560305752342467544783366473335876391755300234358997189558808379958794744399848156613007037604422736060512429609617144122578046342206793546574364822615625666499490377667631314702784945042981997392773015982193238458979519118642319441074805655291631419006892722884275490148193589207213273917485540953017497686849657634656291423220008163513885286403644768832548638145131386177863,1)::nil)
      139967043569813204601289723750208657753268132999100177902413289719372171394227143611107104205575171705969634743194989258113174200864153440287897325704698557539802027190635605116608670080487437843019788934956272928402363990915097974820970200178982325860015490262298714338455837319615267405360214385664667333581430405063513096882763347273393823295053497358317347580599321973030747447189549818476753136081645845715158732636152777489458564279497849401813657772452926659286716247009952672435505652815
      247622053668401714425533644297007225329343254705355701640449505003655653009443473700787607270084441553046243646901074734452592036307436773622971350618371986677492048238858294407600083136791298599136706297732225139012390162543849098250382954179821220150178176729249402077438423725278331661888440609920706132331719509765612887869215058703144185898526339355938489516584831411656937845368048119160330755434732852377188389525012454377200109381491945647660840631394394064016749053096708235766909935557
      212567275039195671493124794949055536337128965047643373243996545197774662535746174159919363090106256651747909145697671167458383625247872371342692585633790167444008499855939770719654152784660652988885692010985836343743921790352978701597520154125477119225578344430739806044590791394863867388519615142187651873099398346752216736534160133513089204038632116111390057956510368124089594721171279022514357704430909408002196677042929096233790477552266642735380225996490619157688214205864526207308810591981
      223641805841145955156988212898417275231060994241979834607806408789285778492939622798440886512634442032394913173755204995518845522256567005240716361647059986169750679724275455828879695798268629170206625141570239504049200822201829878951806071143587496801073747088312384577502929790454952978286857602998021798107019570568814152214680717841481499353838664800855764437259358579900481593799116928872127488451061141759999524441805612522596498068576187465663092433761578273885210839861515797563719764133)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
