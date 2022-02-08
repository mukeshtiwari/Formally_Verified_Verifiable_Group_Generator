From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo14:
  prime  9489030946027095544267646354888817094928068781486254201022858928218470664141616564850334815622322606704665295844872311110366641840745271444824077175270408257506222859365193190456882315844175318920310983445737638140295336511616304451045429934453282538693161296375083036584160901339274287598832901472155574690625644828660481782595398628381579961478982369746332491217720167518089609238435485423747957258894485863643550990557114293188377944886910370857226452028317798841039->
  prime  1132357019917840001446287004829562489473322746165484259941598223291551831429335448263171020058718260710807694333685760746366285564312874190973361980732283345651361761199579570735866631568035238634451259104175997535100963063120553145314287900228830337328074714287782628188490461922788365777982718457846713512845030940813760368300292167318245917071318165686753046322955375125087082658568489115274907100527181698516809542752967549225460302212434993276327368021841775715932508331435351.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1132357019917840001446287004829562489473322746165484259941598223291551831429335448263171020058718260710807694333685760746366285564312874190973361980732283345651361761199579570735866631568035238634451259104175997535100963063120553145314287900228830337328074714287782628188490461922788365777982718457846713512845030940813760368300292167318245917071318165686753046322955375125087082658568489115274907100527181698516809542752967549225460302212434993276327368021841775715932508331435351
      119333262412
      ((9489030946027095544267646354888817094928068781486254201022858928218470664141616564850334815622322606704665295844872311110366641840745271444824077175270408257506222859365193190456882315844175318920310983445737638140295336511616304451045429934453282538693161296375083036584160901339274287598832901472155574690625644828660481782595398628381579961478982369746332491217720167518089609238435485423747957258894485863643550990557114293188377944886910370857226452028317798841039,1)::nil)
      322940835635258240668735554834679854272002458764164266143685726536813440563555101539425875848730090694681655036709897873678502094063789576818756969031929118898312519409668431084070245219246635450661104659089119730758833542923978196289857542559483193540681788625114555829303679526200964561872778603435861672354134584234860613487467013212087651932105439716032776411807322242836260261618926384092469078504977682593831793084533179427195461701950982446937508354312053090683488199437967
      894673552199653588077895974228890838514678118253393382659697472151957846099470590854296024003169790187133876113672552851068382199632368909581178949211461964694731535424437631165943467537445642919696181756875806135968467077966406248883501107312267807392372872920114771321172973786546547398361858592040872115503429404175888679850986339032514611369337707329255998520514893109803432760243253388613125003834717031704815734433776445652623761781875575392730772252634120249361405502052732
      964269478900998849198793188139998841647288073096710964849532458509537252996825032533574427750022906044310716558558348306140883746611865034419955819583056794288427401025241251729269514674907711738451763007261868208255700794820906745415073695175258501313016459039552195713834381313735363774178199002222527616022097942645153980184542265405786794991336827464435971190903086967363843186337689717234818339245092919221548542454514942119731214202110688239877044606732406686227693898220956
      785767144733730759752074353169428172823427091089385621129504953573592939941484533568204008584129909382362828072924704302408881203260789806675070122023007908450050154404597159775028636721268318152729389164137204210394568478180302956821520378480151263864987340948149348723485884800324344821343752041551705361333099907924149279364227925366170018568914600887559163491761841388603739380140665813718186051697025545986873358489769700722715974631093730255537378512136182064822934793232135)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
