From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo37:
  prime  29422346197240164179141702429198725156363742196781754942435420027866309297866165567848335791758677923129895005400928743278603018849188911955543242535864143845968737990657600988483568315215582692667531333177399197465659680166558412089822553613995538740079701671724122074403891323503811273021657820527002092723841463058944191102280003->
  prime  17216191653853109667782975759421342037994680109024876087016661675105692222553408120370775205189672799940226763460299444842041770449414399941666572937435545130030147347846183713422775944635401089183875374031644273361848972211064778608679572252849915399285116440727741479260714779544019001424838128361986983165620420918821042927610803494197.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      17216191653853109667782975759421342037994680109024876087016661675105692222553408120370775205189672799940226763460299444842041770449414399941666572937435545130030147347846183713422775944635401089183875374031644273361848972211064778608679572252849915399285116440727741479260714779544019001424838128361986983165620420918821042927610803494197
      585140
      ((29422346197240164179141702429198725156363742196781754942435420027866309297866165567848335791758677923129895005400928743278603018849188911955543242535864143845968737990657600988483568315215582692667531333177399197465659680166558412089822553613995538740079701671724122074403891323503811273021657820527002092723841463058944191102280003,1)::nil)
      9227896675486237000895528185023592753899901070248066579004731511295565287872876319975072168403118988143909078087977962695842737375043597442722791454943714958012350053551912076778088019233324982127952957530324168471934031439026034854277967973091705165862958378243896369159885244483755005844864776861786964709923792833404908090670066693809
      3298481898234343356230212940601222740572151567093190719182851690640770947977800132831510896875850260534375424609492019757129124573295169506385145176447499331114207559431619363291109967871095050901862685725793107204066802556301742261435261334940110773808455705475029984619670970592436023935148198982347657013494735915885923688234411196715
      14101526947475294316401324519383172311662926723130924366743462106226948457769962924937215655985916379882252987836562632429017691664707689142086263316040167927467140579225096427146416280455824475518389324260893673175155532004306227750687426469327931836994563060907892710957505969638298835181862604775276486486001800640533968782263051277139
      9750837839055597316875540168516246775957088661259785596646569263792647354577015617814337429755854722884519584474269543425352058240704293639038824906474947024447733779162467074495118293939526615546823596613005671328457036673456965179245203293216076046235653488442170883778512937836463484152704229503273957056266527676014517973435991893291)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.