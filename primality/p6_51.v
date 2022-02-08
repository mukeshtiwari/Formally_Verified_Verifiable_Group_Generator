From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo51:
  prime  13945975005088005877437844476697756967881613990440311905335859578458773516438069520989038791004477139890260077787429629682557371287360390133738067355827288897009730498640655960270225687365984808943299->
  prime  28289800785121162386547235780626747546542954664799905028707140558971818923753084289272852880638730003618365667383311603623407484662266145666050497745932375674855988516737128678706916690133129622361055070377.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      28289800785121162386547235780626747546542954664799905028707140558971818923753084289272852880638730003618365667383311603623407484662266145666050497745932375674855988516737128678706916690133129622361055070377
      2028528
      ((13945975005088005877437844476697756967881613990440311905335859578458773516438069520989038791004477139890260077787429629682557371287360390133738067355827288897009730498640655960270225687365984808943299,1)::nil)
      17576957887003029200026667681629044507219408308790315091919662453487993768866963832408178882682216525834067839677097077026613251073588692497379062104056036617919830324098184216342833800131812190940574481988
      16116572880513842177569555607324223190772827916306235758895282205416552562520548539565027154595574647925542299632780988491829029455397104830911872914046862243870407355081639208635511635998897768384978459900
      0
      5009292328175759342986629544723660638526977287539336629943828746063039931794586233612643767014166503722637958052513537351501698442226790029576863412097434870979378294337553680148270863702925495225115636162)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
