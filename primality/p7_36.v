From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo36:
  prime  7517425407288438426893561654286268288105782287833350113714025640852747875421804216950485647009334772721979585455006240340390330099090155693048149928209752856259401814431550675131446291162721807696366439389521919864376249539087984252636414368812885146233649533693665896115871618257518607342883425632001->
  prime  34642308250871843839688248131855492220147040877578341081643647846877515837318354812685016398859989710030676134512040236711564175459208598130658770199180840039908964339019824448753794157203195302580258141569251653606826344703289321646029455477854175960130689222274026519223569633705948407410471170856100147044651708797023.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      34642308250871843839688248131855492220147040877578341081643647846877515837318354812685016398859989710030676134512040236711564175459208598130658770199180840039908964339019824448753794157203195302580258141569251653606826344703289321646029455477854175960130689222274026519223569633705948407410471170856100147044651708797023
      4608267641376895989
      ((7517425407288438426893561654286268288105782287833350113714025640852747875421804216950485647009334772721979585455006240340390330099090155693048149928209752856259401814431550675131446291162721807696366439389521919864376249539087984252636414368812885146233649533693665896115871618257518607342883425632001,1)::nil)
      20673127272463248690089473948192774365710987384215998758042272770961950491209481260645345947774118134669646865265854756817865336773352913191127471617164281459946036121394270310600185002163926974510859849841155962887770113037851703055827906911017889271174617973814221500844763471841834785341274534430620673965809447230808
      24071791639722273451753960436416664324999534651230810885763119743391088931881307579604293307839451050080563974951184937599102394117412268461311656474095083363670258738731247863334721999311035643529065644060102163676558129240744918144091538583451565396636240662286760738315297930222296173377425666012552338487699365562872
      0
      33097599831754752095306014676840420830565007012724199222166084880965704482846593248878037538485538577583280275032579154389860097726710878403374206270710442069870893425706609053053466475991044252113143942321651824650070972849270702011884544865199854483008329293423770849328064267132991514854472813846802197518910855539111)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.