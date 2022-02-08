From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo27:
  prime  15155756630627054754740176529372082232319569124431545932407438650809661675881841880080316756511329695779007145803905807734085082827640568921920568567464079007616296119444154867143856481269356216621524253879109465417788439134414967312312813895498732797781921152219480949006240570294101782776406952074788361665307379434713855511608224118928904574541337383583698719599180387456007212602402486186196267566907->
  prime  822108862671733958116126135659259228609942707585664777557509102174519287946534630943076702140200568017836463616987066634727711232902535020600659321373521501689138366703128736613351350969974958614417961627290569264706882819632756837540055094896121577926138462949486584147773708319157618013945617036343344484573045850975670576109036490979719715600752972365668202224569281117893782476471488901315939505631485651.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      822108862671733958116126135659259228609942707585664777557509102174519287946534630943076702140200568017836463616987066634727711232902535020600659321373521501689138366703128736613351350969974958614417961627290569264706882819632756837540055094896121577926138462949486584147773708319157618013945617036343344484573045850975670576109036490979719715600752972365668202224569281117893782476471488901315939505631485651
      54244
      ((15155756630627054754740176529372082232319569124431545932407438650809661675881841880080316756511329695779007145803905807734085082827640568921920568567464079007616296119444154867143856481269356216621524253879109465417788439134414967312312813895498732797781921152219480949006240570294101782776406952074788361665307379434713855511608224118928904574541337383583698719599180387456007212602402486186196267566907,1)::nil)
      143218944468005900165961455944903750588776422879469540483812881971241049279303275725009240866875266728608881228663197008214777406676032952790517790692965177182843736753662147193863045556981484822921012549836167797390667373137166609362999233898621230548840814637334333351559218840250793648444052036141064716889903958322668759169030632360043783195468897907727025289283131085832732987082628517312367646279016109
      113473510339718277648468890737121754801664086688462452970256120020015213871222409090876555571752002713900144552995519404518934547445066028933182188187014082967938637547967374178698983552556299235924000368779898751992541352440174694550790511168637278707466646004048057092481851446862848905626908580498352953579135144483236949808033478687988499865908757783844378633384198435198234023640747076633628366492641442
      0
      802779586588493820769941231967399232456420529817867379038231116704833390399509580084230493105508627672827363413979050448647567644074634559257110445558058554637992562207408025636063445831106750280917908888605076114797442121774627530399534369987633661471988815907382180845893685465720547685477325759751291136301431656919684657626490322256293679374031695867406552673296333746647097243167322179170872180119671670)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
