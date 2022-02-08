From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo35:
  prime  34642308250871843839688248131855492220147040877578341081643647846877515837318354812685016398859989710030676134512040236711564175459208598130658770199180840039908964339019824448753794157203195302580258141569251653606826344703289321646029455477854175960130689222274026519223569633705948407410471170856100147044651708797023->
  prime  382023002552252535689548947240283527240352959182529987542194543834021303955028474114991140840466093689615299344358062386985123642460867068054043469614082704459887529842161479244649148407963472252939926405889004738372459929606544313548283762226477052111636573402635935896720853689856762220334241158123254767393664136249952498426194781.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      382023002552252535689548947240283527240352959182529987542194543834021303955028474114991140840466093689615299344358062386985123642460867068054043469614082704459887529842161479244649148407963472252939926405889004738372459929606544313548283762226477052111636573402635935896720853689856762220334241158123254767393664136249952498426194781
      11027642840244
      ((34642308250871843839688248131855492220147040877578341081643647846877515837318354812685016398859989710030676134512040236711564175459208598130658770199180840039908964339019824448753794157203195302580258141569251653606826344703289321646029455477854175960130689222274026519223569633705948407410471170856100147044651708797023,1)::nil)
      176956413927343185783790831733862443639847434824108010883181170789954805823571414591144483766705881812932956736101153743412300269399588766698726463220283933807397959432386009819328598989140701197746330485494119513330859467607048471503770509355569990664289523093391164679845384883084285612525440779580714920076344851121325132752829922
      49340600514992675847858462858307852054573292594134412725622053637462618070782575463689494902171597978701698448670495592707795837220943994183185048578518153645248543911327257602591993689640889430703048726184233389358046032996144514224532176389006007704191388690296888025428305813222538872608296651249398016128257514285408150716468458
      106690240378838302261553356897701101858302312060716058297679477557062539962767853296849645840927818321459847849932742387128157745854285397899855284120784577349884462327142615662203716971035389009373109060656615974780308811116529689262481079830293271928262345788543908226469296746087891444260407112106329866696024425660584598031952388
      3474051300957454215381276739569247585296845980831880526547940087999606303592681367934943946247467279319593841654422630214789834294095722030978127914594868582632424305740070046882776649728235592606835225391205984034486645571607444485446478256443815880191050428477608695179630914849086441742896326739525527519108344040267295734179854)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
