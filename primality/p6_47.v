From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo47:
  prime  703440383986605415307878062102511782199289284231998627445928256588340161167888331119098946723775261779334759847902204704334781688627598913512855801520902152702243099843066647668757615996779137032936634733890856519015561239->
  prime  13528365687761343151263163452985869481910586916193075715429897587082086890975056703796473119290776282365820770323052322738891632096032634656092693335840510603074254542693852494709269508309785651236358639579633374488754888478484769.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      13528365687761343151263163452985869481910586916193075715429897587082086890975056703796473119290776282365820770323052322738891632096032634656092693335840510603074254542693852494709269508309785651236358639579633374488754888478484769
      19231716
      ((703440383986605415307878062102511782199289284231998627445928256588340161167888331119098946723775261779334759847902204704334781688627598913512855801520902152702243099843066647668757615996779137032936634733890856519015561239,1)::nil)
      574584708414679338287977680612988855269742297176618795930229218327232057465524876845521259699653333987476118611570435607383096983722798486000866042522815192841239940044939646623617795361543205776100173542442212621458912181102695
      11247647278317412609758971721935824923459786061436904601073479465175628401736994922260861925195959463969603853554756921952977568883266278999280321658852438191491697979256365949690782080469733968752357110754828971423352268360997129
      12146881086944075430553748311558322104420822464016002234762082641952694005621125566857227814291676468100042662485524244932934570315571821794256014929528817943801819757963498614296645870476451702781704158203954303766762322533535338
      9356855770680263012814322646569921339283860264771511930672345524606526600083076824238856218467693292238890868124632771948708748974546234410903982436523044848493141703942803070418520898010617642785908356739180762405822009754357989)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
