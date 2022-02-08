From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo47:
  prime  202509235056259432365365328909242315965317287015433187628888908725097105935707188709911919581496183192494465071389056265796559733215401474512203856846938044175406352779495204913670202891849279565557366108647101953770787->
  prime  8806924123361666454137372788934039079015683495014173896792749751545748040037969929805359470679687510858391791484108763558349298471562028385062230408260150282202902419549001850006554550873273344164308925825243178435339114207.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      8806924123361666454137372788934039079015683495014173896792749751545748040037969929805359470679687510858391791484108763558349298471562028385062230408260150282202902419549001850006554550873273344164308925825243178435339114207
      43489
      ((202509235056259432365365328909242315965317287015433187628888908725097105935707188709911919581496183192494465071389056265796559733215401474512203856846938044175406352779495204913670202891849279565557366108647101953770787,1)::nil)
      6454935830794026243933680413988625895828111904318956234339462525121087195123594924818377886785047260751429881091843341471439465751103261664170588283515734188583917173787557323489256260785700565131152288911045250458740488652
      6098385037304787089053453862431159209502194003658877129236366335379539906684969892444053889284432411669749395559588918801931364014392591293348155461395032445297816254911352658218301723687458352584902476405251497157575416639
      0
      490484902479672519386730477679272342249790426172398040248963981983671314423501451641988056381492048448826794053153583640959633046280358558802476637174353484133688418790274414900864093487076939333532496936428765695027035275)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
