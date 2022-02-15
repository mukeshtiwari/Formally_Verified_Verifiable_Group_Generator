From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo26:
  prime  1640460613471513089009251180623151138070391495511648124427217238685109984947037600671346799130217220147859492993003562224071768389353131049752249078592067133058986418195816731541989479585178474442499631127160022610471771938041604206845712307979781441254101416777558707017195330460287109771987328775511628520572537121149020163853219292345852797032616867158962328286752442348904552352044049->
  prime  825266868596764145648658861397338935137113120570041870425002554835372881370623014541705776563959792545834346486202816564818976026846778180062646491444115874146216505906890180649975734396685407195625867081771411999651951648177294430589344513407128133032419259193279814137332325039635281103007994455638570491147291827314780348715351277605714242275938001908676539244940438895368224122331827489380541.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      825266868596764145648658861397338935137113120570041870425002554835372881370623014541705776563959792545834346486202816564818976026846778180062646491444115874146216505906890180649975734396685407195625867081771411999651951648177294430589344513407128133032419259193279814137332325039635281103007994455638570491147291827314780348715351277605714242275938001908676539244940438895368224122331827489380541
      503070212
      ((1640460613471513089009251180623151138070391495511648124427217238685109984947037600671346799130217220147859492993003562224071768389353131049752249078592067133058986418195816731541989479585178474442499631127160022610471771938041604206845712307979781441254101416777558707017195330460287109771987328775511628520572537121149020163853219292345852797032616867158962328286752442348904552352044049,1)::nil)
      496376509185670774103857971069269455630959742222039303202564886421689463024783788378815632335723178844236882230284301668257243346877296434510101523188140642083344496263183584094025141568382144928955862563306030194037790739392493439885137411250230953577385153328174366376663038757605898490350578781849827083317468843973449389200667562301238376842740894233664044479918311986494281391682953397077846
      435632099614394942115055989793783242362337512820831942589664424667417363002792769514274106276188667005635728482121371804944997126483013700171932881119411150208426000893146857470791967157073791165965687485975940764274927005387406210621250635048265496359329585116096171361280694632662529478357044733393023535898812096801532160703789160276955056770440046050328239328244975811489943664807066190830566
      237504344263612278928556805898603920024443151766517024868237634009273273169436676455727858281493043022075795207300973934143981400513812055847049123756397519421667826647994951856952367804975431296563927177642009677746026025055885103492305504058132064870568831129290936356003575230600021379738608292807363360844211221326017091327461607880734567486591521138875871441829701226712225239285414976165265
      79129696498227473738994406689377436272130201184066232235092659490951386803694778552541599229918803077053530306533015894190928577553874040939996757061299602660940742932762950719446512684392359756861156550415389265205246838007354735885500972808147406469233500087633094566646794755177825885134173461660321484942726032501934219271326746805130925037485299368000429406900609162268521371476683038992574)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.