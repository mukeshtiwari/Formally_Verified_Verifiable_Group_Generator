From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo39:
  prime  13469602962878230251858594114915057835065264503401719174052508272558388884060758027023289463043183705121486080548987429201840284619323536365205037516714437448209486802515837914517657357899304833332145941066525731289437323386021052563726365842490065828747973063508408536494378536722736915770502631767107026747859036851->
  prime  1038953929465956144496645859908013126795159771690662573840725456454115807990146246629701493416328536486652943306839251447784546289446606297576578695115213481155603818923912266146499270159297594243654326066906584377950413506545735773013197434580718809625827401760438514118276575260388874060107764995305458329070082659572124833.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1038953929465956144496645859908013126795159771690662573840725456454115807990146246629701493416328536486652943306839251447784546289446606297576578695115213481155603818923912266146499270159297594243654326066906584377950413506545735773013197434580718809625827401760438514118276575260388874060107764995305458329070082659572124833
      77133226
      ((13469602962878230251858594114915057835065264503401719174052508272558388884060758027023289463043183705121486080548987429201840284619323536365205037516714437448209486802515837914517657357899304833332145941066525731289437323386021052563726365842490065828747973063508408536494378536722736915770502631767107026747859036851,1)::nil)
      797213388902187120415353872854391953321952335299738201494254926929026952753103151562169550924888552675064607601326968822873279878352817122543273176779790812730338968806587422582677612616682993594061331581764217074753161917338646908954848335535558720392677096182335242412624948315152746181930464189283402754353218377530435950
      836080029078881725144603786372394163016785298958021284946291913252826882405847322757739419633554150211876514111651881979219954306354072908187042181852690854497468969510773398047137100525050266655380065244681110587552175590625083378679662446286072688907632416077514457014003210286068990072782193464163227011934215065947924127
      358423904822709694839913040110700851923930929193222017528266886881535092382751965484928554531969567243868449171206917370365255573215010821765854791485388347043989273465884593207048571981465209788010352723442009646181881090789148574320930378467700388029634915326237270969965104732767448132617183031156136233150402070685779618
      311339354705725172129995366338846706655441206143451846292865073342569106308799450682938957446293138197598167280934254759849550986573821654956676655472877964863209758296308117688435246495872839933088218941164713109619603045381543371559837767453634593129418251058972786433261268352491699221757827740216786035081269314648408432)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
