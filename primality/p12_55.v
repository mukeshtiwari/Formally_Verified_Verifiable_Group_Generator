From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo55:
  prime  248015242142635787273305093457513469242688757016722153939799281195741782901344159403872868277127646851163363405735568501049213883383292189683096583586801025806870396784493363796935424413880108431616164031637470130709526945095806204999982708770977462476905661415129706575453078493573412334102203432730151183282985858710124481399263611996090764639459817840649537549934809410184878672024646345126490250160126718253349158934527353215151216389->
  prime  475590666486111142247193357563586012024704375809165040726162447641697834611750332352785892711490479136537798147447561411980940820681611842410674854311859127999349860745716060609457102396378565783597365589964563876740967102236344225045950516798345414733036821279385263879503970572972063325462739959499183156512767533464832799025026109422520904708317761859228146333042066261105471644766753976007296241916131657873800047721709289117586297324445241247.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      475590666486111142247193357563586012024704375809165040726162447641697834611750332352785892711490479136537798147447561411980940820681611842410674854311859127999349860745716060609457102396378565783597365589964563876740967102236344225045950516798345414733036821279385263879503970572972063325462739959499183156512767533464832799025026109422520904708317761859228146333042066261105471644766753976007296241916131657873800047721709289117586297324445241247
      1917586445
      ((248015242142635787273305093457513469242688757016722153939799281195741782901344159403872868277127646851163363405735568501049213883383292189683096583586801025806870396784493363796935424413880108431616164031637470130709526945095806204999982708770977462476905661415129706575453078493573412334102203432730151183282985858710124481399263611996090764639459817840649537549934809410184878672024646345126490250160126718253349158934527353215151216389,1)::nil)
      77794966122584782410467598486218995204321887909102886998640596748739615542609398058419290745762358222436827460523918048747534324046499344801195131468563050630803421002866293592287944148414929341635597674112424393759352367348072962682430788582300627031173745812152321412809919672838691948074732179825491138699774456961915626240220366770539480622332393458947043496869792938080178215320726664624384470555122767212057505696924816116527327537973047457
      28042518930619196380325665902067689051197657899519544380893855770164410341981596224808400960676436707728575990158652393570589733799261772878130320196200445099321897553774569782368696798242096583445692271214248005731811055141169530910485447997604118620103468964154225658062336898201812980141614966649476503782369714834164262150172118867655761974097889734994479506860977258893129715907198762660693387102085636411337015362804965190220784428202394533
      388416612825044063514561970703873532009959736515977967464115049878678096386614118956469653152992191233520940918930137534521677909258936087316228115842467072739836814989919117018997218192334633234559775204157663735026668511646919423168399695906563119653150340281787405418233720311854066771435889444109916517519314180964924340314881443129637025691887186396891244233252776521850067471445993277009486495879991433937526011016053105192900614775655517080
      272248398525316059553291198589689063660188362480002680959303674258229295310843153563936077406388909604812143229404347048200994494223291575465189136390435363498859422620256520722901597008212159416155795015463931522609562506751102634588875288921549945087115225958387707915185705402186056831643594974339432212535767936585911964509043384089437685567323393854503164719492626511043917862267051859113766395993905205750052174211813606198172291000400296210)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
