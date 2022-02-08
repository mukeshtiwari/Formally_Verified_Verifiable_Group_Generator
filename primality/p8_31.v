From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo31:
  prime  11669182732511074211997914002690908117305995309992241953873911877100854749353530958920824853624994359328833923247131380616536154512579336099772974705732841182998362966547636429775510369895447766068707950074078882643519734641776422093794035426032303999463623121409646267209688759901494507325566505712151285843755171986863881046917961885608776134200849553403016826365216889->
  prime  10397304244794986057137175565237513528878069408277996039396108707925404071246905125789085170992836867881813434874683432282220012139134830764345854248222637164751870444435815088784879038557328145149956926550336455404926016230615242244848438864573573012134334528245173334190635170080842661773647838992133076487161636488716688223795097568593760211376487157799648033080678733549049831.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      10397304244794986057137175565237513528878069408277996039396108707925404071246905125789085170992836867881813434874683432282220012139134830764345854248222637164751870444435815088784879038557328145149956926550336455404926016230615242244848438864573573012134334528245173334190635170080842661773647838992133076487161636488716688223795097568593760211376487157799648033080678733549049831
      891005350
      ((11669182732511074211997914002690908117305995309992241953873911877100854749353530958920824853624994359328833923247131380616536154512579336099772974705732841182998362966547636429775510369895447766068707950074078882643519734641776422093794035426032303999463623121409646267209688759901494507325566505712151285843755171986863881046917961885608776134200849553403016826365216889,1)::nil)
      2784102831008745875765683266592357190780013032979855197221691301749079625532612271113250548309953296457785158765667267887949136825223103520733730236165179317571876030690964665519818057060423256304665057121339340383749971720954048931813888070530808759261932425602764251741168926701943838013845864139264814472853070654353432605880592047810412604923946045671720267838841716865382849
      1797706760227436254146303940746958374768353118784826566144441971184425546847811361847328136172568230314198302015735559740366095767052614464758429494328252846941838313904749714018912863585787783212110569202243321287463205162685325154841713500372657829339769306836588302382831322503814743817542769184149922444888496097049015868444213526779129359329503068280543612753211374450309158
      0
      4737425803304874067115395938638527995867761374178506889112853138775695664890063169629637330067089790797509898196237225379003683659532924841713801174068242178058288119376777380905475666917270863182969445331887983388251297136072108309954939734375719852221168942424687887170242843018353827655068050688935641238411314481613334598988271078376714788791081263044307189342259475533659895)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
