From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo25:
  prime  9364111541939390021140741135344464958330073312835446385750405865311682590797760210952117409518512940691015879028669440668996422687058967->
  prime  403265463553619831260426016993609383430484607217258498602341228589647637830948693896761853742098678489909375398216785356980257484067022833587.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      403265463553619831260426016993609383430484607217258498602341228589647637830948693896761853742098678489909375398216785356980257484067022833587
      43065
      ((9364111541939390021140741135344464958330073312835446385750405865311682590797760210952117409518512940691015879028669440668996422687058967,1)::nil)
      84353876168958816605208629973571668008544049847074599882375915051339897958581071119854952572356085266025495623035484596884477716957117062993
      113286941766960384679877449234954851987893780721218863864311068343679840812070130896061348897869928540923192097426799761290258243106591429956
      366591264571754728347326719205044621196031285573095583144144076107891079085766779247732525219263164545345174728387374309066457817708831903564
      62672674604568118394993871652367110200889564837361985208980138754422400310795308751439367884119273066902888452907062958297109234410962562381)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
