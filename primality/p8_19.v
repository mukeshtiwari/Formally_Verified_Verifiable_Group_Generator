From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo19:
  prime  6285216620527504324843585559071747567819949449200832789357077003862839402913186521618614598767898194716794924787094163913729503140462558972625363653018788575522616418360521503127715801246390247474286781922037627606626332910931333108555727257172139834583370196321797223955822704189051617501388064563092439094558976475212214899946030547150214230762784594773418847707285576618530098095377613385142871734862341659718767186292282883874725244690937850839987045363643904096512587->
  prime  25623790101798805430300511482588164103245380329360714721866145519267915262984115709666367710408203032562431677223999994591257356652656677275616247780922032092303362397850806162880762251267514986385784604165531945939677676479349808575536824062193611224543217429282669474628569364408941979664337678013618375129261275500514510680337504197280761491761851285337275097910585002698800250367258702724378669794799686968879938136469699453260961859901149179678663197451039141532718572465239719.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      25623790101798805430300511482588164103245380329360714721866145519267915262984115709666367710408203032562431677223999994591257356652656677275616247780922032092303362397850806162880762251267514986385784604165531945939677676479349808575536824062193611224543217429282669474628569364408941979664337678013618375129261275500514510680337504197280761491761851285337275097910585002698800250367258702724378669794799686968879938136469699453260961859901149179678663197451039141532718572465239719
      4076834841
      ((6285216620527504324843585559071747567819949449200832789357077003862839402913186521618614598767898194716794924787094163913729503140462558972625363653018788575522616418360521503127715801246390247474286781922037627606626332910931333108555727257172139834583370196321797223955822704189051617501388064563092439094558976475212214899946030547150214230762784594773418847707285576618530098095377613385142871734862341659718767186292282883874725244690937850839987045363643904096512587,1)::nil)
      0
      1272112
      129
      1849)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
