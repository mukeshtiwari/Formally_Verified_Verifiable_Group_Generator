From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo21:
  prime  7141415375438733751444424208024282423079591205055924212962813979066572571670931016145464837761973491575737278406008229361912872437773208457190385233103730589925129->
  prime  137265144931307901436513277702434732454012822552379919297358247491638591400086965060671265532597024643333098176212479598114660643440913961816102416340575324941403970061.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      137265144931307901436513277702434732454012822552379919297358247491638591400086965060671265532597024643333098176212479598114660643440913961816102416340575324941403970061
      19221
      ((7141415375438733751444424208024282423079591205055924212962813979066572571670931016145464837761973491575737278406008229361912872437773208457190385233103730589925129,1)::nil)
      43381937372472090151212822178016134916349480801311812709552654619825094536724059106859322840401993587988230113498703044427304804889554619605776305139386357794557840685
      26941812577611538691465796467481015422243416502161518112102828951276403116698372006108305686802472096867669211308517885460989438822757381625554228688057356705833938036
      43902754828161047549701567760251038801161490773778446611313048145872415331122923730212772495897228400864441743998698840305134062017998980103637440726979599291295890133
      108569039964056334386986730644761153289404314716390996009373020607801282668562435863874035271218448769884444361074848612436794191511041540066690488159486510449479905970)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.