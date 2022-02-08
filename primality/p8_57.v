From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo57:
  prime  140345378088219184975515172177090332312604733276233654581676231291392838380085239802971850247919756385435840924930853244800559273642063434789175607464893467767888923905284060205969433->
  prime  810697778566937534613444665292009095906480986324033341541014502890703578474966623289397138420839128163919234955507361642990674005328571575221753684730578500328082461317208655431551740928881.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      810697778566937534613444665292009095906480986324033341541014502890703578474966623289397138420839128163919234955507361642990674005328571575221753684730578500328082461317208655431551740928881
      5776448
      ((140345378088219184975515172177090332312604733276233654581676231291392838380085239802971850247919756385435840924930853244800559273642063434789175607464893467767888923905284060205969433,1)::nil)
      260035655591408206859891587152264459624628925207073018167771566702431082373521201918312247877664996709541912974034493345952755606605419795136051585910148515070719472478619339486630382501963
      306061564755369865193780504303876759531379403748321833446299931029243478647629286986088056287109336824496177056696610496703390836140902490051336091920246302334194183732039839728888853338788
      0
      276558271252074379231108733526431661516231631757520366782660960765890364284584613314040081717601694353961332530863828703326192514770689302692112763104241345887095392843780038915347500184829)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
