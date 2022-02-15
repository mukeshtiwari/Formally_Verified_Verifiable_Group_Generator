From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo66:
  prime  668404344186642638230119565930206524482414622109148336570657427752688537744416210509204447937881601581289->
  prime  2763361608416785104309286024805446260624293673406256658316475294861984500430671825783344756923914717591207149511403.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2763361608416785104309286024805446260624293673406256658316475294861984500430671825783344756923914717591207149511403
      4134266380
      ((668404344186642638230119565930206524482414622109148336570657427752688537744416210509204447937881601581289,1)::nil)
      861436177208762646555121004595214582738850480169343304402089083109164188928931895426401669901775807746903155330309
      1059587328947369647372290664522189988645359307287820146526882386836819281001907517771369306304041384202782789455549
      2587437025754133706540108579771521940186391298605819725531068804149163736574727189790681964806944210607755881560020
      959992788140680054682617051906905449886393278317543108955827461766943571278706565880102897514210865436210742661823)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.