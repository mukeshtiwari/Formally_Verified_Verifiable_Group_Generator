From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo31:
  prime  2141076164560516236916867952644862985275117288963356511310554665644967361340221227380400649203->
  prime  48471823289485527087560973579927053123643380304832741531632625392083838275891350801702884318283763.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      48471823289485527087560973579927053123643380304832741531632625392083838275891350801702884318283763
      22639
      ((2141076164560516236916867952644862985275117288963356511310554665644967361340221227380400649203,1)::nil)
      24708942660717000888079957153942021604665838299224000512868970372414579035047641826313786669953669
      15373626592064514064772400596460759335318001813559936431220925268368829683388940799542332789533784
      9920529598895659990216753460782639956635219922769235763604190759961547144630607333904724346169671
      3962701315675523676021561168374945866465574413286196053904432619687567598793017900115467359444309)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.