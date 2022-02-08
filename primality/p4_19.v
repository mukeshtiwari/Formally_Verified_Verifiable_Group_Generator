From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo19:
  prime  8432928683916437439806111488744862872901214789167658520447759158318597276286314716202115142752404601874869500223550888373169672219769221682516730422367680738424829630927266106245634336971656928838766484481090122531830624062497617952122325396745249708523516084036852973697097153681048503837621842634598809132867109455668726848509337523263433235350047678768681721439156526680721620411833583896464030388836902868924446459160996270204535867466665773->
  prime  129085565730552418075336437874061927209665703740530686876493510196918652910614042726453524633936709093306413585231315722330319218423036127683653550234127640534251599908023341073434074009606295546420092151156479242031345903365410722924970203737129056474430397645109663423605225531193341096777794705450290222424805235235567525166948940403253256699621397420032431352829470080294426357855597779304279606870357544550625174617618313144323271867085437606255629961.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      129085565730552418075336437874061927209665703740530686876493510196918652910614042726453524633936709093306413585231315722330319218423036127683653550234127640534251599908023341073434074009606295546420092151156479242031345903365410722924970203737129056474430397645109663423605225531193341096777794705450290222424805235235567525166948940403253256699621397420032431352829470080294426357855597779304279606870357544550625174617618313144323271867085437606255629961
      15307323300
      ((8432928683916437439806111488744862872901214789167658520447759158318597276286314716202115142752404601874869500223550888373169672219769221682516730422367680738424829630927266106245634336971656928838766484481090122531830624062497617952122325396745249708523516084036852973697097153681048503837621842634598809132867109455668726848509337523263433235350047678768681721439156526680721620411833583896464030388836902868924446459160996270204535867466665773,1)::nil)
      129085565730552418075336437874061927209665703740530686876493510196918652910614042726453524633936709093306413585231315722330319218423036127683653550234127640534251599908023341073434074009606295546420092151156479242031345903365410722924970203737129056474430397645109663423605225531193341096777794705450290222424805235235567525166948940403253256699621397420032431352829470080294426357855597779304279606870357544550625174617618313144323271867085437605891765097
      2741054664656
      2348
      1378276)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
