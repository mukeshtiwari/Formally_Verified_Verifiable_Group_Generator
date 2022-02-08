From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo22:
  prime  742329548203958772181446043507130148498998784336327812459895822767639729661146087197532707365571515331870034156265291484680035023->
  prime  32488052677146255664520986094089550949058681796479386712307340683436754976393441979267342423127056970414712751995752284556217476360063.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      32488052677146255664520986094089550949058681796479386712307340683436754976393441979267342423127056970414712751995752284556217476360063
      43765
      ((742329548203958772181446043507130148498998784336327812459895822767639729661146087197532707365571515331870034156265291484680035023,1)::nil)
      23306826705894130370936424542159042790355545100481137102547091682656977856885114235009240129144141978385674343752100276739585136817099
      15790643817338353302714088643215059929570841034859374658722513946915833257426654870123751286867521178035270704678288845402710187277823
      29042678421441092474231476040567587769273843327378940617457167743965998952670604625880965453702137138804855259135793645272410114016482
      1975554268130444570395196694941084062255117052305608328760971299648300700841237770649084780488075872691569329793856005442610754587576)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
