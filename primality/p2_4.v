From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo4:
  prime  38004736923165089317517853383629215310410453102882325747044252802422241980609942778803688505788720064733790899034487861060970052232313692186231792636183558982044656946976950367591447758117414784421875711645187821223387206654885600424329143134810176997386503941682060971103->
  prime  116529862425161922411577665711838380012228611955215002140598039313796764066854476184642238181428191566628063509332670533894807941949120257875985193343093711589455659846676229382612683559212236269499811150099543747656485484021333260763858086510252445572430082868069000893689035149133.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      116529862425161922411577665711838380012228611955215002140598039313796764066854476184642238181428191566628063509332670533894807941949120257875985193343093711589455659846676229382612683559212236269499811150099543747656485484021333260763858086510252445572430082868069000893689035149133
      3066193108
      ((38004736923165089317517853383629215310410453102882325747044252802422241980609942778803688505788720064733790899034487861060970052232313692186231792636183558982044656946976950367591447758117414784421875711645187821223387206654885600424329143134810176997386503941682060971103,1)::nil)
      112152914853983477860291729307129220148624108731109684409200365059407212796935878403947289637559997096140447821869252012324942183362837041189114387954041517920047799403392176796508381221278713480732701169508348393526376142763825529139401541938687031551116531604619952142461856463303
      15730339712438714279271700151571853066999675381748864881055793869265434013245035869542224844374966621932326967237738684483850811302704695452019701254948252246571635848548568964113339783704324356824004786433133256434948583031642479879273782888100618198264320503859919338890207253496
      0
      96029521331130878920312295293553168944426013082029105416665090959559948191027188452726215267641194241012112901685680102135529039709331649653202994847601836830259093181171520746996652436533458048405701306011124230683210667125070822800714877285668863545251149824819816762694071710829)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.