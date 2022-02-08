From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo75:
  prime  1566526681209588638510276358931982209397930820322770149928023222714384084560154447466011013637946158155451398419987738333575718022687318978392665085022511976194938769182186801368341399829137818947308355376572394641515814327576968985483550752274874032139348021461106961047604837461553685078970464468013->
  prime  42659654582699517803911845806435739526324452099029676722839928400958107390742125913394411923388549778889252481773106090299933953193821070419589055595333423722467388464585038050843574991659936474073752670034013669940031138385601538288679613630169640226967542882305700376305214003789029788075035487912058961.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      42659654582699517803911845806435739526324452099029676722839928400958107390742125913394411923388549778889252481773106090299933953193821070419589055595333423722467388464585038050843574991659936474073752670034013669940031138385601538288679613630169640226967542882305700376305214003789029788075035487912058961
      27232
      ((1566526681209588638510276358931982209397930820322770149928023222714384084560154447466011013637946158155451398419987738333575718022687318978392665085022511976194938769182186801368341399829137818947308355376572394641515814327576968985483550752274874032139348021461106961047604837461553685078970464468013,1)::nil)
      21594415816763037451977142327538272760284877558230047451851357959807554237849584500811624018541499878576906187467358933127629102829015178631594753603161776432551003896088849866471663840889997228383730059901475694282574471058965099849853480700058940276854990682078139322696868926530128304795414226997885193
      36471531247549369159584614548336781548121017285194782217025573665171039847375010255241533276820072791276848318415783439554340728635345311086117867622350135705564591691610732297138729178013563814103304045936784454831141139303339586178472369058936229460469583633197904589638620025332037128293068996098325360
      0
      5455289265231684974536098001088079877732054204977991267953061219265111984278129129215869829311042989061181379517704399298925721878344346764999830359687108898839544365985611935577936756386092063127610663634179440179020895348808617430470507408715013638808300583170922762750835771044608566320363812105699730)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
