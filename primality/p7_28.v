From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo28:
  prime  493670962266413230339038650139171741638246355026370113442729038737384942611930928689412414565527067541942101078736553108683141239293836879588555118976885429161554804600952184752922055601570872388830278855282599179819714300931427059630037581424099050621073996054235805966209615534705178379340215854924216811740889195880288952090238949676712968717351449431303491209506524977337->
  prime  2322891206603531628483183139161800780315331018898845428696950983319683078024450911792225878989000828569004471716125489014070457848322580304513850709192055015907317768945458155861868523870462216873982399055786595335656641075852948791450485753063100543539007721154406445020064519854383119818369074585852199564682060614215198014437781400491382517745725465422924615628402391155970828063.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2322891206603531628483183139161800780315331018898845428696950983319683078024450911792225878989000828569004471716125489014070457848322580304513850709192055015907317768945458155861868523870462216873982399055786595335656641075852948791450485753063100543539007721154406445020064519854383119818369074585852199564682060614215198014437781400491382517745725465422924615628402391155970828063
      4705343
      ((493670962266413230339038650139171741638246355026370113442729038737384942611930928689412414565527067541942101078736553108683141239293836879588555118976885429161554804600952184752922055601570872388830278855282599179819714300931427059630037581424099050621073996054235805966209615534705178379340215854924216811740889195880288952090238949676712968717351449431303491209506524977337,1)::nil)
      2322891206603531628483183139161800780315331018898845428696950983319683078024450911792225878989000828569004471716125489014070457848322580304513850709192055015907317768945458155861868523870462216873982399055786595335656641075852948791450485753063100543539007721154406445020064519854383119818369074585852199564682060614215198014437781400491382517745725465422924615628402370410139351903
      36370126051009921296
      0
      6030764964)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.