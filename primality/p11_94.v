From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo94:
  prime  625654005064644594160329021457211143471513814438828974571547005162606504996197193956323657206092305189570402688662980597872767179683809765903576372364780739502696052120599503->
  prime  12310122947281961694017722977215675232177264979483138882711726827153421850555217478984593400264993890706748928069370342128760101218003946060629074415281197908667516933734682257743037.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      12310122947281961694017722977215675232177264979483138882711726827153421850555217478984593400264993890706748928069370342128760101218003946060629074415281197908667516933734682257743037
      19675608
      ((625654005064644594160329021457211143471513814438828974571547005162606504996197193956323657206092305189570402688662980597872767179683809765903576372364780739502696052120599503,1)::nil)
      1388466440520308938746823382537492316758357906312639294877982807792151137950575225438549540861638192795005197069947879949990900341841664377466868594773372483017580570930424181825699
      10697197759079249106233315997664555591610485021460027010372997790760770948602979603253031897356950662119064717716127233992879552484886750497484397160927458366048701051408163411090244
      7845593051561604741409115687219266505511401766244133356839251399132142635265463082883599838011469472751560198854058044288196159720413018680821325143973999853985450986291587467559365
      5164227150312444577223957393652628018542301358164912600969850895539246840096631932201144641465892432731755638101663976123115351637129096380069346861375968476151473228041422977819427)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.