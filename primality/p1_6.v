From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo6:
  prime  22924275257176792353286783170707832583508528746092221029767418811646590415019050979706291518204361921435913688937016755407308685261204504589653169814611811853779556562676626717206982941027563473208116080791673714500333992047556773495518383156581568879->
  prime  1641469805514887039664746822155363644309544692335187394615466256589142460077024126350889297869505131022497163782646147754184931046856380750562368422758890935944699669909657812205441520551629835604635604635340547162472918086258618142089801809024552475769343.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1641469805514887039664746822155363644309544692335187394615466256589142460077024126350889297869505131022497163782646147754184931046856380750562368422758890935944699669909657812205441520551629835604635604635340547162472918086258618142089801809024552475769343
      71604
      ((22924275257176792353286783170707832583508528746092221029767418811646590415019050979706291518204361921435913688937016755407308685261204504589653169814611811853779556562676626717206982941027563473208116080791673714500333992047556773495518383156581568879,1)::nil)
      941588068461015241827249753218319671689150959285655959395906072187929912301330836691719369601436987580999962350940701379751258261468096779744022484843856203406920180250884992858759411143849548543464564179636713743378075721672537162196191479791026583087679
      499061392498562811912442985640391828230951224456991660204302907513834359726996007746167989131776975783277028304734767513981616040521638396268477981137723602160194083410813992208336695545132822451191547487333527279029038803008758337740123914520640012023346
      0
      343435937924167850629998144731273809766579803847484864472945799342682309450923160190644374958592800661124774148974611798108564186342189688663155725645744672087905260762049197834814975124385131863332615633796652643597299375223036917687632156405565028395869)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.