From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo18:
  prime  1698000741551370176119816770659673992678116434595405000896040994040483106739181504255841533253375204587765498644792140879212924484935615487499751583687052140626235417350272857134331->
  prime  159926811123282758531108345678618832483025760514284674355193943598460755982148236083677966912439546590289743266661728624666594639115007908983437300183728219060170375582271794657903855650897.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      159926811123282758531108345678618832483025760514284674355193943598460755982148236083677966912439546590289743266661728624666594639115007908983437300183728219060170375582271794657903855650897
      94185360
      ((1698000741551370176119816770659673992678116434595405000896040994040483106739181504255841533253375204587765498644792140879212924484935615487499751583687052140626235417350272857134331,1)::nil)
      156018407872625736303784198347663813529919908715088696682619566578417848009033119024016281483517801467319028558550925577194707749713490269845129723207230552493938358158701414702501530669539
      104701378692971903272627983168539204350431475148454214829785295638418658832789495233514185264436152806595606539646610335422201415669286438984255477209378202271162002257204896626685727551142
      25951214812898677891888493763395952910718298170159654758108247197106099548722442505325122612253295360764404805032745284844875786710760570427111705486284745754396633295501840398272085694513
      26929415303860904168794615736447608433280238538927713461402176874818990979520922583195432795364619587804461673395446473995634079786159997486843143497725551605727618224784375755444101535027)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.