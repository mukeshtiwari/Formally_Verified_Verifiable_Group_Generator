From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo30:
  prime  116679429418519825285822900646865901925183715315616503306750790253010399793364339201->
  prime  2467653252772275784969868525780566959815710482075434757239118488131894935042454742902117.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2467653252772275784969868525780566959815710482075434757239118488131894935042454742902117
      21149
      ((116679429418519825285822900646865901925183715315616503306750790253010399793364339201,1)::nil)
      1574313616698342338164689776196777188486358601246331051403896324767674695211144790884800
      1798975213739143559490211928936775067769333382523833367266131933946898201976840679100873
      1408210542498377990490973646172040368505953829873491907773917688464678999349584572365505
      74805465227065086080439258312668054450931499950394048937203905742985853889112190037412)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.