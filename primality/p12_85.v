From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo85:
  prime  1503587477180982375807887367618033874899302564456431462683332933213884476334694603330518986175675301139053788205883890443989748843739978858786108764547287179263097577372175387124551704540795578779749->
  prime  143572170316968927339166014418196305972523513383738241782680428627363590799929946118405301426754863831445516154336024257488128365384519737314195469424802088991659009320034484721865841716584793428116274671009.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      143572170316968927339166014418196305972523513383738241782680428627363590799929946118405301426754863831445516154336024257488128365384519737314195469424802088991659009320034484721865841716584793428116274671009
      95486410
      ((1503587477180982375807887367618033874899302564456431462683332933213884476334694603330518986175675301139053788205883890443989748843739978858786108764547287179263097577372175387124551704540795578779749,1)::nil)
      85079804632277882867653934470042255391125044968141180315662476223622868622180708810906845289928808196412157721088014374807779772079715399889893611510993830513575709226687102057401980276494692401846681291872
      0
      47857390105656309113055338139398768657507837794579413927560142875787863599976648706135100475584954610481838718112008085829376121794839912438065156474934029663886336440011494907288613905528264476038758224303
      111667243579864721263795788991930460200851621520685299164307000043505015066612180314315234443031560757790957008928018866935210950854626462355485365108179402549068118360026821450340099112899283777423769204607)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
