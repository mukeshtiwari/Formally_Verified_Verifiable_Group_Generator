From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo11:
  prime  13260391874991848819295335541866363358830293842774534059330736218851299225908528553110629909397266591549938631625563401260266661148283184357545788148557048050624309189023510277662811692784119516741781186465859043883835435602909->
  prime  1091922354329831293861485290418217121288431673541011721577736826845106074505307167537958337390109447232405837242563213928114217048863209420447201450099455727989422294051788201429018895120492314908744004373037765688664222879068204424857.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1091922354329831293861485290418217121288431673541011721577736826845106074505307167537958337390109447232405837242563213928114217048863209420447201450099455727989422294051788201429018895120492314908744004373037765688664222879068204424857
      82344652
      ((13260391874991848819295335541866363358830293842774534059330736218851299225908528553110629909397266591549938631625563401260266661148283184357545788148557048050624309189023510277662811692784119516741781186465859043883835435602909,1)::nil)
      266521027680699618054037925298683163139037312592509750954263771298891060867623209891568226070994867350304743337699242612673934922653082696684148192569528479342777471226343950838563950758093429153802287812384611187595806393241530027191
      1062970513295158656068931899684258186135432228590283243269306417790460453657066589103711442069886503445254084176981816873565857430203648538980581438000065438194867839089949957909425037471386536630094428070915384058421337199221701343546
      166706547918616859279905229420534220339077227270894611760692774870277574767748511765134448242295047279908144647020832620767800287386802334620147542245045456272953841803834916599300437645949473719769203757606615469166972309788801617320
      939805241131488369478830294466038830365779569767806328169791222581452767411206659021393135967303053968087298825130791526337704893055254683524371063294610602412541655305381619216799612706099132912168914698027767044170226250120325203873)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
