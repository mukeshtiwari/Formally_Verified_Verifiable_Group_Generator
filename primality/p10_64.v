From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo64:
  prime  80121617907196449266641295914361801991039615548700782103919172911509933245042565173961031217511040015409650486777147783036472746501773426453045404804266599807025452944285188207136574159574052199366246878973757926167708325553429068995235886352058361200849200303442097653761655956120284695029424993064393293827276253814025817668591553724947317293055874141700582747326605941446361700151093160077312715351493834590619->
  prime  4390274145023334556401573638698523129454147317376875407539961760929530034307259171288533756999165470464927979360890525273909684286525933279868325276036795862629804987780057938195214399168195033573592321108358953532352379101443948918052120415444547653836272340467453452045305428059855059078793622617741161740621352222474882707214262596130346190084773488333495194751438258436774575197996615675195030729333624972217634925917699.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      4390274145023334556401573638698523129454147317376875407539961760929530034307259171288533756999165470464927979360890525273909684286525933279868325276036795862629804987780057938195214399168195033573592321108358953532352379101443948918052120415444547653836272340467453452045305428059855059078793622617741161740621352222474882707214262596130346190084773488333495194751438258436774575197996615675195030729333624972217634925917699
      54795125956
      ((80121617907196449266641295914361801991039615548700782103919172911509933245042565173961031217511040015409650486777147783036472746501773426453045404804266599807025452944285188207136574159574052199366246878973757926167708325553429068995235886352058361200849200303442097653761655956120284695029424993064393293827276253814025817668591553724947317293055874141700582747326605941446361700151093160077312715351493834590619,1)::nil)
      1189054182322440557313830671380669941174658751314318492392848810335026991329423666233829215277119181656690887671859630079789539468671242483317007901517664398057366111747421375302254424362435820057923452140366784419101144565890617371102928081970794438290072339780813188217870347506169475333810199806108860790778291790802131765220649961299003846610918873791610867420901770796315062589892674682074888908805099338352867128432125
      1545132933901173351701377437648343681648097460799997234930277979023426377891082594076403204402881361773608193391749384809897584691372375102179877380303440038690755920615564440957252096241912502577693730669611083233190416878511296468836656535051425259812382371724903002571345300632925407126828465734423883120660164300110472318297321998500107982313019605462027416863610534238209043657861842939523498783094923357004133486895759
      0
      768375945775001980511049288861751957511118269611866568060779744107710150986170670209767620194932124555878632492438740354817389123685031658276954700467011553320383710364883945244020786615825755036424785680128920415606059472726797608729987751703541887985334758818478828772202786253564522381590898591203331617115774232358642882540532956441559808864751710761465301380076262450047734154626892470976039882732189543881803517212099)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
