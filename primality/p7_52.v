From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo52:
  prime  3348886389900798059444963571273477560464523547687345226988911917001093384421129691458469695271885297482755421079056338640157461000081944292143581395682185173922356845453188873->
  prime  145242637171307790715551623128635301098968364746227216937898906803757439419368923829676551900736035547968971467088085849237897311410446384003968773281533646459824353277896087709988619627427.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      145242637171307790715551623128635301098968364746227216937898906803757439419368923829676551900736035547968971467088085849237897311410446384003968773281533646459824353277896087709988619627427
      43370428333823
      ((3348886389900798059444963571273477560464523547687345226988911917001093384421129691458469695271885297482755421079056338640157461000081944292143581395682185173922356845453188873,1)::nil)
      56324906506949433182603284478803887464206455608452424216659779915517389588525885295447544714346088525711386967229746954103930594986653988693643128154711362949433105523977345195287712216739
      132790796565591696792723109849347145922912085846768533040482383545154023967486447870423589617742763522823685428372252117913678113492801259551069463776255258768326531808344476293898897419662
      0
      122391366572332116445112559861698830076295836459688616671464238787020489720055562831933815550685501235050784410906620368115264550026881312341968486428930471678173683133876095205782156489604)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.