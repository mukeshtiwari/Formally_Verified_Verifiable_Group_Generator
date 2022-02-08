From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo49:
  prime  13077874726514839914774520020603991781151601347004061509221091594920597196463202192547709694815265538561773585950616063643661417520554103617030511625082259337752327750541144915174575398684446395858518243360942030347101499816219450277252273139427->
  prime  276597050465788864197481098435774426171356368489135900920026087232570630705196726372384060045342866140581511342855529746063471661005567001303572769666675778516285456705309378091523294612649684880024538043887087114164290857210592073273617740652629391.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      276597050465788864197481098435774426171356368489135900920026087232570630705196726372384060045342866140581511342855529746063471661005567001303572769666675778516285456705309378091523294612649684880024538043887087114164290857210592073273617740652629391
      21150
      ((13077874726514839914774520020603991781151601347004061509221091594920597196463202192547709694815265538561773585950616063643661417520554103617030511625082259337752327750541144915174575398684446395858518243360942030347101499816219450277252273139427,1)::nil)
      212569666815605272306088569180902515530427103521933771222844094115606580950272993938875075241097130562072970678337746357137463276716054805506010275327017118479701993495587014871987611195938462686563561498734005191381223890313757069289203899658264826
      16960319805448794491307970973162737339208201417640155570919253082995830743358777125362512729884272582848801501352354751241801484232547833508687443683919799445510141297864291993050524959300419023815639297877660904648546769189109711021112945050037588
      0
      161758040601706302624594101858826007633576788931296254800461208231835572145363994457264653276863224636058772453463379392574671027041545366045552795097927520127215449677071551130528735829579290878943973943745630408124623055651986916708796826219061919)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
