From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo71:
  prime  7416560887733316916132600068086374553691020818541555045585299108855660734664095255188181655050878543424806782517763405088252891666150700336846147150693787459421828359471398654594682010034403032709751163608759412617175005937432053859057756105178534595690835915544421356945193203614206892328986723038863015890672669->
  prime  248276792277760517084454919879259474559360612921497096706013472968052098753615252762679569084483210119688831851564647748734353801416060844476261622016625228990609892005717475113194126618818714480297895847757244307174170632452688893139469734858117080258358327430753296167815766133380296199891242278696152493913381287921.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      248276792277760517084454919879259474559360612921497096706013472968052098753615252762679569084483210119688831851564647748734353801416060844476261622016625228990609892005717475113194126618818714480297895847757244307174170632452688893139469734858117080258358327430753296167815766133380296199891242278696152493913381287921
      33476
      ((7416560887733316916132600068086374553691020818541555045585299108855660734664095255188181655050878543424806782517763405088252891666150700336846147150693787459421828359471398654594682010034403032709751163608759412617175005937432053859057756105178534595690835915544421356945193203614206892328986723038863015890672669,1)::nil)
      248276792277760517084454919879259474559360612921497096706013472968052098753615252762679569084483210119688831851564647748734353801416060844476261622016625228990609892005717475113194126618818714480297895847757244307174170632452688893139469734858117080258358327430753296167815766133380296199890394446453768990329487758001
      9501955807025115933281263315351902213136
      0
      97477976010097357444)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
