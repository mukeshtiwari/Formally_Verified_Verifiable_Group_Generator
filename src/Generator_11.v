From Stdlib Require Import NArith
  Znumtheory Lia
  Zdiv Zpow_facts
  String Ascii.
From Verigen Require Import Domainpar
  Functions.
Open Scope N_scope.




(* 3072 bit prime*)

Module Pins <: Prime. 

Definition p : N := 0x9d06128738a30a2beaa41f483dc1ba77244ede05dc8807f3157aaa29f41e7c3129cd53dea180d839692f960b69767bdddb3c6e741d3b9fb0a91cc36608999cb0aad8d09e92ae89ef187410da4f312f722ff5eb0b3a334518bddf8ee4bd6621c5a7ec01add516f46ffe472f9c09890851441b5b1879838a4d44ee8901dfb4674a730f2408467965ace8d957a9867c43b50dbea91280ef71613459b706c140f1ec2e8e427b58b615eec83d7e42593055224ef30366f9742426334b8347f09bd7c91688df12066c18a50d4491f09bfc55dd5c7b2b2ff405f5fa634145af7c66398bbae91ef046ed5557f878ae70a40e54db3ef72f2c95cc16fe48c8786becb943fe4dde5074c41cd0fb4d6c53c11b7f8c7ecb5d2376c73ae084019218659146e6e77a12dfda2afcabca5d38b3b3eebc04fa18167381ea09f7e09bb959216c663cb4cf63874d191e54df4fae4d8ff422b797ff4243d51520d8f6a1db434f7047bbbe23a2eca25b200dbbd2c01e671a6f3b4e2f4b032bc6ae385b4095c3f4969a8b43.
Definition q : N := 0xe9083ee9f7242ae652c554bbac811515d50f405cee5aad220c5ece2893d4a62f.
Definition domain_parameter_seed : N := 0x04c3402a6845731fb42897be90594134e67a7d6e78c1cea0f86bafc3c4d0f087.
Definition index : N := 0x68.
Definition k : N := Eval vm_compute in N.div (p - 1) q.
Definition ggen : N := 0x6767656e.



Theorem prime_p : prime (Z.of_N p).
Proof.
Admitted.

Theorem p_len : 1024 <= N.size p.
Proof.
  simpl. lia.
Qed.

Theorem prime_q : prime (Z.of_N q).
Proof.
Admitted.

Theorem q_len : 160 <= N.size q.
Proof.
  simpl. lia.
Qed.

Theorem k_gteq_2 : 2 <= k.
Proof.
  vm_compute; intro Hf.
  inversion Hf.
Qed.

Theorem safe_prime : p = k * q + 1.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem ggen_hyp : ggen =  0x6767656e.
Proof.
  unfold ggen.
  reflexivity.
Qed.

Theorem index_8bit : 0 <= index < 255.
Proof.
  vm_compute.
  split.
  intros Hf; inversion Hf.
  reflexivity.
Qed.


End Pins.


(* get a concrete instance *)
Module genr := Comp Pins.

Definition G : N := 0x7c14a255460922d87b7941dcdc2e9e2bc433a42b794aaeb6a465369b5280ddb014e37bcbceaef60c3a9c4e7a302e03a4107d1366762976655ada3c1c5b1277786a3317ac679cef02dbdf5afd64d3a62c2bc99b9a2f4399cf048269c4a6a5383f0be6071d053605011c0b4842bfb98672e61c85655f32953c88849c95375a06f7469877026041e0318f2db329c325e6577d4176d1209848df52c8f58ead26783c8704dcd93e7716ba2c595047244144e9af9c6594b845ef8b56577dafd22487d9295d51de911d8e37fb98371409ea3b9b6487ec7538d2a333ac8c0bb86eb003eb3fae779a9c9f758d968b9afb0ec1c1e767178dff3e9fbd7dcc61ee1a0b0c02df91e7192431815365e721435e73be5784fdab675bbb22b42f02906719fd87d9d70a5930c0a31f0f2d020c35c0a2bec7ae1266588dde9fd4ea5a91bef7296b2340ae5acba6d139b81d8895f0d39eed9c9a2749f69bc22dc437b288c4602a5c6d629b4affc610215483a8404f9f6125b90a1091198485d04e9fd2099b549c5ab975.


Theorem G_is_gen : genr.Valid G = genr.compute_generator.
Proof.
  Time vm_compute.
  reflexivity.
Qed.



Time Eval vm_compute in genr.compute_generator.

(*
 = genr.Valid
         2815857067680651424347728195758246993191714291494761217484085964025213854469287867033561128449900900542462959417353120442070851755032021214983970103765146890716305532795232886202363258275657863077915583611655753362163656499220264084336345455815303397349442140403382571439497917600111644650834845541746126249643813462066176659367193455120967628954142480075772577080948417949213511906413145103570460433944152933121864621552213123281686253383669446690860954251216167486044861167685492759490205462427228551444743543073926251592860014822346807308315112641756207739293679496794973286349904658615276240292724715580842054385093926991100921590637938925586397890638618258362890968509121690608946555141641898453203613149349214698377732472649750557446967482753177687967393915835032845286305409022430101066346395788534519697210466132849239485539531264233037800600251881786274602063793159587693118604019689435792492692309345753911927683445
     : genr.Tag
Finished transaction in 1484.13 secs (1482.492u,1.759s) (successful)
Finished transaction in 1483.557 secs (1482.168u,1.214s) (successful)
*)


Time Eval vm_compute in (genr.verify_generator 2815857067680651424347728195758246993191714291494761217484085964025213854469287867033561128449900900542462959417353120442070851755032021214983970103765146890716305532795232886202363258275657863077915583611655753362163656499220264084336345455815303397349442140403382571439497917600111644650834845541746126249643813462066176659367193455120967628954142480075772577080948417949213511906413145103570460433944152933121864621552213123281686253383669446690860954251216167486044861167685492759490205462427228551444743543073926251592860014822346807308315112641756207739293679496794973286349904658615276240292724715580842054385093926991100921590637938925586397890638618258362890968509121690608946555141641898453203613149349214698377732472649750557446967482753177687967393915835032845286305409022430101066346395788534519697210466132849239485539531264233037800600251881786274602063793159587693118604019689435792492692309345753911927683445).

(*

Finished transaction in 1490.535 secs (1488.985u,1.676s) (successful)
	 = true
     : bool
     
*)