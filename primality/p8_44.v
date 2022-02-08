From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo44:
  prime  589812878359484771587455375619002482465924185481289114609831941413447736135907372349312919240096685458932829620249466636008352958798806208041022994155780479966828518306793245429914757925372837378927079650062126941329909774702013969746360491610014616301015337227555090965113922353->
  prime  160148351983680743120512233409574030049077598538621545555320008060344983106566113369774841083748012422551277629808616178875532028784887056832109054257980786776272818550429778397899036759963796333972553567013789087582048737500794577795371706206687069316621853385346483135893914711329089.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      160148351983680743120512233409574030049077598538621545555320008060344983106566113369774841083748012422551277629808616178875532028784887056832109054257980786776272818550429778397899036759963796333972553567013789087582048737500794577795371706206687069316621853385346483135893914711329089
      271524
      ((589812878359484771587455375619002482465924185481289114609831941413447736135907372349312919240096685458932829620249466636008352958798806208041022994155780479966828518306793245429914757925372837378927079650062126941329909774702013969746360491610014616301015337227555090965113922353,1)::nil)
      160148351983680743120512233409574030049077598538621545555320008060344983106566113369774841083748012422551277629808616178875532028784887056832109054257980786776272818550429778397899036759963796333972553567013789087582048737500794577795371706206687069316621853385346483135893914711235009
      9834496
      0
      3136)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
