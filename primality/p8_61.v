From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo61:
  prime  588096480855955048208466885948885580051126202756128471552138227084621146328247134143346338892871457143906059740633187917714180176243729635103973395491954831613->
  prime  9687713329140147509138075012235992160182201938001704311878373014764964143465215035344399227162063235361728035715813101039954338805868009520241266281767472475219257.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      9687713329140147509138075012235992160182201938001704311878373014764964143465215035344399227162063235361728035715813101039954338805868009520241266281767472475219257
      16473
      ((588096480855955048208466885948885580051126202756128471552138227084621146328247134143346338892871457143906059740633187917714180176243729635103973395491954831613,1)::nil)
      0
      6912
      24
      144)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.