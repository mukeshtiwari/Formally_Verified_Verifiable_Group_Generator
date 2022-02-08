From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo41:
  prime  35974555098463352789273853506286430944128844666105589886591411701654129713582726074784849628582096458226343805791028035379493194499034103249833273410704556730024738371847745179541557019858463137715848019484911449445683640825180948887565623940548530179593032962669->
  prime  7482851358700771233580118624721602782102576205928627118770559999590865596944061354459547862143590391696912416979756995471076102428577231725088433307571192176852228288221573960568893068731630301420150099060187994823202640840439240155080713556229457679761276315603520179.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      7482851358700771233580118624721602782102576205928627118770559999590865596944061354459547862143590391696912416979756995471076102428577231725088433307571192176852228288221573960568893068731630301420150099060187994823202640840439240155080713556229457679761276315603520179
      208004
      ((35974555098463352789273853506286430944128844666105589886591411701654129713582726074784849628582096458226343805791028035379493194499034103249833273410704556730024738371847745179541557019858463137715848019484911449445683640825180948887565623940548530179593032962669,1)::nil)
      7482851358700771233580118624721602782102576205928627118770559999590865596944061354459547862143590391696912416979756995471076102428577231725088433307571192176852228288221573960568893068731630301420150099060187994823202640840439240155080713556229457679649382483155719699
      14406462054002124060149776
      0
      3795584547076)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
