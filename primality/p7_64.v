From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo64:
  prime  7020586362815189794917194588006237092990633337843999758065043029743167382837699005891->
  prime  51514012980601269433840272062543543290965835208545510922860617684780188579741569695840189580051.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      51514012980601269433840272062543543290965835208545510922860617684780188579741569695840189580051
      7337565599
      ((7020586362815189794917194588006237092990633337843999758065043029743167382837699005891,1)::nil)
      45841468227401205891327480232229823241246319834332647868672204645736848479335155540791036203077
      37584570273225039238681742326572983066165838768744585241808748983362043486105144537485980022271
      0
      1195377075772740548416520100312890402697735945813454652348633014524818292842699397083219326192)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
