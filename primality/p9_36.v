From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo36:
  prime  17216191653853109667782975759421342037994680109024876087016661675105692222553408120370775205189672799940226763460299444842041770449414399941666572937435545130030147347846183713422775944635401089183875374031644273361848972211064778608679572252849915399285116440727741479260714779544019001424838128361986983165620420918821042927610803494197->
  prime  2330825607472928026250056252217065685270391147006645677657976868014183112152797824053021808832440918721337960442550631819968979576196628744921690010405433484373278358826583854067721193701452013927357568102517589689519484858079794399443472580850248421688422329516712738632748395483007256023616693601463654579232650561093051230218556161922729158533.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2330825607472928026250056252217065685270391147006645677657976868014183112152797824053021808832440918721337960442550631819968979576196628744921690010405433484373278358826583854067721193701452013927357568102517589689519484858079794399443472580850248421688422329516712738632748395483007256023616693601463654579232650561093051230218556161922729158533
      135385668
      ((17216191653853109667782975759421342037994680109024876087016661675105692222553408120370775205189672799940226763460299444842041770449414399941666572937435545130030147347846183713422775944635401089183875374031644273361848972211064778608679572252849915399285116440727741479260714779544019001424838128361986983165620420918821042927610803494197,1)::nil)
      2309625646543318959289351969548744670301160991320339150857076685205936562296065938678126984164153909940440773053476583674373185813271977292180877695161856357292266436522291874854226948702214754975516318978294289478930907502836463848899134988166269990751015823853207669056205049820970819144471327776321690659265542975799664807618827575861632335278
      580286684640159145173501657956003706335316402098207451892485374182251396052093925826828892969035498109327043298997127704829927042224756896853174463824219992015914019783657283753593978158909064894153584495894400192129947719666807770856382207750943469091083512033895519440511798034276210794918582480762866576464468725912515589237570249571053437022
      0
      248523947725368240967637953340859430814908812935090854567138669566099818135755572959270938526879583878622588692019401181048642944114490100165160476227070756856465553967085106440433030080922943291214474885155283990428780231843207890212600945016440949619285059503925616983710368358090494147633112721828090262602434939240542681020465935027973318940)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
