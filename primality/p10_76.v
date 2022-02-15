From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo76:
  prime  146440988895383073912765307338536846901416971242226596644340873001612747059222723312086642249526718911976202888524773040396359744710149831019130343459036689676321185178496439015951414205778052893214966977724728224476859038555492547180735032037808420252359826094087754494746140836757384558876092866851681988111->
  prime  7755890393036004252004636919662234758911344931519556869504685368504660220952642332893404075772305069612268923936681046262239828742594716585089707058921555514494762398009956688245869377807186940610461736187496711684142709867920805139434879005434667853311240472514731173373497892584345820953982408103937661143229542549.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      7755890393036004252004636919662234758911344931519556869504685368504660220952642332893404075772305069612268923936681046262239828742594716585089707058921555514494762398009956688245869377807186940610461736187496711684142709867920805139434879005434667853311240472514731173373497892584345820953982408103937661143229542549
      52962565
      ((146440988895383073912765307338536846901416971242226596644340873001612747059222723312086642249526718911976202888524773040396359744710149831019130343459036689676321185178496439015951414205778052893214966977724728224476859038555492547180735032037808420252359826094087754494746140836757384558876092866851681988111,1)::nil)
      4022633944827356993447037146579916356435866812458280467760304903445069734927441496160136704407580349809675344112488102520262420648795005064393768528939041731716241732399755061596716000039545177751335063689890267226110216320143920834002776023889529145162142982385755904970095788420790513128911551873662116236475528494
      4457153412142832004661891111266607109412423127807925183739284960978715772123866716213988730461214632603785460636693809153257739170999421256395390300738719807362445352541977976552039520907674158273864694330809329085723820810948956152950450295478102935731871855212675078320528455578959440237487804374766445454948694931
      1212240825794854259828317990590474195875111075190917349205766976472162619697876203778731105594442291967287032152988154601466605997799725488969725560455486964414630135246141227051794119273883907592958986193893069066786720361359499021106702276025616785247599026745152605631184348894348743533837601534929990660153601202
      3464780881213539915507331429316999296187457946449276917674790360574034940302043554937645840357961452425442614407404431887009794668734028118027414964862874405577413799030949390484500903636373988953043682887999625610733716637868978857406081047703808181135530188303914274736818343927855239593708548879366794578112519553)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.