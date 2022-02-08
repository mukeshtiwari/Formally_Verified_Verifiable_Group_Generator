From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo75:
  prime  7755890393036004252004636919662234758911344931519556869504685368504660220952642332893404075772305069612268923936681046262239828742594716585089707058921555514494762398009956688245869377807186940610461736187496711684142709867920805139434879005434667853311240472514731173373497892584345820953982408103937661143229542549->
  prime  162532400297010539924987911265257193296572349828199176159555839058956817066982467964902511344864046177269359508672468322066266539930671167783556975678224822753974182273617216454807255195028551939641552631039135047577088915669902429772655919148887987506220859290553134904413628070377729969398676877166927933379016186000813181.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      162532400297010539924987911265257193296572349828199176159555839058956817066982467964902511344864046177269359508672468322066266539930671167783556975678224822753974182273617216454807255195028551939641552631039135047577088915669902429772655919148887987506220859290553134904413628070377729969398676877166927933379016186000813181
      20955995
      ((7755890393036004252004636919662234758911344931519556869504685368504660220952642332893404075772305069612268923936681046262239828742594716585089707058921555514494762398009956688245869377807186940610461736187496711684142709867920805139434879005434667853311240472514731173373497892584345820953982408103937661143229542549,1)::nil)
      54053950443128175446216069964195450292478690724056485640397426159657415383151570328258317462362690194080110636060636871550715739908233525476809336772078265463825531612260317358704434661528638731696676947139718471868321633630431519868584529312651090958414037210000559311046431953915175676618946539568668865196741463161858619
      111440643984670521666239864863535401894229533778594024703285104744916044685241168871832914502627455986423581279281857110940593910360458090181642181359196223362229024566190387922526978995430586320541109856461909940712075709426248009930908782699439347374153331020427248761747735092617224457784204708141101017961715192206965250
      17380006148073828183264642762107285440379432131953082713862086068112930350864608076803714094870254937081269545602194225063479710575283717002581099650907069451683196718454276004377513675370146470081541975449201497081646064266385421091371443387275028746942400325177773193533430739885014935054401244507837624717947122739736630
      45294613297998834248745402290331979574111634692256027657604161934971022301576842121250032835427794797044312316067283704685228193179691331525633430710316822628428618795118775012190886048676141204379774833273167129896849537941759853297574526396004560825788134693473839035404664811643098088955257909206216324138810041269103748)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
