From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo45:
  prime  43375579525332873944257391821241550757895975601195456681035702306636095653839704082624814071715317980084777795442922652726421869573697304958374600461792677759201278317401627009120930071936108665299065669965193029678459982477039178463051->
  prime  3678167252172229165393670656534533713965202099905798815571454744033035563229275804729665880524360058700878886296049267553734280251627573427762611210038077789853000682235233163432562727361155378437613589190628126533755557173081739919597417732075263.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      3678167252172229165393670656534533713965202099905798815571454744033035563229275804729665880524360058700878886296049267553734280251627573427762611210038077789853000682235233163432562727361155378437613589190628126533755557173081739919597417732075263
      84798112035
      ((43375579525332873944257391821241550757895975601195456681035702306636095653839704082624814071715317980084777795442922652726421869573697304958374600461792677759201278317401627009120930071936108665299065669965193029678459982477039178463051,1)::nil)
      1395327779302997900971687741800825847817466736951067937366059587442374358360064901852016472760808551706602590029134963028624920077211430530686412030793781452373780139749946598207700758994764125476181180390233280651683461671813199729722542487302051
      2291119285703910215743566525915220543280289133291099757692301113007663707649141139495787535789906999606488982434391073198469484594838744205175075072258028007426396892098341382025919158982585538397449640310557716411644922083044251064810177622223075
      0
      1338141365739426218464908997339978600320377979725972363955599762349620806342870901170821763544555858908061592640649504795424101784340431436587423037043568429775094582917661158293029498701423651452491465833610530885982755289610756717864020752168675)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.