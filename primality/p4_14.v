From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo14:
  prime  443250520062634172197390495177936741864408796328803827435085222083308873945057852985178858067979826427241526361997109950343178312541984445485432367005320325385366324294491413177944893255624611290339454738180659785871738751785974821731021944706996298769489833920198207898165110175504323908382526667104909356570782403799209682302825138775854245303245810439747321879570150570293237306767780555457564516328445377826936272486535011014871260866103645926283214599977188951167022559297608928373953018189->
  prime  1590779393910724761810977332458908755417339984557264713781874757158820969083718959760581606887729509361845969011155335858418911239630435436808802591241720983997901191814052123850272547901183547786376799663745891086326301426049776627372653914261240096511971254184528126325158784064793729618055640927666541770622157581912723279211768763764277391939811258534129515105107158752001066453326395110874196138812661820635285766028528785412907384945061699825809360752033567184922314974804656305657187881772522912111.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1590779393910724761810977332458908755417339984557264713781874757158820969083718959760581606887729509361845969011155335858418911239630435436808802591241720983997901191814052123850272547901183547786376799663745891086326301426049776627372653914261240096511971254184528126325158784064793729618055640927666541770622157581912723279211768763764277391939811258534129515105107158752001066453326395110874196138812661820635285766028528785412907384945061699825809360752033567184922314974804656305657187881772522912111
      3588894591
      ((443250520062634172197390495177936741864408796328803827435085222083308873945057852985178858067979826427241526361997109950343178312541984445485432367005320325385366324294491413177944893255624611290339454738180659785871738751785974821731021944706996298769489833920198207898165110175504323908382526667104909356570782403799209682302825138775854245303245810439747321879570150570293237306767780555457564516328445377826936272486535011014871260866103645926283214599977188951167022559297608928373953018189,1)::nil)
      1305508717772380600535135719584743504279563391358868743161403359184505324534500953515071377002775286228326072274728318939963472765777671214998835724849014133517410001930913206740382106693030662622605349883624055499256690782026556907852148958666576174284773573587223884693566176367605413353064407048654926787645909514367845277326932632879228734847756258925915122622622705749748706835030420913833734125429108759777564692991154964394609748329718089444774595642763821770359988013115359221748781862410978002592
      306162620885157117267558135654192398435921076360466033220697683771106707726710695334037854614739931740965874333199036215153060446358960552761501950564250742398058789445758107929701724760048193655402157851501585488381677877347269746999855413338226763421561919254610463443509873738665793722995802046126772148291355327256283082683501582747050010449501764631490324717008265013634345086445796542696011878833828447982877231449897570555041140252984043354875653914209141468979123355129427324327538319783157403579
      0
      957175848562125237580576990194134768773367957754820675881530961502647571585762424175327815472406026075706429623606863400743041634455861569252037226170590959486998900760075325188811788521077840078619442811549828875106944926551782245141793832262602861859286466041255685866349629959275864411328802321184513272828832202406333435696618316214984850753772701321247013768641278772958344831075516523461579559760674219504299286507553355177344667415488590019949592929407001418821476131711700413727719253649835913402)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
