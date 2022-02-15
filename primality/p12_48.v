From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo48:
  prime  349135603251201735849943220356953785505726697745627227741921212482585029764696436764764516751776579867059777523808725155587142753282433513158200285709248698566856210162456860452302774333948507801682060233325402819974620683701567245937489034917080599542749090008768269465027147885064085186062763409030296365059136159558074329726025813275433766626522468260735956433191677484498025305296523588792043690003123203394190765784110154974982066372498977905128809431710924273375647128617653268641771->
  prime  8349323781033322637987693356172129918013605807550716334826249677878333664921046586223378669550541614170591359963848329343953251504825007855580780662928686293173809594714157549122411571776663449563546845940127147546440112126865245945640007778024562869799308834497521311722483800272265987499307967881906062648016229525208855071763002499712681391846678906909663268382165591846517742835612120510612658111722408844920811358553119970901982913040691403238904330424780037119654212100303729894393939594419.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      8349323781033322637987693356172129918013605807550716334826249677878333664921046586223378669550541614170591359963848329343953251504825007855580780662928686293173809594714157549122411571776663449563546845940127147546440112126865245945640007778024562869799308834497521311722483800272265987499307967881906062648016229525208855071763002499712681391846678906909663268382165591846517742835612120510612658111722408844920811358553119970901982913040691403238904330424780037119654212100303729894393939594419
      23914272
      ((349135603251201735849943220356953785505726697745627227741921212482585029764696436764764516751776579867059777523808725155587142753282433513158200285709248698566856210162456860452302774333948507801682060233325402819974620683701567245937489034917080599542749090008768269465027147885064085186062763409030296365059136159558074329726025813275433766626522468260735956433191677484498025305296523588792043690003123203394190765784110154974982066372498977905128809431710924273375647128617653268641771,1)::nil)
      4839289091278756000245898092702348089872433057693761145504961932132135725351857282385458319178835110686338310130937011818672005237859910476012313784886941742268046284098968045522224822886482137159129727282587006052170123073506320772313670216280908647716473656186474502248271429772388363440977610200893236480436316824788108535660798898133160054415034322269545809842699792044173084689840750697635960820760054708430137788450653055141973830703973570671987632862988786245378332333725645520107241645545
      2811228149803637060530127520477762862463543405337771751196808672545020059351300133607768205944524702744478568944615265369248086634009100639023159162566187383932453018522686575012586072622741474496996990209256630770448624491649222370761386391887273972645763568957571638776187876767057955688291526073670512657951849809031904987417620466395443461675800154350812782801284261331720336902781786729484201966529776325807226728186281016865964875932556108120672070258326210529413965088360853298333431356067
      616980182504082006201867191453084901927080590072360109226674512711160846769480755189255762412099164305299506316817017918648894921650381652604915232058282371034951266035950235159398857584440953143036766826613807885241918601022423162828723955239329773540098769008303068712787747852325817277253261475045568337905600683075106918773717987992140464719226013393487610973752376472235005518222922214607637497762462293743912371781456334085370990987113286072715637179189434191439185523109864524202146071345
      7866735637733727479909809427049729599713243683203632647582548291820826363833297405048880264557528255114663857819176467823650400728683554697854729120428499676867672618189000378467443217729547040138481905846796803278609468334169843884656272729246552888955944460767547782272771965251985952512048334506183079285247967449446339122346611951220220856433081782221294630769115445384591270708674709939126760030480164509845130500634398934961038482614493926696242723894251765588207331213281542130159622370598)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.