From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo39:
  prime  459613878601185732079450934625605356411985484558293244602104263592763666725579880311079867796679616819861135559153380435470022808839413955560790202758240282040456016331180891864625853634010057280352074011980999947842351727572664678819049118905851021978227241412920566311859973214762744414286865148389->
  prime  130361332307297519893163809735991393619344062312173505875092525080536550294536355774758692165270816148143563162031748162619755440923127134079525603809981962354418980562298155503255454694510319239001293523514783222684024346429690829025097402809646197239751197691706250344521657485150562393220462008134084917237.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      130361332307297519893163809735991393619344062312173505875092525080536550294536355774758692165270816148143563162031748162619755440923127134079525603809981962354418980562298155503255454694510319239001293523514783222684024346429690829025097402809646197239751197691706250344521657485150562393220462008134084917237
      283632280
      ((459613878601185732079450934625605356411985484558293244602104263592763666725579880311079867796679616819861135559153380435470022808839413955560790202758240282040456016331180891864625853634010057280352074011980999947842351727572664678819049118905851021978227241412920566311859973214762744414286865148389,1)::nil)
      59739303587719242070123637927645237426985093830069078081199269060893888615340600414969286914897542929479731606549633497581376745626294470203243218022426812935689891373201014091351747192937061138246351451760685202772370837752338531620408304876864564611757415252246796659439119662372391684526270661538260120141
      31463977000457245265064807022228195854938749861537024049902518152641204646620127762408465404195182176825114646336594027990392850907528294052713525821343791991046505261842258709109627770050528902263854512092697312044588796518097243076057058477567670999003019505537012212385823567581967538548929555407305110481
      1773821493695204935923783793864203091078586672638876752994729421707817548669355209826080917771225054769557449528428334263286490983717129963955470830745322141066022893520642069102319250833264019054418665667298147823125677528487264485606008669743560864059523631375631150268073086339999414032405470938505047791
      1919842928594327288284853390797647438872418709724382795133260175461311396264909153298525036645962816484064747663468183243700502288215436675136713385178664655564181547124333486215926782595016467891599767322347783156649461711362176134607805833677391127828241490389791216425100842468030916256098433640829712650)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
