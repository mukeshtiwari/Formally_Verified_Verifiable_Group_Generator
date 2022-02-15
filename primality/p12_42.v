From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo42:
  prime  16343954230118816815699956484637324009087638197989592846247708712668274761130949869158159168232074524191720613805773325527801053454078738339883239222675582051564019056270766771446286440370735406589483990701712663928956583821443556194153710730889785371915568868780773695565454600551630994635085204322474629106738897894600947247585511053929749618102576498954097272623717803901213478111082795997153030578349625331643093929482326836425697768729578291991935177119968699687264299936343351307927335140749807159064652019136134048913209703339->
  prime  39939677344182332466052277890817391763388701617895641196131389618215163552522320934843541806765767898489892762588278252619418314179097781852320512788086027275426137772863974119956260361632976325122332046287564916936121965718406323530214112430421969774434280034711340196987638147321353168649986062241458126371460732582503213104182375052798257434102258935324037786398333134899527935862507910771087414876094649302023639136890605805601633088055918731152526388081157742295972004927892427989446417980900307396890548143184986386830159677240143775083338839.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      39939677344182332466052277890817391763388701617895641196131389618215163552522320934843541806765767898489892762588278252619418314179097781852320512788086027275426137772863974119956260361632976325122332046287564916936121965718406323530214112430421969774434280034711340196987638147321353168649986062241458126371460732582503213104182375052798257434102258935324037786398333134899527935862507910771087414876094649302023639136890605805601633088055918731152526388081157742295972004927892427989446417980900307396890548143184986386830159677240143775083338839
      2443697331859940
      ((16343954230118816815699956484637324009087638197989592846247708712668274761130949869158159168232074524191720613805773325527801053454078738339883239222675582051564019056270766771446286440370735406589483990701712663928956583821443556194153710730889785371915568868780773695565454600551630994635085204322474629106738897894600947247585511053929749618102576498954097272623717803901213478111082795997153030578349625331643093929482326836425697768729578291991935177119968699687264299936343351307927335140749807159064652019136134048913209703339,1)::nil)
      35685916375776628511815507782584324799325677694565757324611220790641293062437554468843896848277125259808903758456635396724508514674365993409813093200883212739173138407142670815381617219298257404784802585208994324355981615405909274125207406989739997340593994951533225515679004713377115341048774074034545983121102671803813572959586486717202714843728917524093518296323563475942038758573010826498726769792580843343625142566601278639974087224747403720786451618663021009330147414263914214662903198587801913976061011678573170455772844980653546075654216378
      7289719419146587345048958633954056473825450493476690780080636092065774103400255229601807118050066557014524033859407655579589277818817501179230370464570056271998115824965921945901211798485011001013566853853447607156509069585077352549138111104104462669725354472590373501281114683444473943268815042512049007928696882229370721180660672796182515743233612155240352101692635706051086730789682004867310650857590162954505592979166430683396624953010003714578478818858261224999044264008947925280609721617125032783792574778191845928626174901829132674759292546
      0
      31162424553487647343795251233094902978562461313598296300715988615382422510275027577285792866543134807527667587567022193438925948743756221068267670690308179183048394638811141125440064720294746596727962120989394458304422218990746104699342577405889631155737122678932359384400025260497375037887936174594217643777848839942736732124331693953692709454414435592069928316041142611871658324323013574817502222379242833887565615347324833909839222626739580675821894343887260864528827776012055889594227914948860276662262158965681753557131414434704319264802944230)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.