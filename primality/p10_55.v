From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo55:
  prime  95186273253400984877058233491333022338937403361052651688643843562362586904739034288528219571861778111654096724259463367857758526567751276350683236480534227457636626603027278620186717411319676232971439202230361921348809513371473462029550202322144642796571149494996116093384338444945987607627825368384892471494131907801662001027072737708452228116359312951483299763635469569727795750668607914733116072339821696921912348629195840811158106579979900753828003427265702007123448438613373->
  prime  1527024653476190479830061066988217393234778879252214680801144821582723475683064531655991037494045961332645087112174907560497966090834962003854114062990692077137938922504656249561020589724304058568985558984396655323942002612359606546416550956337221607707163801431048891680240814044636883517974377838760623032520723596071006784154581221231458911936568719452660156291745979418827230811953693971399551865450151436711140095018154704341628338399888989450704294974187146462848253801472235056492297.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1527024653476190479830061066988217393234778879252214680801144821582723475683064531655991037494045961332645087112174907560497966090834962003854114062990692077137938922504656249561020589724304058568985558984396655323942002612359606546416550956337221607707163801431048891680240814044636883517974377838760623032520723596071006784154581221231458911936568719452660156291745979418827230811953693971399551865450151436711140095018154704341628338399888989450704294974187146462848253801472235056492297
      16042488074
      ((95186273253400984877058233491333022338937403361052651688643843562362586904739034288528219571861778111654096724259463367857758526567751276350683236480534227457636626603027278620186717411319676232971439202230361921348809513371473462029550202322144642796571149494996116093384338444945987607627825368384892471494131907801662001027072737708452228116359312951483299763635469569727795750668607914733116072339821696921912348629195840811158106579979900753828003427265702007123448438613373,1)::nil)
      806611860308348885210720735104582702676951789089160362413744582926844954166795664440737131654566464207251488164578058972086688101976742440254919871437259725039469191959076733262677835626929504726948497404480801020853939382287995618839201644019290946599992943805303228609736960893345879515578632184144109281612519071140785298214237628578559613160369395541690930249229783264880678982331681035518163009633199591177624788174123808113380665443437649145624982786247925642342867848561807763128783
      214827855781218901472736108311530839683886238861957516737173216268937096032637764587896198151662470340556921818203290969009360896855273015244898779019529922857431133413669166245580267242819838603132075504666085629587620748829666907728501013023561216991657706461578584769846679197871876262812499282686622373961565258667913801902744243292574610001899346349449564367419983135729130528840162231088214399264670619428974999628113387246561645411893912853530673711217489666506434438469046360629852
      944392864051043625487361250255885129782695168465124520630698249413168244982505498749014132319329112482778382867016604048190944621342426365474274475282773851136879275958356760920116407371858476701973797991969456220602018149368510140853821035582754666842151801442929411818916820433877808783252815284145863736799488393341513869587646106133070170255409849624296567917828324117668359586033863682305802665891538212293245916488444897016583220975815505291182835179752279777222741194860137859631553
      301952614799254428285235265357878586342812877278480848494262597921923996103452083139751054933625038730021915856397275186232282459205695484802912281506972670843217599231219741743929425870474729301183384948814527318105671438569993614078946957278954363079404583309239539562220008292434578044315434059416876959531086130826667270015856426480920288567834485185857731380745673332080066626646286431135295479930075170602486079917189644072945874010022520901643816316373112674093748831562853386964866)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.