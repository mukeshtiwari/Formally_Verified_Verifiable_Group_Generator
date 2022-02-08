From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo22:
  prime  19244471567549755883258773599930927090271032217869035551647885892130289548217088838738488468686964717770362220652417090880060674491254941142183788185222869086073454450203247169105278086649562589514397935159407172244937697289635655432808741844571823268036516412890967297623927913954960004842510121173243898332162316402430425673403830595063753095203202689868685760516839809323082139297423335556563052917795160166494464805486037->
  prime  47877262366970822425385923606720157306895336148064390751989434677306880201084143382011354844380521738281406798839012597460504548729696149045876226517665788741442413286665897453422720561480681040510447330996655336433860528993876768646978089916738540677389515648899003588738623116797587529973392480233343504925301596090596756230018008843560914443324686187301692516165696343916971331601063037295195667158674698282472745205565713770147.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      47877262366970822425385923606720157306895336148064390751989434677306880201084143382011354844380521738281406798839012597460504548729696149045876226517665788741442413286665897453422720561480681040510447330996655336433860528993876768646978089916738540677389515648899003588738623116797587529973392480233343504925301596090596756230018008843560914443324686187301692516165696343916971331601063037295195667158674698282472745205565713770147
      2487845
      ((19244471567549755883258773599930927090271032217869035551647885892130289548217088838738488468686964717770362220652417090880060674491254941142183788185222869086073454450203247169105278086649562589514397935159407172244937697289635655432808741844571823268036516412890967297623927913954960004842510121173243898332162316402430425673403830595063753095203202689868685760516839809323082139297423335556563052917795160166494464805486037,1)::nil)
      43533324067250302938106337342314149417904719144606626704337879164434536902488548392311583009269903382763014513916151289155724666024453343891253387779222565363181858409378651246564469640861055841078901179089198262772612831159270741751520761050987694851752301484888648370291017496736849605900789398245032634361148003205386285456861972703127057121215760819384520950351760016550725806048860055510053120680811611683996857808847278332580
      30896692094215727819861083292532374667336941774219236890900168073625193072187104830548537571716698208606843006356664646836886326718773415294948616007549169749155306392220125307539706840066939998796872711556109468191132031012084149927842892419616193457552464422697504962418914837360913583180153541105453814972164565315132563343133588098889735814404106903140951371658791642567774487345429409068504203707070016524254838739821068348309
      11122303898080955999556686673448899066923516911153664549728568068073939759479842015456337911485811670597678717482533968828662445806078840929859786779359477935464402866219275841304559926510677813778429089009413781451074167824801308986198682350034004284243486471509368817654622113690517690780864785499650949776326541342072051807717205671564402472474630432536580489353465329005681223499073005047175078717121015122535374931632941760920
      6741165508085204718253691518037989157064753001237659056561550819341980792744366661448240099383626499090203610203111823994648175555965170531198956949850265860807773902479913741934786816784608833416812544143325459270206874744727165603500393034142179306338085018448082527630026800835628022977078301110961930381451821892372047238357372630183016753191285987238464533525297704454976344285692243415897008834151345194599558082702376086603)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
