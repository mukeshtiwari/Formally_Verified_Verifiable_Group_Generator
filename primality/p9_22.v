From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo22:
  prime  12784537450109455543241633780534751244068919613678660781647058068239898229439033130682404214404489904359933891912338532530526041310466656735638175109591939910259156438784606874667677544345811547025064069346562391940336138559203935646104755264625701417007348362257013497367037491118345896133136267314374044746938033570133474998382375883070043447546232024290997373877989695217664434133035144003123102575730850834215331400865889483795418161142793->
  prime  5779965794374824155315324587424867293651744357276653496738126857117331859401104235482537034062259381397284471858440210604459758230610888169389327876419146064453008244952555383632546906507423955325648034559523341799642595631718893361441822553266125702667275609857151548249783637036167985467219722392955081963313026203671256563002619676038176516831151339132587958284369935827743723813900803597058319321952348407304826025973388498135061870337904757649491.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      5779965794374824155315324587424867293651744357276653496738126857117331859401104235482537034062259381397284471858440210604459758230610888169389327876419146064453008244952555383632546906507423955325648034559523341799642595631718893361441822553266125702667275609857151548249783637036167985467219722392955081963313026203671256563002619676038176516831151339132587958284369935827743723813900803597058319321952348407304826025973388498135061870337904757649491
      452105977
      ((12784537450109455543241633780534751244068919613678660781647058068239898229439033130682404214404489904359933891912338532530526041310466656735638175109591939910259156438784606874667677544345811547025064069346562391940336138559203935646104755264625701417007348362257013497367037491118345896133136267314374044746938033570133474998382375883070043447546232024290997373877989695217664434133035144003123102575730850834215331400865889483795418161142793,1)::nil)
      4744304192859504349342750335670742141160990015302543921892976220189379275656349861197158970877818503756091386349154741972305042547110496600975215570161872872610129319132355341286083728262249232875041719847886734372783314930031274882010961318014207498760026964808107243604685691035542782593942535001750227668996359042871879185163263751450424164561529411604861467934027471024193313271911472431617058905781473012281992751477343517750715271985839220433493
      1173470285433053983579440414774807620405022419423445554952316409985224719437431275182974329696874252328051935830450423771290472825947058665005473395966426918672622361878452817336418198424315475696382422877329231430218269016663120541036647955430991876618011317629413219903949148804419481982821157478413154148452007115167652338829887315078340416813494476447733612198401347911674680391210416036949135489155174675172826049731939641711137777047285038836891
      0
      5095016724413113748856410078366738994860169006402706457828202743370360405547904034138863209267812229462815936546407214251909822307051947705753707227013733262612305578317940356764075009233097818882987821928223297248850075050147679859136454103434184463580715478523778540118960790883965341123575071380214009569050490114719345847862958306957175713302825195822012766403845089366910723499236587295702213759302945232523496686328666150353485654603524905879263)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.