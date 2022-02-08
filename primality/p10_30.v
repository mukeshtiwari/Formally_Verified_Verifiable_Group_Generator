From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo30:
  prime  1853038651837735811800681791082722691929887450801207776652300330069355924821099798409550998610402412599292764427750915933590243647430382622154900463583601043121038768571157046634784019286266786772895026350269276930144323479722768390030515189202855378084767954672572420959001313730250234283764966754613374705313533471443234144554051286657415756696146035417796398575509427403678636082683112405651227180446846349126421333448601475189785435579057338922103814287211291682753221137365137216009565975007176098893021795663732573411161814750068654497219840540835903458207268235012670584962706581475056616855238004715240923830991000834869893170765150723605117024561431->
  prime  56093088428678058177891280807868675688014288278059854847615265187885904045277435612482128218203674858674728165347543513104807031539203651544744867486277994140979272586300043565951391256324036115186451320505523046407844037003988598529186241264354660373094103566523422975290362179754992448972923851653289856739084870327639910282888604980244939823936925726612754044459743147637375663344057287636328022507747230326653688059472491560269849182066414873329813307564705957161251416596762992965238114570542636861487550364286535121365590202227375202377503994784851115637605398688839875749925933310647719783153605146044022945153816521609981474992393130602083212312158578392391.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      56093088428678058177891280807868675688014288278059854847615265187885904045277435612482128218203674858674728165347543513104807031539203651544744867486277994140979272586300043565951391256324036115186451320505523046407844037003988598529186241264354660373094103566523422975290362179754992448972923851653289856739084870327639910282888604980244939823936925726612754044459743147637375663344057287636328022507747230326653688059472491560269849182066414873329813307564705957161251416596762992965238114570542636861487550364286535121365590202227375202377503994784851115637605398688839875749925933310647719783153605146044022945153816521609981474992393130602083212312158578392391
      30270868
      ((1853038651837735811800681791082722691929887450801207776652300330069355924821099798409550998610402412599292764427750915933590243647430382622154900463583601043121038768571157046634784019286266786772895026350269276930144323479722768390030515189202855378084767954672572420959001313730250234283764966754613374705313533471443234144554051286657415756696146035417796398575509427403678636082683112405651227180446846349126421333448601475189785435579057338922103814287211291682753221137365137216009565975007176098893021795663732573411161814750068654497219840540835903458207268235012670584962706581475056616855238004715240923830991000834869893170765150723605117024561431,1)::nil)
      42541565628446496056493321487580470751186595719378956048509832367182645213900199293685746137240400275286272438621139591537653739547290027067480787214157228563260386986310848561886484317965771134604630993155015144572483035841726447539604467574003586905527660712187147587853892139920325903315280413444050735407856382621942204337542817206847333783840321782394281324405554869617009871127685125239597229500442487647875108864885316759126811204641328155457312213441834150977348182741612337324370340707494782121038290482297160939855951254215512932224773940962424307785571185383712359898988185774429470805767190293144882331901419052822376162267068526475173738212725186286837
      27541489230979114530985533794893987142790912185507995812928621101770900541354210058480130925096785580101023947875033388483676270191645074481577088210908736310158170540320191943232461039782967954348798290464604292897993541477719622819056396780191980582918225074688471002470202495208275202433465670979085384916782743191238146523165186962094345826699745790387878831551407321079276611962729999461605061645487606337488469649402295464340930468811467549663866938472659181764706012683215994956339740911645730940220921233064886747684126902648280323490775680755218454508836895429946530074542435085174071825063599863326191033535339264280212810737650234519765706352896105151331
      4691533384871597082570490492081018377115403192506722384903846927679475111270424001487498279202989022644659602610541857499890285804949222997359279485199595622039179661329979722408350163757391067735152251559664461273571434794578876341005539871375663827792658812069774257084950668921639715958873968249718066702678422176569395774600765589828420117002786048873110237782796872891117673466514512711423751992608204373097378316756380135635520543601900997455016522310458807602338266761695585742278046448263685331145320869007015403994979557126708238754059658527080400556865593854102062387468071068354841424947898269734307582560086507556357416753652826479090692257981955725779
      5281898460974668000266261685335151979463818481945618622217337375059082579689261021476460927971969157520456081800526091106029015190364303558373818805145906052171894998011515855895031220386434862637729753258261229637557151214678158580955434213045127317184286110665776270614752042146733098786223732989849981810363427389666436617807930750636347473350721912548284127564892698618183883424639882074263488915109452457923744688547853628987976694682660015071202267384609541031541157788297170537406008322185109797595744337829896691708186617322696046541208620259270189881835565547794142851847011883792402746261738516142430639154977685605086035725868052064329302846307005689372)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
