From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo47:
  prime  297791305036854831399496256530051626565864099025042115228594205921686113497546909656665794373443926148156152400469656218178336878683055318871209358875028768997939755769958462954952440096751513775081914348569524227306056531311400954486077192001174203403105242366477974847475333638326808320744681930467408810720872766850574901613116226788950212451916195164682905061250919558679947565124687570100374573841570286093785455759532040684351006310582844379744518317423679630965273786774186346879231164003013413014415113294802933359610539130228522081->
  prime  16433443427414962863527303203744676882610067762160504854884290955090872812277432607664597562995710201448092821213049710696127158998103558430375931880183903850752976596504368901845166083848377139315043646634630509855075165228196814174770112776585357745504423030005938149512259395919823283207668400650687822812961417913224296824347691226578328474154964435180950917921226558192789532719348649161683756226844730746800776624010479202283606032871605691852497500358507643151644524343429626335589477783501485315940438551346911141351285023208557333388157681.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      16433443427414962863527303203744676882610067762160504854884290955090872812277432607664597562995710201448092821213049710696127158998103558430375931880183903850752976596504368901845166083848377139315043646634630509855075165228196814174770112776585357745504423030005938149512259395919823283207668400650687822812961417913224296824347691226578328474154964435180950917921226558192789532719348649161683756226844730746800776624010479202283606032871605691852497500358507643151644524343429626335589477783501485315940438551346911141351285023208557333388157681
      55184430
      ((297791305036854831399496256530051626565864099025042115228594205921686113497546909656665794373443926148156152400469656218178336878683055318871209358875028768997939755769958462954952440096751513775081914348569524227306056531311400954486077192001174203403105242366477974847475333638326808320744681930467408810720872766850574901613116226788950212451916195164682905061250919558679947565124687570100374573841570286093785455759532040684351006310582844379744518317423679630965273786774186346879231164003013413014415113294802933359610539130228522081,1)::nil)
      5346591300311675126917322586244087138825214365461052757014875278115692736307662936658673244217035522909121730551975798266520166280023804736934559626446563571744445632977526612343290648732427601406210610956388824512560052665470578876332198657344677514518966486903592669658519035445893033057429207259779670921864430213129281652673395900498970699610243417594154588087893507687085686363045190500899666530466224433912818228866167620131109409513470295147286759287216848194057605485388341344757269908131848393916994761793852170170594582313205917303575079
      4816522451221739565669169702053903768355337471867684911530105174327924870299059315154768005819557644511464165243482282849297157099203109018789747566848953805446287074682070867616561650786845654708836604059491450543638963928558659649208571411639771753662612330663233158767775254331233717440158682428428928605166083260651219759501601092770603382929038388402937094156020374048737108116827526698084112352271937609369049324880572646019725834512643688447143673476424819601604640960686099307447666525160022597798748080816432182985769854909937539750122940
      9301032758812301952267631365524916251293223244765793097424400548087299237958727134888981398716963117151148328873412853974093399390292311962914969452160550721974970462011784699432804477422933066074657836605386968236277366636393622993650367244823260462031360370666257309992446630085201520966513715356468384123474458002051786552000406875018992929130863198137115231963850582199950966220593438666949526769266609883235815442067726477472382165072022108217134456468281553702824608183563314595572780907532442963827477552534450794978621043003061534214321885
      873094495988676693016367932650622189579516715291584534813044152852816541301440071371220471291381938691358024517373153125700159082646492804306870203136676970894642519726048525289782851342165591414061470998923794814876863692322357510284108607541536634149462202328015302554900518399796933286780534006115386801249844672836943106559893769957749587797252111173443492481148072885085119056752678087568683156612870605134238944325525349750325932761113306126190017722643112514843126382856519376126430524697514951028895264812757863896086097430365098354785987)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
