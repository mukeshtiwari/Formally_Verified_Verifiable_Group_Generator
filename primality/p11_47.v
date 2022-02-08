From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo47:
  prime  20928605500745914056419630420984304517383848760396129607194562012962770306430678559170407021633270938594442566639297704414629887420149154920915727271177648450703247863585849233559499037259506088123978448775580493814010132629158179090619660648217856786692951723255829750384778038382023431307885110574430549065569615261776838697262038580438692889634252671061739156290971639262392481816988233418780110726101656011751985875305694058218349275672714231941076264241556080286855122445128441837832606246025586627814549830412971->
  prime  22304912455685966856597898156729074351056045422577299882422890800059228007322172842578571328189918102058290298706631200052344778076673003646824987327984832968118394849590981850856838812947765727491187519523960218248207066971116879263976990771765959484699453614482683257364548970340797928447826013547928968805925824647477550443787660623274463658973244829265611229951476297681662926561628934860534905029793897732260985041334824319213866088816140794091273346646176412122771385251497066338575406215930777140200667976368090885443.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      22304912455685966856597898156729074351056045422577299882422890800059228007322172842578571328189918102058290298706631200052344778076673003646824987327984832968118394849590981850856838812947765727491187519523960218248207066971116879263976990771765959484699453614482683257364548970340797928447826013547928968805925824647477550443787660623274463658973244829265611229951476297681662926561628934860534905029793897732260985041334824319213866088816140794091273346646176412122771385251497066338575406215930777140200667976368090885443
      1065762
      ((20928605500745914056419630420984304517383848760396129607194562012962770306430678559170407021633270938594442566639297704414629887420149154920915727271177648450703247863585849233559499037259506088123978448775580493814010132629158179090619660648217856786692951723255829750384778038382023431307885110574430549065569615261776838697262038580438692889634252671061739156290971639262392481816988233418780110726101656011751985875305694058218349275672714231941076264241556080286855122445128441837832606246025586627814549830412971,1)::nil)
      22304912455685966856597898156729074351056045422577299882422890800059228007322172842578571328189918102058290298706631200052344778076673003646824987327984832968118394849590981850856838812947765727491187519523960218248207066971116879263976990771765959484699453614482683257364548970340797928447826013547928968805925824647477550443787660623274463658973244829265611229951476297681662926561628934860534905029793897732260985041334824319213866088816140794091273346646176412122771385251497066338575406215930777140200667976368090791363
      9834496
      0
      3136)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
