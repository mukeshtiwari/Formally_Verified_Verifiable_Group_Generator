From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo67:
  prime  1919556258681175476406685284758214173762843753374646378802427693980522450507861694454768568272668569966849043087280402244454380753343461228604919938931403522591151730421300847870007958009490905021690289820973281313334333089994854568911044690104814349114926444585266355905163562729840207172229185270843341844779314930134694989601361858168524157644246948255792962762113->
  prime  9426704060946763426029954531798217570102774717642690944783349353347840994473944800439623193362930256801141628877093402741469471032072093518009666575550493861968529639494157717805147208793383230297108378921660750256664532159429198705569009455673795513916080918751707940590864817912593054320726296206614846123252548955723231076026113522547159765292726930478132098949892736001429.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      9426704060946763426029954531798217570102774717642690944783349353347840994473944800439623193362930256801141628877093402741469471032072093518009666575550493861968529639494157717805147208793383230297108378921660750256664532159429198705569009455673795513916080918751707940590864817912593054320726296206614846123252548955723231076026113522547159765292726930478132098949892736001429
      4910876677
      ((1919556258681175476406685284758214173762843753374646378802427693980522450507861694454768568272668569966849043087280402244454380753343461228604919938931403522591151730421300847870007958009490905021690289820973281313334333089994854568911044690104814349114926444585266355905163562729840207172229185270843341844779314930134694989601361858168524157644246948255792962762113,1)::nil)
      0
      16464
      28
      196)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.