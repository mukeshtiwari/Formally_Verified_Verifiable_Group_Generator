From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo24:
  prime  76347075409217483924261000643133342976202673670431657463348287657262220842530254952930705657132995833839862909161821028751180160984389->
  prime  1372867842060345559919670539555779397197411119957218804721563937621040971957611365121001923904541279146695701725184827722708613685726100669021.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1372867842060345559919670539555779397197411119957218804721563937621040971957611365121001923904541279146695701725184827722708613685726100669021
      17981931
      ((76347075409217483924261000643133342976202673670431657463348287657262220842530254952930705657132995833839862909161821028751180160984389,1)::nil)
      1292753681962483003088448077590321202210395791196337227648048514583715120752317513248688265151476362583690769391154801428918543118579172627331
      950236940390808350041117067517392016080618912730290664060071815447387573643246853879406909934645802337975538629053038094617805113343864702201
      0
      763290016499184757087952625329178700641701874009370871902343343016027267808856863678291502311256802358123984473928471747345346772814297718807)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.