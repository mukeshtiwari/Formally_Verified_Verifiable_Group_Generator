From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo50:
  prime  64799856613037805076995607181706349482806427843680286917472318965453180842336946381349489585821865343734912841502943085978517542854850133640130001952939908466635344476994187153979533487873633489013091106359500766102917176342014427269419->
  prime  13077874726514839914774520020603991781151601347004061509221091594920597196463202192547709694815265538561773585950616063643661417520554103617030511625082259337752327750541144915174575398684446395858518243360942030347101499816219450277252273139427.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      13077874726514839914774520020603991781151601347004061509221091594920597196463202192547709694815265538561773585950616063643661417520554103617030511625082259337752327750541144915174575398684446395858518243360942030347101499816219450277252273139427
      201819501
      ((64799856613037805076995607181706349482806427843680286917472318965453180842336946381349489585821865343734912841502943085978517542854850133640130001952939908466635344476994187153979533487873633489013091106359500766102917176342014427269419,1)::nil)
      0
      221184
      48
      576)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.