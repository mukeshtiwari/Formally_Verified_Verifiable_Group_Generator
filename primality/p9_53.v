From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma primo53:
  prime  1939803328268014886070585181607272991998696775457665290028825598146725720938318974863633952892209433833164315204861043856262833661109403230208439526644898227421242902954817435527606927384661962787393829207953703912579->
  prime  129807759121039020146071419182795494078568790820076045878148951376782591793750429159924656859640870893247689644985527386845255020569869864212933942827770254962537859657773011594318882050738838356433804312814319917699422563.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      129807759121039020146071419182795494078568790820076045878148951376782591793750429159924656859640870893247689644985527386845255020569869864212933942827770254962537859657773011594318882050738838356433804312814319917699422563
      66918
      ((1939803328268014886070585181607272991998696775457665290028825598146725720938318974863633952892209433833164315204861043856262833661109403230208439526644898227421242902954817435527606927384661962787393829207953703912579,1)::nil)
      129807759121039020146071419182795494078568790820076045878148951376782591793750429159924656859640870893247689644985527386845255020569869864212933942827770254962537859657773011594318882050738838356433804312814319917699168643
      43606528
      552
      8464)
     ((Proof_certif _ H) :: nil)).
native_cast_no_check (refl_equal true).
Time Qed.
