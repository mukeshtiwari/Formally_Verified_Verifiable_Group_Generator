(* Implementation of SHA 256. *)
(* https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf *)
(* https://www.rfc-editor.org/rfc/rfc4634 *)
Require Import Lia
  Coq.Unicode.Utf8
  Coq.Bool.Bool 
  Coq.Init.Byte
  Coq.NArith.NArith
  Coq.Strings.Byte
  Coq.ZArith.ZArith
  Coq.Lists.List.
  
Import Notations ListNotations.
Local Open Scope N_scope.


Section Wf_proof.

  Let f (a : N) := N.to_nat a.

  Definition zwf (x y : N) := (f x < f y)%nat.

  Lemma zwf_well_founded : well_founded zwf.
  Proof.
    exact (well_founded_ltof _ f).
  Defined.

  Lemma N_acc (x : N) : forall a, a < x -> Acc N.lt a.
  Proof.
    induction (zwf_well_founded x) as [z Hz IHz].
    intros ? Hxa.
    constructor; intros y Hy.
    eapply IHz with (y := a).
    unfold zwf. unfold f.
    abstract nia. abstract nia.
  Defined.
    
  Lemma N_lt_wf : well_founded N.lt.
  Proof.
    red; intros ?.
    constructor; intros y Hy.
    eapply N_acc with (x := a).
    exact Hy.
  Defined. 


  Lemma N_Lt_wf : forall up, Acc (fun x y => x < y) up.
  Proof.
    intros up.
    pose proof (N_lt_wf up).
    exact H.
  Defined.

End Wf_proof.


Section Util.

  Definition np_total (np : N):  (np <? 256 = true) ->  byte.
  Proof.
    intros H.
    pose proof of_N_None_iff np as Hn.
    destruct (of_N np) as [b | ].
    + exact b.
    + exfalso; abstract (apply N.ltb_lt in H;
        intuition nia). 
  Defined.

  Lemma np_true : forall np (H : np <? 256 = true) x, of_N np = Some x -> 
    np_total np H = x.
  Proof.
    unfold np_total; intros * Heq.
    generalize (of_N_None_iff np).
    rewrite Heq; intros; reflexivity.
  Qed.  

  
  Lemma nmod_256 : forall np, np mod 256 < 256.
  Proof. 
    intros; eapply N.mod_lt; intro H;
    inversion H.
  Qed. 

  Lemma nmod_256_dec : forall np, (np mod 256 <? 256) = true.
  Proof. 
    intros; apply N.ltb_lt.
    apply nmod_256.
  Qed. 

  Lemma N_eq_gt : forall up t : N, 256 <= up -> t = up / 256 -> 0 <=  t / 256 < t.
  Proof.
    intros up t Hup Ht.
    split. 
    apply N.le_0_l.
    apply N.div_lt_upper_bound. 
    nia.
    (* I know that 1 <= t *)
    assert (Hot: 1 <= t).
    rewrite Ht.
    apply N.div_le_lower_bound.
    nia.
    simpl. exact Hup. nia.
  Qed.

  (*log_{256} n = N.div (N.log2 n) (N.log2 256) *)
  Definition log256 n := N.div (N.log2 n) 8.

  Lemma ulogt : forall t : N, 1 <= t -> t + 1 <= 2 * 2 ^ N.log2 t.
  Proof.
    intros t Ht.
    assert (Htw : t + 1 = N.succ t).
    nia. rewrite Htw. 
    apply N.lt_pred_le. 
    rewrite N.pred_succ.
    assert (Hs : 2 * 2 ^ N.log2 t = 2 ^ (1 + N.log2 t)).
    rewrite N.pow_add_r. simpl. nia. rewrite Hs; clear Hs.
    assert (Hn : 1 + N.log2 t = N.succ (N.log2 t)).
    nia. assert (Htt : 0 < t). nia.
    pose proof  (N.log2_spec t Htt).
    rewrite Hn. nia.
  Qed.
  
  Lemma log256_unique : forall t a b c, 1 <= t -> 0 <= b -> 0 <= c < 2 ^ b -> a = t * 2 ^ b + c -> 
    N.log2 a = b + N.log2 t.
  Proof.
    intros t a b c Ht Hb (Hc,H) EQ.
    apply N.log2_unique.
    - nia.
    - rewrite EQ. split.
      + rewrite N.pow_add_r.
        assert (Htz : 0 < t). nia.
        pose proof (N.log2_spec t Htz) as Hze.
        nia.  
      + rewrite N.pow_succ_r.
        rewrite N.pow_add_r.
        rewrite N.mul_assoc.
        assert (t + 1 <= 2 * 2 ^ N.log2 t).
        apply ulogt. exact Ht.
        nia. nia.
  Qed.

  Lemma nlog256 : forall up t r, 1 <= t ->  r < 256 -> up = 256 * t + r ->
   log256 up =  1 + log256 t.
  Proof.
    intros ? ? ? Ht Hr Hup; unfold log256.
    assert (Htw : 256 = 2 ^ 8). reflexivity.
    assert (Hte : 0 <= 8). nia.
    assert (Hre : 0 <= r < 2^8). nia.
    assert (Hupn : up = t * 2^8 + r). nia.
    pose proof (log256_unique t up 8 r Ht Hte Hre Hupn).
    rewrite H.
    assert (Hs : (8 + N.log2 t) = (1 * 8 + N.log2 t))
      by nia.
    rewrite Hs. rewrite N.div_add_l.
    reflexivity. nia.
  Qed.
  
  Lemma nlogle256 : forall up : N, up < 256 -> 1%nat = N.to_nat (N.log2 up / 8 + 1).
  Proof.
    intros ? Hup.
    assert (Hun : 256 = 2^8).
    reflexivity. rewrite Hun in Hup.
    clear Hun.
    assert (Hn : N.log2 up < 8).
    destruct up. simpl. nia.
    apply N.log2_lt_pow2. nia.
    exact Hup.
    assert (Htn : N.log2 up / 8 = 0).
    apply N.div_small. exact Hn.
    rewrite Htn. nia.
  Qed.


  Lemma N_dec : forall n m : N, {n < m} + {m <= n}.
  Proof.
    intros [| n] [| m].
    + right; nia.
    + left; nia.
    + right; nia.
    + destruct (n <? m)%positive eqn:Ht.
      ++ 
      apply Pos.ltb_lt in Ht.
      left. abstract nia.
      ++ 
      apply Pos.ltb_ge in Ht.
      right. abstract nia.
  Defined.
      

        


  Lemma nlog_le256 : forall up : N, up < 256 <-> 0%nat = N.to_nat (N.log2 up / 8).
  Proof.
    intros ?; split; intro Hup.
    assert (Hun : 256 = 2^8).
    reflexivity. rewrite Hun in Hup.
    clear Hun.
    assert (Hn : N.log2 up < 8).
    destruct up. simpl. nia.
    apply N.log2_lt_pow2. nia.
    exact Hup.
    assert (Htn : N.log2 up / 8 = 0).
    apply N.div_small. exact Hn.
    rewrite Htn. nia.
    assert(Hp : {up < 256} + {256 <= up}).
    apply N_dec. destruct Hp.
    exact l. remember (N.div up 256) as t.
    remember (N.modulo up 256) as r.
    assert (Hp: up = 256 * t + r).
    subst t; subst r. apply N.div_mod'.
    assert (Ht: 1 <= t). subst t.
    apply N.div_le_lower_bound.
    nia. simpl. exact l.
    assert (Hr : 0 <= r < 256).
    rewrite Heqr. 
    eapply N.mod_bound_pos.
    nia. nia. 
    assert (H256 : 256 = 2^8). 
    reflexivity. rewrite H256 in Hr.
    assert (H8 : 0 <= 8). nia.
    pose proof (log256_unique t up 8 r Ht H8 Hr).
    rewrite N.mul_comm, H256 in Hp.
    specialize(H Hp). rewrite H in Hup.
    assert (H18: 8 = 1 * 8).
    reflexivity.
    rewrite H18 in Hup at 1.
    rewrite N.div_add_l in Hup.
    rewrite N2Nat.inj_add in Hup.
    simpl in Hup. inversion Hup.
    nia.
  Qed.

End Util. 

Section Fuel.

  (* passing this extra parameter n to faciliate the computation *)
  Fixpoint byte_list_from_N_fuel (n : nat) (up : N) : list byte :=
  match n with 
  | 0%nat => [np_total (N.modulo up 256) (nmod_256_dec up)]
  | S n' => 
    let r := N.modulo up 256 in
    let t := N.div up 256 in
    List.cons (np_total r (nmod_256_dec up)) (byte_list_from_N_fuel n' t)
  end.


  Lemma byte_list_Sn : forall n np, byte_list_from_N_fuel (S n) np = 
    List.cons (np_total (N.modulo np 256) (nmod_256_dec np)) (byte_list_from_N_fuel n (N.div np 256)).
  Proof.
    reflexivity.
  Qed.

  Lemma fuel_byte_list_length_correctness : forall (n : nat) (np : N), 
    List.length (byte_list_from_N_fuel n np) = (1 + n)%nat. 
  Proof.
    induction n; simpl; intro np.
    + reflexivity.
    + f_equal. apply IHn.
  Qed. 

  (*
    Log256 np fuel is enough to compute the np. Also, the list 
    is in little endien style, i.e., least significate digit first 
  *)
  Definition byte_list_from_N (np : N) := 
    byte_list_from_N_fuel (N.to_nat (log256 np)) np.

  (* Turn the list into big endien *)
  Definition big_endien_list_N (np : N) := 
      List.rev (byte_list_from_N np).
  

  Lemma byte_list_length_correctness : forall np, List.length (byte_list_from_N np) = 
    (1 + N.to_nat (log256 np))%nat.
  Proof.
    intros ?. unfold byte_list_from_N.
    rewrite fuel_byte_list_length_correctness;
    reflexivity.
  Qed.

  Lemma big_endien_list_correctness : forall np, List.length (big_endien_list_N np) = 
    (1 + N.to_nat (log256 np))%nat.
  Proof.
    intros np. unfold big_endien_list_N.
    rewrite rev_length, byte_list_length_correctness;
    reflexivity.
  Qed.
   
  
  Fixpoint horner_eval_byte_list (l : list byte) := 
    match l with
    | List.nil => 0 
    | List.cons h tl => 
          to_N h + 256 * horner_eval_byte_list tl
  end.
  
  Lemma eval_byte_list_cons : forall h tl, horner_eval_byte_list (List.cons h tl) = 
    to_N h + 256 * horner_eval_byte_list tl.
  Proof. 
    reflexivity. 
  Qed.

  Lemma np_mod_total : forall np, to_N (np_total (np mod 256) (nmod_256_dec np)) = np mod 256.
  Proof.
    intros ?; unfold np_total.
    generalize (of_N_None_iff (np mod 256)).
    generalize (np_total_subproof (np mod 256) (nmod_256_dec np)).
    intros; destruct (of_N (np mod 256)) eqn:Htn.
    ++ apply to_of_N; exact Htn.
    ++ apply of_N_None_iff in Htn.
       assert (Hn : np mod 256 < 256). 
       apply nmod_256. nia.
  Qed.


  Lemma byte_list_from_N_correct : forall np, horner_eval_byte_list (byte_list_from_N np) = np.
  Proof.
    intro np. unfold byte_list_from_N.
    remember (N.to_nat (log256 np)) as n.
    unfold log256 in Heqn. generalize dependent np.
    induction n.
    + simpl. intros ? Hn. 
      apply nlog_le256 in Hn.
      unfold np_total.
      generalize (of_N_None_iff (np mod 256)).
      generalize (np_total_subproof (np mod 256) (nmod_256_dec np)).
      intros; destruct (of_N (np mod 256)) eqn:Htn.
      ++ 
        rewrite N.add_0_r.
        assert (Hnp : np mod 256 = np). 
        apply N.mod_small; exact Hn.
        rewrite Hnp in Htn.
        apply to_of_N; exact Htn.
      ++
        assert (Hnp : np mod 256 = np). 
        apply N.mod_small; exact Hn.
        rewrite Hnp in Htn.
        apply of_N_None_iff in Htn.
        nia.
    + intros ? Hn. rewrite byte_list_Sn, 
      eval_byte_list_cons.
      destruct ( N_dec np 256) as [Hnl |  Hnr].
      ++ (* impossible case *)
        apply nlog_le256 in Hnl.
        rewrite <-Hnl in Hn. nia.
      ++ 
        specialize (IHn (N.div np 256)).
        assert (Hnp : np = 256 * (N.div np 256) + (N.modulo np 256)).
        apply N.div_mod. nia.
        assert (Hnt : 1 <= N.div np 256).
        apply N.div_le_lower_bound; nia.
        assert (Hnw : np mod 256 < 256).
        apply nmod_256.
        pose proof (nlog256 np _ _ Hnt Hnw Hnp).
        unfold log256 in H; rewrite H,  N2Nat.inj_add  in Hn;
        simpl in Hn. apply eq_add_S in Hn.
        specialize (IHn Hn). rewrite IHn.
        rewrite np_mod_total. nia.
  Qed.




End Fuel.

Section Wellfounded.

  (* uses well founded induction to compute the byte list, but it's very slow because of proof embedding *)
  Definition byte_list_sig (np : N) :  {l : list byte | List.length l = N.to_nat (log256 np + 1) ∧ 
    np = horner_eval_byte_list l}.
  Proof.
  induction (N_Lt_wf np) as [up Hacc IHuz].
  destruct (up <? 256) eqn:Hnp.
  + exists (List.cons (np_total up Hnp) List.nil).
    pose proof (proj1 (N.ltb_lt up 256) Hnp) as Ht.
    split.
    ++ abstract (simpl; apply nlogle256; exact Ht).
    ++ simpl. pose proof (np_true up Hnp).
      rewrite N.add_comm; simpl.
      destruct (of_N up) as [b | ] eqn:Hb.
      specialize(H b eq_refl); rewrite H.
      apply to_of_N_iff in Hb; intuition.
      apply of_N_None_iff in Hb; intuition.
      abstract nia.
  + pose proof (proj1 (N.ltb_ge up 256) Hnp) as Ht.
    refine(
      let r := N.modulo up 256 in 
      let t := N.div up 256 in _ ).
    assert (Htt: t < up). 
    abstract (unfold t; 
      apply N.div_lt; nia).
    destruct (IHuz t Htt) as [lr Hlr].
    assert (Hr : r <? 256 = true).
    abstract (apply N.ltb_lt; unfold r;
    apply (nmod_256 up)).
    exists (List.cons (np_total r Hr) lr).
    split.
    ++
      simpl. assert (Hup: up = 256 * t + r).
      abstract (unfold t, r; rewrite <-N.div_mod with (b := 256);
      [reflexivity | nia]).
      rewrite nlog256 with (t := t) (r := r).
      abstract nia. 
      assert (Hot: 1 <= t).
      abstract (unfold t;
      apply N.div_le_lower_bound; nia).
      exact Hot.
      apply N.ltb_lt in Hr. exact Hr.
      exact Hup.
    ++ 
      destruct Hlr as [Hlr1 Hlr2].
      rewrite eval_byte_list_cons, <-Hlr2.
      assert (Htn : to_N (np_total r Hr) = r).
      unfold np_total.
      generalize (of_N_None_iff r).
      destruct (of_N r) eqn:Hnr.
      intros. apply to_of_N_iff; exact Hnr.
      apply of_N_None_iff in Hnr.
      pose proof (proj1 (N.ltb_lt r 256) Hr).
      abstract nia. rewrite Htn; unfold r, t.
      rewrite N.add_comm.
      apply N.div_mod. abstract nia. 
  Defined.

End Wellfounded.

Section Sha256.

  Definition word := 32.

  Definition add (x y : N) := (x + y) mod (2 ^ word).


  (* shiftr is fine but shift-left needs to be truncated *)
  Definition shift_left (x n : N) := (N.shiftl x n) mod (2 ^ word).

  (* right shift *)
  Definition shift_right (x n : N) := N.shiftr x n.

  (* bitwise and *)
  Definition bitwise_and (x y : N) := N.land x y.

  (* bitwise or *)
  Definition bitwise_or (x y : N) := N.lor x y.

  (* bitwise xor *)
  Definition bitwise_xor (x y : N) := N.lxor x y.

  (* flipping/negating the bits *)
  Definition bitwise_neg (x : N) := N.lnot x word.

  (* The rotate left (circular left shift) operation, where x is a w-bit word and n 
  is  an  integer  with  0 ≤ n  < w,  is  defined  by  ROTL n(x)=(x  <<  n) \/ (x >> w - n).*)
  Definition ROTL (n x : N) :=  bitwise_or (shift_left x n) 
    (shift_right x (word - n)). 
    
  (* 
  The  rotate  right  (circular  right  shift)  operation,  where  x  is  a  w-bit  word 
  and n is  an integer with  0 ≤ n  < w, is defined by  ROTR  n(x)=(x >> n) \/ (x << w - n). 
  *)
  Definition ROTR (n x : N) :=  bitwise_or (shift_right x n) 
    (shift_left x (word - n)).

  (*
  The right shift operation, where x is a w-bit word and n is an integer with 
  0 ≤ n < w, is defined by SHR n(x)=x >> n. 
  *) 
  Definition SHR (n x : N) := shift_right x n.


  Lemma rotl_rotr : forall (x ml : N), 0 <= ml < word -> ROTL ml x = ROTR (word - ml) x.
  Proof.
    intros ? ? Hm.
    unfold ROTL, ROTR, 
    bitwise_or, shift_left,
    shift_right.
    assert(H32: word - (word - ml) = ml) by nia.
    rewrite H32, N.lor_comm.
    reflexivity.
  Qed.

  Lemma rotr_rotl : forall (x ml : N), 0 <= ml < word -> ROTR ml x = ROTL (word - ml) x. 
  Proof.
    intros ? ? Hm.
    unfold ROTL, ROTR, 
    bitwise_or, shift_left,
    shift_right.
    assert(H32: word - (word - ml) = ml) by nia.
    rewrite H32, N.lor_comm.
    reflexivity.
  Qed. 

  (* Equation 4.2 *)
  Definition Ch (x y z : N) := bitwise_xor (bitwise_and x y) 
    (bitwise_and (bitwise_neg x) z).

  (* Equation 4.3*)
  Definition Maj (x y z : N) := bitwise_xor (bitwise_xor (bitwise_and x y) 
    (bitwise_and x z)) (bitwise_and y z).

  (* Equation 4.4 *)
  Definition Sigma₀ (x : N) := bitwise_xor (bitwise_xor (ROTR 2 x)
    (ROTR 13 x)) (ROTR 22 x).

  (* Equation 4.5 *)
  Definition Sigma₁ (x : N) :=  bitwise_xor (bitwise_xor (ROTR 6 x)
    (ROTR 11 x)) (ROTR 25 x).

  Definition sigma₀ x := bitwise_xor (bitwise_xor (ROTR 7 x)
    (ROTR 18 x)) (SHR 3 x).

  Definition sigma₁ x := bitwise_xor (bitwise_xor (ROTR 17 x)
     (ROTR 19 x)) (SHR 10 x).


  (* 5.3.3 *)
  (* superscript is not working *)
  Definition H₀ : list N := [ 
    0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a; 0x510e527f; 
    0x9b05688c; 0x1f83d9ab; 0x5be0cd19].

  (* 4.2.2 SHA-224 and SHA-256 Constants  *)
  Definition K : list N := [ 
    0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5; 0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5;
    0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3; 0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174;
    0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc; 0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da;
    0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7; 0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967;
    0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13; 0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85;
    0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3; 0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070;
    0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5; 0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3;
    0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208; 0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2].

  (* message m is in big endien style *)
  Context (m : list byte).

  (* Length of message bytes *)
  Let n := N.of_nat (List.length m).
  (* Length of message, in bits *)
  Let mbits := 8 * n.
  (* Hypothesis that message length, in bits, is less than 2^64*)
  Context {Hn : mbits < 2^64}.
  (* Length of to be padded *)
  Let k := Z.to_N (Zmod (448 - (Z.of_N mbits + 1)) 512).


  (* 
    Suppose  that  the  length  of  the  message,  M,  is l bits.  Append the bit “1” to the end of 
    the message, followed by k  zero bits, where  k is the smallest, non-negative solution to the 
    equation l + k + 1 = 448 mod 512. Then  append  the  64-bit  block  that  is  equal  to  the 
    number l expressed using a  binary  representation.  For  example,  the  (8-bit  ASCII)  message
    “abc”  has  length 8 * 3 = 24 bits, so the message is padded with a one bit, then 
    (448 - (21 + 1) mod 512) = 423 zero bits, and then the message length, to become the 
    512-bit padded message 
  *)

  (* return v byte of zeros *)
  Fixpoint get_zero_bytes (v : nat) : list byte :=
  match v with 
  | 0%nat => []
  | S v' => List.cons x00 (get_zero_bytes v')
  end.

  Lemma eval_zero_byte : forall v : nat, horner_eval_byte_list (get_zero_bytes v) = 0%N.
  Proof.
    induction v.
    + simpl; reflexivity.
    + simpl; rewrite IHv;
      reflexivity.
  Qed.

  Lemma get_zero_bytes_len : forall v, List.length (get_zero_bytes v) = v%nat.
  Proof.
    induction v.
    + simpl; reflexivity.
    + simpl; rewrite IHv;
      reflexivity.
  Qed.

  (* x80 followed by v zero bytes *)
  Definition message_padding (v : nat) : list byte :=
  match v with 
  | 0%nat => []
  | S v' => List.cons x80 (get_zero_bytes v')
  end.
  
  Lemma message_padding_app : forall v, message_padding (S v) = List.cons x80 (get_zero_bytes v).
  Proof.
    simpl; destruct v.
    + reflexivity.
    + simpl; reflexivity.
  Qed.

  Lemma message_padding_length : forall v, List.length (message_padding v) = v.
  Proof.
    unfold message_padding.
    induction v.
    + simpl; reflexivity.
    + simpl; rewrite get_zero_bytes_len;
      reflexivity.
  Qed.
    
  (* if v is non-zero then padding evaluates to x80*)
  Lemma message_padding_correct : forall v, (0 < v)%nat -> horner_eval_byte_list (message_padding v) = to_N x80.
  Proof.
    destruct v.
    + intro H; nia.
    + intros H. rewrite message_padding_app, eval_byte_list_cons, 
      eval_zero_byte; nia.
  Qed.

  (* 8 bytes, or 64 bits, are needed to represent the message length *)
  Lemma upper_bound_on_msg_len : (N.to_nat (log256 mbits + 1) <= 8)%nat.
  Proof.
    unfold log256; unfold mbits.
    assert (Hnt : N.log2 (8 * n) < 64).
    destruct n. simpl. nia.
    apply N.log2_lt_pow2. nia.
    exact Hn. 
    assert (Hnw: N.log2 (8 * n) / 8 < 8). 
    apply N.div_lt_upper_bound with (q := 8).
    nia. exact Hnt.
    nia.
  Qed.

  (* lb is length byte *)
  Definition append_zero_in_length_byte (lb : list byte) : list byte := 
    let nl := List.length lb in 
    if (nl <=? 8)%nat then get_zero_bytes (8 - nl) ++ lb
    else lb. (* impossible case *)

  (* if the length byte is less the 8, then append it with zero, 
    in big endian style, to turn it into 8 bytes*)
  Definition message_length_byte : list byte := 
    append_zero_in_length_byte (big_endien_list_N mbits).

  (* proof that if the message length bytes is equal to 8 bytes *)
  Lemma message_length_byte_8 : (List.length message_length_byte = 8)%nat.
  Proof.
    unfold message_length_byte,
    append_zero_in_length_byte.
    assert (Ht: (List.length (big_endien_list_N mbits) <= 8)%nat).
    rewrite big_endien_list_correctness.
    unfold log256. 
    assert (Hnt : N.log2 mbits < 64).
    destruct mbits. simpl. nia.
    apply N.log2_lt_pow2. nia.
    exact Hn.
    assert (Hwt: N.log2 mbits / 8 < 8).
    apply N.div_lt_upper_bound; nia.
    nia.
    apply Nat.leb_le in Ht.
    rewrite Ht.
    apply Nat.leb_le in Ht.
    rewrite app_length.
    rewrite get_zero_bytes_len.
    nia.
  Qed.


  Lemma push_N : forall a : Z, (0 <= a)%Z -> (1 + Z.to_N a) = Z.to_N (1 + a).
  Proof.
    intros. rewrite Z2N.inj_add.
    all: nia.
  Qed.

  Lemma mod_eq_custom : forall (a b : Z), (0 < b)%Z -> Z.modulo a b = (a - b * (a / b))%Z.
  Proof.
    intros a b Hb; rewrite Zmod_eq; nia.
  Qed. 

  (* carrying this extra information of w to simplify other proofs *)
  Lemma k_plus_gen : exists w : N, k =  8 * w + 7 /\ 
    (w = (Z.to_N (55 - Z.of_N n - 64 * ((447 - Z.of_N (8 * n)) / 512)))) /\ 
    (0 <= (55 - Z.of_N n - 64 * ((447 - Z.of_N (8 * n)) / 512)))%Z.
  Proof.
    unfold k, mbits.
    assert (H: (448 - (Z.of_N (8 * n) + 1))%Z = (447 - (Z.of_N (8 * n)))%Z).
    nia. rewrite H.
    assert (Hp : (0 <= (447 - Z.of_N (8 * n)) mod 512 < 512)%Z).
    apply Z.mod_pos_bound; nia.
    rewrite mod_eq_custom.
    assert (Ht: (447 - Z.of_N (8 * n) - 512 * ((447 - Z.of_N (8 * n)) / 512))%Z =
        (8 * (55 - Z.of_N n - 64 * ((447 - Z.of_N (8 * n)) / 512)) + 7)%Z).  
    nia. rewrite Ht.
    exists (Z.to_N (55 - Z.of_N n - 64 * ((447 - Z.of_N (8 * n)) / 512))).
    rewrite mod_eq_custom in Hp.
    all:nia.
  Qed.

  Lemma k_plus_gen_one : exists w : N, 1 + k = 8 * (w + 1) /\ 
    (w = (Z.to_N (55 - Z.of_N n - 64 * ((447 - Z.of_N (8 * n)) / 512)))) /\ 
    (0 <= (55 - Z.of_N n - 64 * ((447 - Z.of_N (8 * n)) / 512)))%Z.
  Proof.
    destruct k_plus_gen as [x [Hx H]].
    exists x. rewrite Hx. nia.
  Qed.

  (* k + 1 is divisible by 8*)
  Lemma k_plus_one_div_8 : N.modulo (1 + k) 8 = 0.
  Proof.
    destruct k_plus_gen as [x [H1 H2]].
    assert (Ht : 1 + (8 * x + 7) =  (x + 1) * 8).
    nia. rewrite H1, Ht.
    rewrite N.mod_mul.
    reflexivity. nia.
  Qed.
    
  (* compute the  wt *)
  Let wt := N.div (1 + k) 8.

  (* 0 < wt *)
  Lemma wt_exact_val : wt = Z.to_N (56 - Z.of_N n - 64 * ((447 - Z.of_N (8 * n)) / 512)) /\ 
    (0 < wt).
  Proof.
    destruct k_plus_gen_one as [x [Hx [Hy Hz]]].
    assert (wt = x + 1). unfold wt.
    rewrite Hx. rewrite N.mul_comm, N.div_mul.
    reflexivity. nia.
    rewrite H, Hy.
    nia.
  Qed.


  Lemma sha_64_byte : n + wt + 8 = 64 * Z.to_N (1 -  ((447 - Z.of_N (8 * n)) / 512)) ∧ 
    (0 < (64 - 64 * ((447 - Z.of_N (8 * n)) / 512)))%Z.
  Proof.
    destruct wt_exact_val as [H1 H2].
    nia.
  Qed.


  (* message + padding + message_length should be divisible by 64 (byte)*)
  Lemma div_64 : N.modulo (n +  wt + 8) 64 = 0.
  Proof.
    destruct sha_64_byte as [H1 H2].
    rewrite H1, N.mul_comm, N.mod_mul.
    reflexivity. nia.
  Qed. 
    
  (* Number of 64 byte, 512 bits, blocks in the message *)
  Let ms := N.div (n + wt + 8) 64.

  Definition prepared_message : list byte := 
    m ++ message_padding (N.to_nat wt) ++ message_length_byte.

  Lemma prepared_message_correctness : List.length prepared_message = N.to_nat (n + wt + 8).
  Proof.
    unfold prepared_message.
    repeat rewrite app_length.
    rewrite message_padding_length, 
    message_length_byte_8.
    nia.
  Qed.


  (* turns 4 bytes --32 bit--, 'a' most significant and 'd' least significant, to N *)
  Definition big_endien_32_bit_to_N (a b c d : byte) : N :=
    ((to_N a * 256 + to_N b) * 256 + to_N c) * 256 + to_N d.


  
  (* Section 5.2.1:
     For SHA-1, SHA-224 and SHA-256, the message and its padding are parsed into
     N 512-bit blocks, M(1), M(2),...M(N). Since the 512 bits of the input block
     may be expressed as sixteen 32- bit words, the first 32 bits of message
     block i are denoted M0(i), M1(i), and so on up to M15(i).
     (i < N.to_nat ms)%nat  
     (j < 16)%nat
   *)  
  Definition M (i j : nat) : N := big_endien_32_bit_to_N
    (nth (64 * i + 4 * j) prepared_message x00)
    (nth (64 * i + 4 * j + 1) prepared_message x00)
    (nth (64 * i + 4 * j + 2) prepared_message x00)
    (nth (64 * i + 4 * j + 3) prepared_message x00).

  (* [n-1; n-2; .... 0] *)
  Fixpoint from_n (n : nat) := 
    match n with 
    | 0%nat => [] 
    | S n' => n' :: (from_n n')
    end.
  
  (* [0, 1, 2, .... n-1]*)
  Definition upto_n (n : nat) := List.rev (from_n n).
  
  
  (* From section 6.2.2 (step 1):
     Prepare the message schedule, {W(t)}:
     W(t) = Mt(i) for 0 <= t <= 15
     W(t) = σ{1,256}(W_(t-2)) + W(t-7) + σ{0,256}(W(t-15)) + W(t-16) for 16 <= t <= 63
  *)

  Definition W (i : nat) : list N := 
    List.fold_left 
    (fun (acc : list N) (t : nat) => 
      let wtp := 
        if (t <? 16)%nat then M i t (* copy the M i into 16 (32 bit) N into acc *)
        else 
          let a := nth (t - 2) acc 0 in 
          let b := nth (t - 7) acc 0 in
          let c := nth (t - 15) acc 0 in 
          let d := nth (t - 16) acc 0 in
          add (add (add (sigma₁ a) b) (sigma₀ c)) d
      in acc ++ [wtp]) (upto_n 64) [].
  

  (* Steps 2, 3, and 4 in section 6.2.2. *)
  Definition sha256_intermediate (W : list N) (H : list N) : list N :=
    (* step 2 *)
    let a := nth 0 H 0 in
    let b := nth 1 H 0 in
    let c := nth 2 H 0 in
    let d := nth 3 H 0 in
    let e := nth 4 H 0 in
    let f := nth 5 H 0 in
    let g := nth 6 H 0 in
    let h := nth 7 H 0 in
    (* Step 3 *)
    let '(a, b, c, d, e, f, g, h) := 
    List.fold_left 
    (fun '(a, b, c, d, e, f, g, h) t => 
      let T₁ := add (add (add (add h (Sigma₁ e)) (Ch e f g)) (nth t K 0)) (nth t W 0) in
      let T₂ := add (Sigma₀ a) (Maj a b c) in
      let h := g in
      let g := f in
      let f := e in
      let e := add d T₁ in
      let d := c in
      let c := b in
      let b := a in
      let a := add T₁ T₂ in
      (a, b, c, d, e, f, g, h)) (upto_n 64) (a, b, c, d, e, f, g, h) 
    in 
    (* step 4: compute Hi *)
    [add a (nth 0 H 0); add b (nth 1 H 0); add c (nth 2 H 0);
    add d (nth 3 H 0); add e (nth 4 H 0); add f (nth 5 H 0);
    add g (nth 6 H 0); add h (nth 7 H 0)].


  Definition sha256 := 
    List.fold_left 
    (fun H i => sha256_intermediate (W i) H) 
    (upto_n (N.to_nat ms)) H₀.

End Sha256.

From Coq Require Import String Ascii.


Definition concat_bytes (bs : list byte) : N :=
    List.fold_left (fun acc b => acc * (N.shiftl 1 8) + to_N b) bs 0.

Definition sha256_string (s : string) :=
  concat_bytes (List.flat_map big_endien_list_N (sha256 (list_byte_of_string s))).

(* start of sha256 tests *)
(* https://www.di-mgt.com.au/sha_testvectors.html *)

Lemma sha256_1st : sha256_string "abc" = 
  0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad.
Proof.
 Time vm_compute; reflexivity.
Qed.

Lemma sha256_2nd : sha256_string "" =
  0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855.
Proof.
  Time vm_compute; reflexivity.
Qed.

Lemma sha256_3rd : sha256_string  "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" =
  0x248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1.
Proof.
  Time vm_compute; reflexivity.
Qed.

Lemma sha256_4th : sha256_string ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghij" ++
 "klmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu") =
  0xcf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1.
Proof.
  Time vm_compute; reflexivity.
Qed.


(* end of sha256 *)


