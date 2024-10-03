Require Import Coq.NArith.NArith
  Verigen.Functions
  Znumtheory Lia
  Zdiv Zpow_facts List
  Coq.Init.Peano
  Coq.Arith.PeanoNat.
Import ListNotations.

Section Fermat_Little_Theorem.


  (* pascal triangle https://en.wikipedia.org/wiki/Binomial_coefficient *)
  (* nC0 = 1
     0C(S _) = 0 
     (n+1)C(k+1) = nC(k+1) + nCk
  *)
  Fixpoint binomial_exp (n k : nat) : nat :=
   match n with 
   | O => match k with
    | O => S O 
    | S _ => O 
    end
   | S n' => match k with
    | O => S O 
    | S k' => binomial_exp n' k + binomial_exp n' k'
    end
   end.


  Lemma nCo : forall n, (binomial_exp n 0 = 1)%nat.
  Proof.
    destruct n; simpl; reflexivity.
  Qed.

  Lemma nCone : forall n, (binomial_exp n 1 = n)%nat.
  Proof.
    induction n.
    - simpl. reflexivity.
    - simpl. rewrite IHn, nCo.
      lia.
  Qed.

  Lemma k_gt_n : forall (n k : nat), (n < k)%nat -> (binomial_exp n k = 0)%nat.
  Proof.
    induction n.
    - destruct k; simpl; intros Hf.
      lia. reflexivity.
    - destruct k; simpl; intros Hf;
      try lia.
      assert (Ht : (n < k)%nat) by lia.
      pose proof (IHn k Ht) as H₁.
      rewrite H₁. clear Ht; clear H₁.
      assert (Ht : (n < S k)%nat) by lia.
      pose proof (IHn (S k) Ht) as H₁.
      rewrite H₁. lia.
  Qed.


  Lemma nCn : forall n, (binomial_exp n n = 1)%nat.
  Proof.
    induction n.
    - simpl. reflexivity.
    - simpl. assert (Ht : (n < S n)%nat) by lia.
      pose proof (k_gt_n n (S n) Ht) as H.
      rewrite H. lia.
  Qed.


  Lemma snCsk : forall (n k : nat), 
    binomial_exp (S n) (S k) = (binomial_exp n (S k) + binomial_exp n k)%nat.
  Proof.
    intros ? ?; simpl;
    reflexivity.
  Qed.




  (* nCk = n!/ k! * (n - k)!
     (n + k)Ck = (n + k)!/ k! * n!
  *)

  Lemma connect_fact_with_binomial_exp_def : forall k n, 
    fact (n + k) = (fact k * fact n * binomial_exp (n + k) n)%nat.
  Proof.
    induction k.
    - simpl; intros ?.
      repeat rewrite Nat.add_0_r.
      rewrite nCn. nia.
    - induction n.
      + simpl. lia.
      + assert (Ht : (S n + S k = S (S n +  k))%nat).
        nia. rewrite Ht; clear Ht.
        rewrite snCsk, Nat.mul_add_distr_l.
        eapply eq_trans with 
          (y := (fact (S n + k) * S k + fact (n + S k) * S n)%nat).
        assert (Ht : (fact (S (S n + k)) = (S (S n + k)) * fact (S n + k))%nat).
        simpl. lia. rewrite Ht; clear Ht.
        assert (Ht : (S (S n + k) = S n + S k)%nat) by lia.
        rewrite Ht; clear Ht.
        rewrite Nat.mul_add_distr_r.
        rewrite <-Nat.add_comm. apply f_equal2.
        lia. assert (Ht : (n + S k = S n + k)%nat) by lia.
        rewrite Ht; clear Ht. lia.
        apply f_equal2.
        assert (Ht : (fact (S k) = (S k) * fact k)%nat).
        simpl. lia. rewrite Ht; clear Ht.
        pose proof (IHk (S n)) as Hs.
        assert (Ht : (S k * fact k * fact (S n) * binomial_exp (S n + k) (S n) =
          S k * (fact k * fact (S n) * binomial_exp (S n + k) (S n)))%nat).
        lia. rewrite Ht; clear Ht.
        rewrite <-Hs. lia.
        rewrite IHn.
        assert (Ht : (fact (S n) = (S n) * fact n)%nat).
        simpl. lia. rewrite Ht; clear Ht.
        assert (Ht : (S n + k = n + S k)%nat) by lia.
        rewrite Ht; clear Ht.
        lia.
  Qed.

  Lemma n_k_interchange : forall (n k : nat), 
    (binomial_exp (n + k) n = binomial_exp (n + k) k)%nat.
  Proof.
    intros ? ?.
    pose proof (connect_fact_with_binomial_exp_def n k) as H₁.
    pose proof (connect_fact_with_binomial_exp_def k n) as H₂.
    apply Nat.mul_cancel_l with (p := (fact k * fact n)%nat).
    pose proof (fact_neq_0 n) as Hn.
    pose proof (fact_neq_0 k) as Hk.
    lia. rewrite <-H₂.
    rewrite Nat.add_comm.
    assert (Ht : (fact k * fact n * binomial_exp (k + n) k = 
      fact n * fact k * binomial_exp (k + n) k)%nat) by lia.
    rewrite Ht; clear Ht.
    rewrite <-H₁.
    reflexivity.
  Qed.

  (* 
  forall x y, Nat.pow (x + y) n = nC0 x^n * y * 0 + 
  nC1 * x^(n-1) * y ^ 1 + nC2 * x ^ (n - 2) * y ^ 2 + nCn x ^0 * y ^ n 
  *)

  Fixpoint list_upto (n : nat) : list nat :=
    match n with 
    | O => [O]
    | S n' => n :: list_upto n'
    end.


  Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
    match n with 
    | O => []
    | S n' => match l with 
      | [] => []
      | h :: t => h :: (take n' t)
    end 
    end.

 
  Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
    match n with 
    | O => l
    | S n' => match l with 
      | [] => []
      | h :: t => drop n' t
    end
    end.

  Fixpoint zip_with {A B C : Type} (f : A -> B -> C) (l₁ : list A) 
    (l₂ : list B) : list C :=
    match l₁, l₂ with
    | h₁ :: t₁, h₂ :: t₂ =>  (f h₁ h₂) :: (zip_with f t₁ t₂)
    | _, _ => []
    end.
    
  
  Lemma zip_length_min : forall {X Y Z : Type}
    (f : X -> Y -> Z) l l', 
    length (zip_with f l l') = min (length l) (length l').
  Proof.
    induction l; destruct l'; simpl; eauto.
  Qed.

  Lemma zip_length : forall {X Y Z : Type} (f : X -> Y -> Z) 
    l l', length l = length l' -> length (zip_with f l l') = length l.
  Proof.
    intros * H. rewrite zip_length_min.
    rewrite H. rewrite Nat.min_id.
    eauto.
  Qed.

  Lemma zip_list_index {A B C : Type} (f : A -> B -> C) : forall 
    (l₁ : list A) (l₂ : list B) k def₁ def₂ def₃, 
    List.length l₁ = List.length l₂ -> 
    (k < List.length l₁)%nat -> 
    List.nth k (zip_with f l₁ l₂) def₁ = 
    f (List.nth k l₁ def₂) (List.nth k l₂ def₃).
  Proof.
    induction l₁.
    - simpl; intros ? ? ? ? ? Hl Hk.
      lia.
    - simpl; intros ? ? ? ? ? Hl Hk.
      destruct l₂.
      simpl in Hl.
      lia.
      simpl in Hl.
      inversion Hl as [Hlt]; clear Hl.
      destruct k.
      simpl. reflexivity.
      simpl.
      assert (Hw : (k < List.length l₁)%nat) by lia.
      clear Hk.
      apply IHl₁; assumption.
  Qed.



  Lemma zip_list_index_some {A B C : Type} (f : A -> B -> C) : forall 
    (l₁ : list A) (l₂ : list B) k t w, 
    List.length l₁ = List.length l₂ -> 
    (k < List.length l₁)%nat -> 
    Some t = List.nth_error l₁ k ->
    Some w = List.nth_error l₂ k ->
    List.nth_error (zip_with f l₁ l₂) k = Some (f t w).
  Proof.
    induction l₁.
    - simpl; intros ? ? ? ? ? Hl Hk Hw.
      lia.
    - simpl; intros ? ? ? ? Hl Hk Hw Hv.
      destruct l₂.
      simpl in Hl.
      lia.
      simpl in Hl.
      inversion Hl as [Hlt]; clear Hl.
      destruct k.
      simpl. simpl in Hw.
      simpl in Hv.
      inversion Hw; inversion Hv; subst.
      reflexivity.
      simpl.
      assert (Hwt : (k < List.length l₁)%nat) by lia.
      clear Hk.
      apply IHl₁; assumption.
  Qed.


  Lemma index_some {A : Type} : forall (l : list A) k, 
    (k < List.length l)%nat -> 
    exists t, Some t = List.nth_error l k.
  Proof.
    induction l.
    + destruct k; intros Hk.
      all:(simpl in Hk; lia).
    + destruct k; intros Hk.
      exists a. simpl; reflexivity.
      simpl in Hk.
      simpl. apply IHl.
      lia.
  Qed.


  Lemma take_drop_inv {A : Type} : forall (n : nat) (l : list A), 
    (take n l ++ drop n l = l).
  Proof.
    induction n.
    - simpl; intros ?; reflexivity.
    - simpl; intros ?.
      destruct l.
      + reflexivity.
      + simpl. rewrite IHn.
        reflexivity.
  Qed.


  Lemma list_upto_length : forall n : nat, 
    List.length (list_upto n) = S n.
  Proof.
    induction n.
    - simpl; reflexivity.
    - simpl; rewrite IHn;
      reflexivity.
  Qed.


  Lemma list_elem_bound : forall n x : nat, 
    In x (list_upto n) -> (x <= n)%nat.
  Proof.
    induction n.
    - simpl; intros ? [H | H]; lia.
    - simpl; intros ? [H | H]. lia.
      specialize (IHn x H).
      lia.
  Qed.

  Lemma list_elem_nth : forall n k : nat,
    (k < List.length (list_upto n))%nat -> 
    (List.nth_error (list_upto n) k = Some (n - k))%nat.
  Proof.
    induction n;simpl.
    + intros [|]; intro H; simpl.
      reflexivity. lia.
    + intros ? Hk.
      destruct k.
      - simpl. reflexivity.
      - simpl. apply IHn.
        lia.
  Qed.


  Definition populate_terms (x y n : nat) : list (nat * nat * nat) :=
    List.map (fun k => (k, n - k, binomial_exp n k * Nat.pow x k * 
      Nat.pow y (n - k)))%nat (list_upto n).



  Lemma populate_terms_length : forall n x y : nat, 
    List.length (populate_terms x y n) = S n.
  Proof.
    intros ? ? ?.
    unfold populate_terms.
    rewrite List.length_map.
    apply list_upto_length.
  Qed.

  Lemma populate_terms_values : forall n x y a b v : nat, 
      In (a, b, v) (populate_terms x y n) ->
      (a <= n /\ b <= n /\ a + b = n /\ 
      v = binomial_exp n a * Nat.pow x a * 
      Nat.pow y b)%nat.
  Proof.
    intros ? ? ? ? ? ? Hin.
    unfold populate_terms in Hin.
    apply in_map_iff in Hin.
    destruct Hin as (xt & H₁ & H₂).
    inversion H₁; subst.
    apply list_elem_bound in H₂.
    split. exact H₂.
    split. lia.
    split. lia.
    lia.
  Qed. 
    


  Lemma populate_term_nth : forall n k x y,
    (k < List.length (populate_terms x y n))%nat -> 
    List.nth_error (populate_terms x y n) k = 
    Some (n - k, k, binomial_exp n (n - k) * Nat.pow x (n - k) * 
    Nat.pow y k)%nat.
  Proof.
    intros * Hk.
    unfold populate_terms.
    rewrite nth_error_map.
    rewrite list_elem_nth.
    simpl. f_equal.
    f_equal. f_equal.
    rewrite populate_terms_length in Hk.
    lia.
    rewrite populate_terms_length in Hk.
    f_equal. 
    assert (Ht : (n - (n - k) = k)%nat).
    lia. rewrite Ht. reflexivity.
    rewrite populate_terms_length in Hk.
    rewrite list_upto_length.
    lia.
  Qed.
   
      
  
  Definition mul_x_populate_terms (x y n : nat) :=
    List.map (fun '(a, b, v) => (S a, b, x * v)%nat)
      (populate_terms x y n).


  Lemma mul_x_populate_terms_length : forall n x y : nat,
    List.length (mul_x_populate_terms x y n) = S n.
  Proof.
    intros *.
    unfold mul_x_populate_terms.
    rewrite List.length_map,
    populate_terms_length.
    reflexivity.
  Qed.



  Lemma mul_x_populate_terms_values : forall n x y a b v : nat, 
    In (S a, b, v) (mul_x_populate_terms x y n) ->
    (a <= n /\ b <= n /\ a + b = n /\ 
    v = binomial_exp n a * Nat.pow x (S a) * 
    Nat.pow y b)%nat.
  Proof.
    intros ? ? ? ? ? ? Hin.
    unfold mul_x_populate_terms in Hin.
    apply in_map_iff in Hin.
    destruct Hin as (xt & H₁ & H₂).
    repeat destruct xt.
    destruct p.
    inversion H₁; subst.
    apply populate_terms_values in H₂.
    split. lia.
    split. lia.
    split. lia.
    destruct H₂ as (H₂ & H₃ & H₄ & H₅).
    simpl. lia.
  Qed.
 


  Lemma mul_x_populate_terms_nth : forall n k x y,
    (k < List.length (mul_x_populate_terms x y n))%nat ->
    List.nth_error (mul_x_populate_terms x y n) k = 
    Some (S (n - k), k, x * binomial_exp n (n - k) * Nat.pow x (n - k) * 
    Nat.pow y k)%nat.
  Proof.
    intros * Hk.
    unfold mul_x_populate_terms.
    rewrite nth_error_map.
    assert (Ht : (k < List.length (populate_terms x y n))%nat).
    rewrite mul_x_populate_terms_length in Hk.
    rewrite populate_terms_length.
    exact Hk.
    pose proof (populate_term_nth _ _ _ _ Ht) as Hp.
    rewrite Hp. simpl. f_equal.
    f_equal. lia.
  Qed.


  Definition mul_y_populate_terms (x y n : nat) :=
    List.map (fun '(a, b, v) => (a, S b, y * v)%nat)
      (populate_terms x y n).


  Lemma mul_y_populate_terms_length : forall n x y : nat,
    List.length (mul_y_populate_terms x y n) = S n.
  Proof.
    intros *.
    unfold mul_y_populate_terms.
    rewrite List.length_map,
    populate_terms_length.
    reflexivity.
  Qed.




  Lemma mul_y_populate_terms_values : forall n x y a b v : nat, 
    In (a, S b, v) (mul_y_populate_terms x y n) ->
    (a <= n /\ b <= n /\ a + b = n /\ 
    v = binomial_exp n a * Nat.pow x a * 
    Nat.pow y (S b))%nat.
  Proof.
    intros ? ? ? ? ? ? Hin.
    unfold mul_y_populate_terms in Hin.
    apply in_map_iff in Hin.
    destruct Hin as (xt & H₁ & H₂).
    repeat destruct xt.
    destruct p.
    inversion H₁; subst.
    apply populate_terms_values in H₂.
    split. lia.
    split. lia.
    split. lia.
    destruct H₂ as (H₂ & H₃ & H₄ & H₅).
    simpl. lia.
  Qed.


  Lemma mul_y_populate_terms_nth : forall n k x y,
    (k < List.length (mul_y_populate_terms x y n))%nat ->
    List.nth_error (mul_y_populate_terms x y n) k = 
    Some ((n - k), S k, y * binomial_exp n (n - k) * Nat.pow x (n - k) * 
    Nat.pow y k)%nat.
  Proof.
    intros * Hk.
    unfold mul_y_populate_terms.
    rewrite nth_error_map.
    assert (Ht : (k < List.length (populate_terms x y n))%nat).
    rewrite mul_y_populate_terms_length in Hk.
    rewrite populate_terms_length.
    exact Hk.
    pose proof (populate_term_nth _ _ _ _ Ht) as Hp.
    rewrite Hp. simpl. f_equal.
    f_equal. lia.
  Qed.



  (* align the two polynomials *)
  Definition append_mul_x_populate_terms (x y n : nat) :=
    mul_x_populate_terms x y n ++ [(O, S n, O)].
  


  Lemma append_mul_x_populate_terms_length : forall n x y,
    List.length (append_mul_x_populate_terms x y n) = 
    S (S n).
  Proof.
    intros *.
    unfold append_mul_x_populate_terms.
    rewrite List.length_app,
    mul_x_populate_terms_length.
    simpl. lia.
  Qed.

  


  Lemma append_mul_x_populate_terms_nth : forall n k x y,
    (k < List.length (append_mul_x_populate_terms x y n))%nat ->
    List.nth_error (append_mul_x_populate_terms x y n) k = 
    (if k <? S n then 
      Some (S (n - k), k, x * binomial_exp n (n - k) * Nat.pow x (n - k) * 
      Nat.pow y k)
    else Some (O, S n, O))%nat.
  Proof.
    intros * Hk.
    pose proof (append_mul_x_populate_terms_length n x y) as Hv.
    unfold append_mul_x_populate_terms.
    pose proof (mul_x_populate_terms_length n x y) as Hp.
    assert (Ht : ((k < S n) \/ (k = S n))%nat) by lia.
    destruct Ht as [Ht | Ht].
    assert (Hw : ((k <? S n) = true)%nat).
    apply Nat.ltb_lt. exact Ht.
    rewrite Hw.
    rewrite nth_error_app1.
    rewrite mul_x_populate_terms_nth.
    f_equal. lia. 
    lia.
    assert (Hw : ((k <? S n) = false)%nat). rewrite Ht.
    apply Nat.ltb_ge. lia.
    rewrite Hw. 
    pose proof (@nth_error_app2 _ (mul_x_populate_terms x y n) 
    [(0%nat, S n, 0%nat)] k) as Hpp.
    assert (Hvw : (length (mul_x_populate_terms x y n) <= k)%nat).
    lia.
    specialize (Hpp Hvw).
    rewrite Hpp.
    rewrite Ht.
    rewrite Hp.
    simpl. 
    assert (Hnn : (n - n = 0)%nat) by lia.
    rewrite Hnn.
    simpl. reflexivity.
  Qed.
    


  
  Definition append_mul_y_populate_terms (x y n : nat) :=
    (S n, O, O) :: mul_y_populate_terms x y n.
  
  
  Lemma append_mul_y_populate_terms_length : forall n x y,
    List.length (append_mul_y_populate_terms x y n) = 
    S (S n).
  Proof.
    intros *.
    unfold append_mul_y_populate_terms.
    simpl;
    rewrite mul_y_populate_terms_length;
    lia.
  Qed.


  Lemma append_mul_y_populate_terms_nth : forall n k x y,
    (k < List.length (append_mul_y_populate_terms x y n))%nat ->
    List.nth_error (append_mul_y_populate_terms x y n) k =
    (if k =? O then Some (S n, O, O) 
    else Some ((n - (k - 1)), S (k - 1), y * binomial_exp n (n - (k - 1)) * 
      Nat.pow x (n - (k - 1)) * Nat.pow y (k - 1)))%nat.
  Proof.
    intros * Hk.
    unfold append_mul_y_populate_terms.
    assert (Ht : ((k = 0) \/ (0 < k))%nat). lia.
    destruct Ht as [Ht | Ht].
    rewrite Ht. simpl.
    reflexivity.
    assert (Hw : (k =? 0 = false)%nat).
    apply Nat.eqb_neq. lia.
    rewrite Hw.
    pose proof (@nth_error_app2 _ [(S n, 0, 0)] 
      (mul_y_populate_terms x y n) k) as Hp.
    simpl in Hp.
    assert (Htt : (1 <= k)%nat). lia.
    specialize (Hp Htt).
    rewrite Hp.
    simpl. 
    rewrite mul_y_populate_terms_nth.
    f_equal.
    pose proof (append_mul_y_populate_terms_length n x y) as Hwtt.
    unfold append_mul_y_populate_terms in Hwtt.
    simpl in Hwtt.
    rewrite mul_y_populate_terms_length.
    rewrite append_mul_y_populate_terms_length in Hk.
    lia.
  Qed.
    



  (* assumes that indexes are aligned *)
  Definition add_polynomials (x y n : nat) :=
    zip_with 
    (fun '(x, y, a) '(_, _, b) => (x, y, a + b)%nat)
    (append_mul_x_populate_terms x y n)
    (append_mul_y_populate_terms x y n).




  Lemma add_polynomials_length : forall x y n, 
    List.length (add_polynomials x y n) = S (S n).
  Proof.
    intros *.
    unfold add_polynomials.
    rewrite zip_length.
    rewrite append_mul_x_populate_terms_length.
    reflexivity.
    rewrite append_mul_x_populate_terms_length.
    rewrite append_mul_y_populate_terms_length.
    reflexivity.
  Qed.



  Lemma add_polynomials_nth : forall n x y k  a b c u v w l m t : nat,
    (k < S (S n))%nat ->
    Some (a, b, c) = List.nth_error (append_mul_x_populate_terms x y n) k ->
    Some (u, v, w) = List.nth_error (append_mul_y_populate_terms x y n) k ->
    Some (l, m, t) = List.nth_error (add_polynomials x y n) k -> 
    (a = l /\ b = m /\ t = c + w /\ l = u /\ m = v)%nat.
  Proof.
    intros * Hk Ha Hb Hc.
    rewrite append_mul_x_populate_terms_nth in Ha.
    rewrite append_mul_y_populate_terms_nth in Hb.
    unfold add_polynomials in Hc.
    pose proof (append_mul_x_populate_terms_length n x y) as Hx.
    pose proof (append_mul_y_populate_terms_length n x y) as Hy.
    assert (Hxx : (k < length (append_mul_x_populate_terms x y n))%nat).
    lia.
    assert(Hyy: (k < length (append_mul_y_populate_terms x y n))%nat).
    lia.
    destruct (index_some (append_mul_x_populate_terms x y n) k Hxx) as [t₁ Ht₁].
    destruct (index_some (append_mul_y_populate_terms x y n) k Hyy) as [t₂ Ht₂].
    erewrite zip_list_index_some with (t := t₁) (w := t₂) in Hc.
    destruct t₁. destruct p.
    destruct t₂. destruct p.
    inversion Hc; subst; clear Hc.
    rewrite append_mul_x_populate_terms_nth in Ht₁.
    rewrite append_mul_y_populate_terms_nth in Ht₂.
    assert (Ht : ((k = O) \/ (k = (S n)) \/ (S O <= k < S n))%nat).
    lia.
    destruct Ht as [Ht | [Ht | Ht]].
    rewrite Ht in Hb, Ht₂.
    simpl in *.
    assert (Hkt : (k <? S n = true)%nat).
    rewrite Ht. compute. reflexivity.
    rewrite Hkt in Ha, Ht₁.
    inversion Ha; subst; clear Ha.
    inversion Hb; subst; clear Hb.
    inversion Ht₁; subst; clear Ht₁.
    inversion Ht₂; subst; clear Ht₂.
    simpl. lia.
    assert (Hkt: (k =? 0 = false)%nat).
    rewrite Ht. compute. reflexivity.
    rewrite Hkt in Hb, Ht₂.
    clear Hkt.
    assert (Hkt: (k <? S n = false)%nat).
    rewrite Ht. apply Nat.ltb_irrefl.
    rewrite Hkt in Ha, Ht₁.
    clear Hkt.
    inversion Ha; subst; clear Ha.
    inversion Hb; subst; clear Hb.
    inversion Ht₁; subst; clear Ht₁.
    inversion Ht₂; subst; clear Ht₂.
    simpl.
    repeat split; try lia.
    assert (Hn : (n - 0 = n)%nat).
    lia. clear Hn.
    destruct Ht as [Htl Htr].
    assert (Hkt : (k <? S n = true)%nat).
    apply Nat.ltb_lt. exact Htr.
    rewrite Hkt in Ha, Ht₁.
    clear Hkt.
    assert (Hkt: (k =? 0 = false)%nat).
    apply Nat.eqb_neq. lia.
    rewrite Hkt in Hb, Ht₂.
    clear Hkt.
    inversion Ha; subst; clear Ha.
    inversion Hb; subst; clear Hb.
    inversion Ht₁; subst; clear Ht₁.
    inversion Ht₂; subst; clear Ht₂.
    lia.
    all:(try assumption; try reflexivity).
    rewrite Hx, Hy. reflexivity.
    rewrite append_mul_y_populate_terms_length.
    lia.
    rewrite append_mul_x_populate_terms_length.
    lia.
  Qed.


  
  
  Lemma add_polynomials_membership : forall n x y k : nat,
    (k < S (S n))%nat ->
    List.nth k (add_polynomials x y n) (O, O, O) = 
    (fun '(x, y, a) '(_, _, b) => (x, y, a + b)%nat)
    (List.nth k (append_mul_x_populate_terms x y n) (O, O, O))
    (List.nth k (append_mul_y_populate_terms x y n) (O, O, O)).
  Proof.
    intros ? ? ? ? Hk.
    unfold add_polynomials.
    erewrite zip_list_index.
    reflexivity.
    unfold append_mul_x_populate_terms,
    append_mul_y_populate_terms,
    mul_x_populate_terms, 
    mul_y_populate_terms.
    simpl. rewrite List.length_map,
    List.last_length. simpl.
    rewrite List.length_map.
    apply f_equal.
    reflexivity.
    rewrite append_mul_x_populate_terms_length.
    exact Hk.
  Qed.



  Lemma populate_terms_membership : forall n k x y a b c u v w l m t : nat,
    (k < S (S n))%nat ->
    Some (a, b, c) = List.nth_error (append_mul_x_populate_terms x y n) k ->
    Some (u, v, w) = List.nth_error (append_mul_y_populate_terms x y n) k ->
    Some (l, m, t) = List.nth_error (populate_terms x y (S n)) k ->
    (a = l /\ b = m /\ t = c + w /\ l = u /\ m = v)%nat.
  Proof.
    intros * H₁ H₂ H₃ H₄.
    unfold append_mul_x_populate_terms in H₂.
    unfold append_mul_y_populate_terms in H₃.
    assert (Ht : ((k = O) \/ (k = (S n)) \/ (S O <= k < S n))%nat).
    lia.
    destruct Ht as [Ht | [Ht | Ht]].
    rewrite Ht in H₂, H₃, H₄.
    simpl in H₃.
    rewrite populate_term_nth in H₄.
    rewrite nth_error_app1 in H₂.
    rewrite mul_x_populate_terms_nth in H₂.
    inversion H₂; inversion H₃;
    inversion H₄; subst; clear H₂; clear H₃; 
    clear H₄. split.
    lia. split. lia.
    split. rewrite nCn.
    assert (Hn : (n - 0 = n)%nat).
    lia. rewrite Hn. clear Hn.
    rewrite nCn.
    rewrite k_gt_n. simpl.
    lia. lia. lia.
    rewrite mul_x_populate_terms_length.
    lia.
    rewrite mul_x_populate_terms_length.
    lia.
    rewrite populate_terms_length. lia.
    rewrite populate_term_nth in H₄.
    pose proof (@nth_error_app2 _ (mul_x_populate_terms x y n) 
    [(0%nat, S n, 0%nat)] k) as Hpp.
    assert (Hvw : (length (mul_x_populate_terms x y n) <= k)%nat).
    rewrite mul_x_populate_terms_length. 
    lia.
    specialize (Hpp Hvw).
    rewrite Hpp in H₂.
    rewrite mul_x_populate_terms_length, Ht in H₂.
    rewrite Nat.sub_diag in H₂.
    simpl in H₂.
    rewrite Ht in H₃.
    pose proof (@nth_error_app2 _ [(S n, 0, 0)] 
      (mul_y_populate_terms x y n) k) as Hp.
    simpl in Hp.
    assert (Htt : (1 <= k)%nat). lia.
    specialize (Hp Htt).
    rewrite Ht in Hp.
    rewrite Hp in H₃.
    simpl in H₃.
    rewrite Nat.sub_0_r in H₃.
    clear Hpp; clear Hvw; clear Hp.
    rewrite mul_y_populate_terms_nth in H₃.
    simpl in H₃.
    rewrite Nat.sub_diag in H₃.
    rewrite Ht in H₄.
    rewrite Nat.sub_diag in H₄.
    inversion H₂; inversion H₃;
    inversion H₄; subst; clear H₂; clear H₃; 
    clear H₄.
    simpl. rewrite nCo.
    lia.
    rewrite mul_y_populate_terms_length.
    lia. 
    rewrite populate_terms_length.
    lia.
    destruct Ht as [Htl Htr].
    pose proof (@nth_error_app2 _ [(S n, 0, 0)] 
      (mul_y_populate_terms x y n) k Htl) as Hp.
    simpl in Hp.
    rewrite Hp in H₃.
    clear Hp.
    rewrite nth_error_app1 in H₂.
    rewrite mul_x_populate_terms_nth in H₂.
    rewrite mul_y_populate_terms_nth in H₃.
    rewrite populate_term_nth in H₄.
    inversion H₂; inversion H₃;
    inversion H₄; subst; clear H₂; clear H₃; 
    clear H₄. split.
    destruct k. lia.
    lia.
    split. lia.
    destruct k. lia.
    split.
    destruct (n - k) eqn:Hk.
    lia.
    simpl.
    assert (Hsn : n - S k = n0).
    lia. rewrite Hsn.
    rewrite Nat.sub_0_r.
    rewrite Hk.
    rewrite <-Hk.
    rewrite <-Hsn.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.add_comm.
    f_equal. lia.
    assert (Hx : (x * x ^ (n - S k)) = 
    (x ^ (n - k))).
    rewrite <-Nat.pow_succ_r.
    assert (Hss : S (n - S k) = n - k).
    lia. rewrite Hss.
    reflexivity. lia.
    rewrite Hx. lia.
    lia.
    rewrite populate_terms_length.
    lia.
    rewrite mul_y_populate_terms_length.
    lia. 
    rewrite mul_x_populate_terms_length.
    lia.
    rewrite mul_x_populate_terms_length.
    lia.
  Qed.


  Lemma populate_terms_membership_simp : forall n k x y a b c u v w : nat,
    (k < S (S n))%nat ->
    Some (a, b, c) = List.nth_error (append_mul_x_populate_terms x y n) k ->
    Some (u, v, w) = List.nth_error (append_mul_y_populate_terms x y n) k ->
    Some (a, b, c + w) = List.nth_error (populate_terms x y (S n)) k.
  Proof.
    intros * H₁ H₂ H₃.
    assert (Ht : k < List.length (populate_terms x y (S n))).
    rewrite populate_terms_length. lia.
    pose proof (populate_term_nth _ k x y Ht) as Hw.
    symmetry in Hw.
    destruct (populate_terms_membership n k x y a b c u v w _ _ _ 
      H₁ H₂ H₃ Hw) as (Ha & Hb & Hc & Hd & He).
    rewrite <-Hw.
    f_equal. f_equal. f_equal.
    exact Ha.
    exact Hb.
    symmetry.
    exact Hc.
  Qed.

    

   

  Lemma add_poly_def_correct_pointwise : forall n x y k,
    k < S (S n) -> 
    List.nth_error (add_polynomials x y n) k = 
    List.nth_error (populate_terms x y (S n)) k.
  Proof.
    intros * Hk.
    unfold add_polynomials.
    pose proof (append_mul_x_populate_terms_length n x y) as Hx.
    pose proof (append_mul_y_populate_terms_length n x y) as Hy.
    assert (Hxx : (k < length (append_mul_x_populate_terms x y n))%nat).
    lia.
    assert(Hyy: (k < length (append_mul_y_populate_terms x y n))%nat).
    lia.
    destruct (index_some (append_mul_x_populate_terms x y n) k Hxx) as [t₁ Ht₁].
    destruct (index_some (append_mul_y_populate_terms x y n) k Hyy) as [t₂ Ht₂].
    erewrite zip_list_index_some with (t := t₁) (w := t₂).
    destruct t₁. destruct p.
    destruct t₂. destruct p.
    apply populate_terms_membership_simp with (u := n4) (v := n5).
    lia. exact Ht₁.
    exact Ht₂.
    rewrite append_mul_x_populate_terms_length.
    rewrite append_mul_y_populate_terms_length.
    reflexivity.
    rewrite append_mul_x_populate_terms_length.
    lia. exact Ht₁. exact Ht₂.
  Qed.

  (* Not in Coq library! *)
  Lemma nth_ext_error {A : Type} : forall (l l' : list A), 
    length l = length l' ->
    (forall n, n < length l -> nth_error l n = nth_error l' n) -> l = l'.
  Proof.
    induction l.
    + destruct l'.
      simpl; intros Hl Hn.
      reflexivity.
      simpl; intros Hl Hn.
      lia.
    + destruct l'.
      simpl; intros Hl Hn.
      lia.
      simpl; intros Hl Hn.
      assert (Ht : 0 < S (length l)).
      lia.
      pose proof (Hn 0 Ht) as Hp.
      simpl in Hp.
      f_equal. inversion Hp.
      reflexivity.
      apply IHl.
      lia.
      intros ? Hnn.
      assert (Hv : S n < S (length l)).
      lia.
      pose proof (Hn _  Hv).
      simpl in H.
      exact H.
  Qed.


  (*
  
  Example ct : add_polynomials 1 0 5 = populate_terms 1 0 6.
    reflexivity.
  Qed.

  *)

  Lemma add_poly_def_correct : forall n x y,
    add_polynomials x y n = populate_terms x y (S n).
  Proof.
    intros *.
    pose proof (@nth_ext_error (nat * nat * nat)
      (add_polynomials x y n) (populate_terms x y (S n))).
    assert (Ht : length (add_polynomials x y n) = S (S n)).
    rewrite add_polynomials_length.
    reflexivity.
    assert (Hw : length (populate_terms x y (S n)) = S (S n)).
    rewrite populate_terms_length.
    reflexivity.
    rewrite Ht, Hw in H.
    exact (H eq_refl (add_poly_def_correct_pointwise n x y)).
  Qed.
    


  
  Definition sum_xy (x y : nat) (n : nat) : nat :=
    List.fold_right (fun x acc => acc + x)%nat 0%nat 
    (List.map (fun '(_, _, x) => x ) (populate_terms x y n)).



  Lemma fold_right_eq : forall l n a x y,
    a * fold_right (fun x0 acc : nat => acc + x0) 0
      (map (fun k : nat => binomial_exp n k * x ^ k * y ^ (n - k)) l) =
    fold_right (fun x0 acc : nat => acc + x0) 0
      (map (fun k : nat => a * binomial_exp n k * x ^ k * y ^ (n - k)) l).
  Proof.
    induction l.
    + intros *; simpl; lia.
    + intros *; simpl.
      specialize (IHl n a0 x y).
      rewrite Nat.mul_add_distr_l.
      rewrite IHl.
      lia.
  Qed.


  Lemma fold_right_add : forall l n x y, 
    fold_right (fun x0 acc : nat => acc + x0) 0
    (map (fun k : nat => x * binomial_exp n k * x ^ k * y ^ (n - k)) l) 
    +
    fold_right (fun x0 acc : nat => acc + x0) 0
    (map (fun k : nat => y * binomial_exp n k * x ^ k * y ^ (n - k)) l) 
    =
    fold_right (fun x0 acc : nat => acc + x0) 0
    (map (fun k : nat => 
      x * binomial_exp n k * x ^ k * y ^ (n - k) + 
      y * binomial_exp n k * x ^ k * y ^ (n - k)) l).
  Proof.
    induction l.
    + intros *; simpl; reflexivity.
    + intros *; simpl.
      rewrite <-IHl.
      lia.
  Qed. 


  Lemma push_fn_inside : forall l n x y att bt ct ut vt wt,
    map (fun '(y0, x0) => let '(_, _) := y0 in x0)
    (zip_with
      (fun '(y0, a) =>
        let
        '(x0, y1) := y0 in
        fun '(y2, b) => let '(_, _) := y2 in (x0, y1, a + b))
      (map
          (fun x0 : nat =>
          (S x0, n - x0, x * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0))))
          l ++ [(att, bt, ct)])
      ((ut, vt, wt)
        :: map
            (fun x0 : nat =>
              (x0, S (n - x0),
              y * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0)))) l)) 
    =
    zip_with (fun a b : nat => a + b)
    (map (fun x0 : nat => x * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0)))
      l ++ [ct])
    (wt :: 
    map (fun x0 : nat => y * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0))) l).
  Proof.
    induction l.
    + intros *; simpl; reflexivity.
    + intros *; simpl.
      f_equal.
      rewrite IHl.
      reflexivity.
  Qed.     


  Lemma fold_right_simp : forall l n x y u v, 
    fold_right (fun x0 acc : nat => acc + x0) 0
    (zip_with (fun a b : nat => a + b)
      (map (fun x0 : nat => x * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0))) l ++
        [u])
      (v :: map (fun x0 : nat => y * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0)))
        l))
    = 
    u + v + 
    fold_right (fun x0 acc : nat => acc + x0) 0
    (zip_with (fun a b : nat => a + b)
     (map (fun x0 : nat => x * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0))) l)
     (map (fun x0 : nat => y * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0))) l)).
  Proof.
    induction l.
    + intros *; simpl. lia. 
    + intros *; simpl.
      rewrite IHl.
      lia.
  Qed.

  

  Lemma fold_right_gen : forall l n x y,
    fold_right (fun x0 acc : nat => acc + x0) 0
    (map
      (fun k : nat =>
        x * binomial_exp n k * x ^ k * y ^ (n - k) +
        y * binomial_exp n k * x ^ k * y ^ (n - k)) l) 
    =
    fold_right (fun x0 acc : nat => acc + x0) 0
    (map (fun '(y0, x0) => let '(_, _) := y0 in x0)
      (zip_with
          (fun '(y0, a) =>
          let
          '(x0, y1) := y0 in
            fun '(y2, b) => let '(_, _) := y2 in (x0, y1, a + b))
          (map
            (fun x0 : nat =>
              (S x0, n - x0, x * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0))))
            l ++ [(0, S n, 0)])
          ((S n, 0, 0)
          :: map
                (fun x0 : nat =>
                (x0, S (n - x0),
                y * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0))))
                l))).
  Proof.
    intros *.
    rewrite push_fn_inside.
    rewrite fold_right_simp.
    simpl.
    revert l n x y.
    induction l.
    + intros *; simpl; reflexivity.
    + intros *; simpl.
      rewrite IHl. lia.
  Qed.

  

      

  Lemma pow_add : forall (n x y : nat), 
    (Nat.pow (x + y) n = sum_xy x y n)%nat.
  Proof.
    induction n.
    + unfold sum_xy; intros *; simpl;
      reflexivity.
    + simpl; intros *.
      unfold sum_xy.
      rewrite <-add_poly_def_correct.
      unfold add_polynomials,
      append_mul_x_populate_terms,
      append_mul_y_populate_terms,
      mul_x_populate_terms,
      mul_y_populate_terms,
      populate_terms.
      repeat rewrite map_map.
      unfold sum_xy, populate_terms in IHn.
      assert (Hxy: (x + y) * (x + y) ^ n = 
        x * (x + y) ^ n + y * (x + y) ^ n).
      lia. rewrite Hxy; clear Hxy.
      rewrite IHn.
      rewrite map_map.
      repeat rewrite fold_right_eq.
      rewrite fold_right_add.
      rewrite fold_right_gen.
      reflexivity.
  Qed.



  Lemma connection_between_divide_and_mod : forall n p : nat,
    prime (Z.of_nat p) ->
    Nat.divide p n <-> Nat.modulo n p = 0.
  Proof.
    intros * Hp; split; intro H.
    unfold Nat.divide in H.
    destruct H as [z Hz].
    rewrite Hz.
    rewrite Nat.Div0.mod_mul.
    reflexivity. 
    apply prime_ge_2 in Hp.
    apply Nat.Div0.mod_divides in H.
    destruct H as [c Hn].
    econstructor.
    instantiate (1 := c).
    lia.
  Qed.

  Lemma connection_between_not_divide_and_mod : forall n p : nat,
    prime (Z.of_nat p) ->
    ~Nat.divide p n <-> Nat.modulo n p <> 0.
  Proof.
    intros n p Hp; split; intros Hnd.
    intro H. apply Hnd.
    apply connection_between_divide_and_mod.
    exact Hp.
    exact H.
    intros H.
    apply Hnd.
    apply connection_between_divide_and_mod.
    exact Hp.
    exact H.
  Qed.


  Lemma prime_div_mul : forall p a b : nat,
    prime (Z.of_nat p) -> Nat.divide p (a * b) -> 
    Nat.divide p a \/ Nat.divide p b.
  Proof.
    intros * Hp Hpab.
    pose proof prime_ge_2 (Z.of_nat p) Hp as Hpf.
    apply connection_between_divide_and_mod in Hpab.
    pose proof prime_mult (Z.of_nat p) Hp
    (Z.of_nat a) (Z.of_nat b).
    assert (Hz : (Z.divide (Z.of_nat p) (Z.of_nat a * Z.of_nat b)%Z)).
    apply Z.mod_divide. lia.
    rewrite <-Nat2Z.inj_mul,
    <-Nat2Z.inj_mod.
    lia.
    destruct (H Hz) as [Hl | Hl].
    left.
    apply Z.mod_divide in Hl.
    rewrite <-Nat2Z.inj_mod in Hl.
    apply connection_between_divide_and_mod.
    exact Hp. lia.
    lia.
    apply Z.mod_divide in Hl.
    rewrite <-Nat2Z.inj_mod in Hl.
    right.
    apply connection_between_divide_and_mod.
    exact Hp. lia.
    lia.
    exact Hp.
  Qed.

    


    
  Theorem divide_is_le : forall a b : nat, b <> 0 -> Nat.divide a b -> a <= b.
  Proof.
    intros * Hb Hn.
    unfold Nat.divide in Hn.
    destruct Hn as [z Hn].
    rewrite Hn.
    assert (Hza : z * a <> 0).
    lia.
    destruct z; lia.
  Qed.
  

  Lemma fact_k_nt_zero : forall k p : nat, 
    prime (Z.of_nat p) -> 1 <= k < p -> Nat.modulo (fact k) p <> 0.
  Proof.
    induction k; simpl.
    - intros * Hp Hk; lia.
    - intros * Hp Hk.
      destruct k.
      + simpl. 
        rewrite Nat.mod_1_l.
        lia. lia.
      + remember (S k) as t.
        assert (Ht : 1 <= t < p).
        lia.
        pose proof (IHk p Hp Ht) as Hs.
        intro H.
        assert (Hf : fact t + t * fact t = (1 + t) * fact t).
        lia. rewrite Hf in H; clear Hf.
        (* 
        From H, I know that that p divides ((1 + t) * fact t)
        that means either p divides (1 + t) or 
        p divides fact t.
        Case analysis:
        1. p divides (1 + t)
          but from Hk, 1 + t < p, p does not divide (1 + t) contradiction.
        2. p divides fact k means mod (fact k) p = 0 but 
          we have induction hypothesis that mod (fact k) p <> 0.
        We are home!
        *)
        apply connection_between_divide_and_mod in H.
        apply prime_div_mul in H.
        destruct H as [H | H].
        apply divide_is_le in H.
        lia. lia.
        apply connection_between_divide_and_mod in H.
        lia.
        all:exact Hp.
  Qed.  
        



  Lemma fact_pk_nt_zero : forall k p : nat, 
    prime (Z.of_nat p) -> 1 <= k < p -> Nat.modulo (fact (p - k)) p <> 0.
  Proof.
    intros * Hp Hk.
    assert (1 <= p - k < p).
    lia.
    apply fact_k_nt_zero.
    exact Hp.
    exact H.
  Qed.


  Lemma fact_p_zero : forall p : nat, 
    prime (Z.of_nat p) ->  Nat.modulo (fact p) p = 0.
  Proof.
    intros p Hp.
    apply prime_ge_2 in Hp.
    destruct p.
    lia. destruct p.
    lia.
    assert (Hf : fact (S (S p)) = S (S p) * fact (S p)).
    simpl. reflexivity.
    rewrite Hf; clear Hf.
    rewrite Nat.mul_comm,
    Nat.Div0.mod_mul.
    reflexivity.
  Qed.


  (*
      Proof Idea:
      1. We know that  Nat.modulo (fact k) p <> 0 because 
        1 <= k < p
      2. Similarly, Nat.modulo (fact (p - k)) p <> 0 because 
        1 <= k < p and 1 <= p - k < p 
      3. Multiply both sides of Hmp by inverse (fact k) mod p and 
        inverse (fact (p - k)) mod p. 
      Hmp: fact p mod p = (fact k * fact (p - k) * binomial_exp p k) mod p
      4. Replace the expression in the goal, binomial_exp p k mod p = 0, 
        by inv (fact k ) mod p * inv (fact (p - k)) mod * fact p mod p.
      5. But fact p mod p = 0 (and we are home)
    
  *)
  Lemma binom_mod_p : forall p k : nat, 
    prime (Z.of_nat p) ->
    Nat.modulo (binomial_exp p k) p = 0 <->
    k <> 0 /\ k <> p.
  Proof.
    intros * Hp.
    split; intro Hb.
    split; intro Hk.
    rewrite Hk in Hb.
    rewrite nCo in Hb.
    rewrite Nat.mod_1_l in Hb.
    lia. 
    apply prime_ge_2 in Hp. 
    lia.
    rewrite Hk in Hb.
    rewrite nCn in Hb.
    rewrite Nat.mod_1_l in Hb.
    lia. 
    apply prime_ge_2 in Hp. 
    lia.
    destruct Hb as [Hbl Hbr].
    assert (Hpp: (2 <= Z.of_nat p)%Z).
    eapply prime_ge_2; assumption.
    assert (Hk : (p < k) \/ (k <= p)). 
    lia.
    destruct Hk as [Hk | Hk].
    pose proof k_gt_n p k Hk as Hppp.
    rewrite Hppp.
    rewrite Nat.Div0.mod_0_l.
    reflexivity. 
    assert (Hkp: 1 <= k < p). 
    lia. 
    pose proof connect_fact_with_binomial_exp_def k (p - k) as Hvt.
    rewrite n_k_interchange in Hvt.
    assert (Hw : p - k + k = p).
    lia. rewrite Hw in Hvt; clear Hw.
    assert (Hmp: Nat.modulo (fact p) p = 
      Nat.modulo (fact k * fact (p - k) * binomial_exp p k) p).
    rewrite Hvt. reflexivity.
    symmetry in Hmp.
    rewrite fact_p_zero in Hmp.
    pose proof fact_k_nt_zero k p Hp Hkp as Hf.
    pose proof fact_pk_nt_zero k p Hp Hkp as Hpf.
    apply connection_between_divide_and_mod. 
    exact Hp.
    apply connection_between_divide_and_mod  in Hmp.
    apply prime_div_mul in Hmp.
    destruct Hmp as [Hmp | Hmp].
    apply prime_div_mul in Hmp.
    destruct Hmp as [Hmp | Hmp].
    apply connection_between_not_divide_and_mod in Hf.
    congruence.
    exact Hp.
    apply connection_between_not_divide_and_mod in Hpf.
    congruence.
    exact Hp. exact Hp.
    exact Hmp.
    all:exact Hp.
  Qed.
    
   

  Lemma binom_mod_p_bound : forall p k : nat, 
    prime (Z.of_nat p) -> k <= p -> 
    Nat.modulo (binomial_exp p k) p = 0 <->
    1 <= k < p.
  Proof.
    intros * Hp Hk; split; intro H.
    apply binom_mod_p in H.
    lia.
    exact Hp.
    apply binom_mod_p.
    exact Hp.
    lia.
  Qed.


  Lemma list_upto_no_dup : forall n, 
    NoDup (list_upto n).
  Proof.
    induction n.
    + simpl. constructor.
      intros H. inversion H.
      constructor.
    + simpl. constructor.
      intros H.
      pose proof list_elem_bound n (S n) H as Hf.
      lia.
      exact IHn.
  Qed.



  Lemma split_upto_hd_tl : forall n : nat, 
    2 <= n -> exists l : list nat, 
    list_upto n = n :: l ++ [0] /\ 
    (forall x, In x l -> 1 <= x < n).
  Proof.
    induction n.
    + intros H; lia.
    + destruct n.
      - intros H; lia.
      - intros H; destruct n.
        ++
          simpl. exists [1].
          split. reflexivity.
          intros ? Hx. simpl in Hx.
          destruct Hx as [Hx | Hx]; 
          lia.
        ++ assert (Hp: 1 < S (S n)) by lia.
           destruct (IHn Hp) as [lp [Hl Hr]].
           simpl in * |- *.
           exists (S (S n) :: lp).
           split. f_equal.
           rewrite Hl. simpl.
           reflexivity.
           intros x [Hx | Hx].
           lia. specialize (Hr x Hx).
           lia.
  Qed.



     


  Lemma prime_pow_exp : forall (x p : nat),
    prime (Z.of_nat p) ->
    Nat.modulo (Nat.pow (x + 1) p) p = Nat.modulo (Nat.pow x p + 1) p.
  Proof.
    intros * Hp.
    rewrite pow_add.
    unfold sum_xy, populate_terms.
    rewrite map_map.
    pose proof prime_ge_2 (Z.of_nat p) Hp as Hpp.
    assert (Hpt : 2 <= p). lia.
    destruct (split_upto_hd_tl p Hpt) as [l [Hl Hr]].
    rewrite Hl. simpl. 
    rewrite map_last. simpl.
    rewrite nCn, nCo.
    simpl. rewrite Nat.sub_diag,
    Nat.sub_0_r, Nat.pow_1_l,
    Nat.add_0_r. simpl.
    rewrite Nat.add_0_r,
    Nat.mul_1_r.
    rewrite fold_right_app.
    simpl. clear Hl.
    induction l.
    + simpl. f_equal. lia.
    + simpl in * |- *.
      pose proof (Hr a (or_introl eq_refl)) as Hw.
      apply binom_mod_p_bound in Hw.
      rewrite
      Nat.pow_1_l, Nat.mul_1_r.
      remember
      ((fold_right (fun x0 acc : nat => acc + x0) 1
      (map (fun x0 : nat => binomial_exp p x0 * x ^ x0 * 1 ^ (p - x0)) l))) as t.
      rewrite <-Nat.Div0.add_mod_idemp_l.
      assert (Hv : (t + binomial_exp p a * x ^ a) mod p = 
        t mod p).
      rewrite <-Nat.Div0.add_mod_idemp_r,
      Nat.Div0.mul_mod, Hw.
      simpl.
      rewrite Nat.Div0.mod_0_l,
      Nat.add_0_r. reflexivity.
      rewrite Hv. 
      rewrite Nat.Div0.add_mod_idemp_l.
      apply IHl.
      intros y Hy. 
      apply Hr. right.
      exact Hy.
      exact Hp. 
      lia.
  Qed.



  Lemma fermat_little_simp : forall n p : nat, prime (Z.of_nat p) ->
    Nat.modulo (Nat.pow n p) p = Nat.modulo n p.
  Proof.
    induction n.
    - simpl; intros * Hp.
      apply prime_ge_2 in Hp.
      assert (Hz : 0 ^ p = 0).
      destruct p. lia. 
      destruct p. simpl.
      lia. simpl. lia.
      rewrite Hz. lia.
    - simpl; intros * Hp.
      pose proof prime_ge_2 (Z.of_nat p) Hp as Hpp.
      assert (Hs : S n = n + 1) by lia.
      rewrite Hs; clear Hs.
      rewrite prime_pow_exp.
      specialize (IHn p Hp).
      rewrite <-Nat.Div0.add_mod_idemp_l.
      rewrite IHn.
      rewrite Nat.Div0.add_mod_idemp_l.
      reflexivity.
      exact Hp.
  Qed.
      

  Lemma mod_div_same : forall p a b, 
    prime (Z.of_nat p) -> a <= b ->
    a mod p = b mod p <-> Nat.divide p (b - a).
  Proof.
    intros * Hp Hab; split; intros Ht.
    - exists ((b / p) - (a / p)).
      rewrite Nat.mul_comm, 
      Nat.mul_sub_distr_l.
      assert (Hpt : p <> 0).
      pose proof prime_ge_2 (Z.of_nat p) Hp as Hf.
      lia.
      rewrite (Nat.div_mod a p Hpt) at 1.
      rewrite (Nat.div_mod b p Hpt) at 1.
      lia.
    - destruct Ht as [z Hz].
      assert (b = a + z * p) by lia.
      assert (Hbb: b mod p = (a + z * p) mod p).
      congruence.
      rewrite Hbb.
      rewrite Nat.Div0.mod_add.
      reflexivity. 
  Qed.

  

  Lemma mod_simpl : forall a b p : nat, 
    prime (Z.of_nat p) -> 
    Nat.modulo a p <> 0 ->
    Nat.modulo (a * b) p = Nat.modulo a p ->
    Nat.modulo b p = 1.
  Proof.
    intros * Hp Ha Hab.
    assert (Hn : a <> 0).
    intros H. rewrite H in Ha.
    rewrite Nat.Div0.mod_0_l in Ha.
    lia. 
    assert (Ht : b <> 0).
    intro H. rewrite H in Hab.
    rewrite Nat.mul_comm in Hab.
    rewrite Nat.Div0.mod_0_l in Hab.
    lia. 
    assert (Hu : a <= a * b). 
    destruct a. lia.
    destruct b. lia.
    lia. symmetry in Hab.
    apply mod_div_same in Hab.
    assert(Hsimp: a * b - a = a * (b - 1)).
    rewrite Nat.mul_sub_distr_l.
    lia. rewrite Hsimp in Hab;
    clear Hsimp.
    apply prime_div_mul in Hab.
    destruct Hab as [Hab | Hab].
    apply connection_between_divide_and_mod in Hab.
    lia. exact Hp.
    apply connection_between_divide_and_mod in Hab.
    pose proof prime_ge_2 (Z.of_nat p) Hp as Hf.
    assert (Hadd :  (1 + (b - 1)) mod p = 1 mod p).
    rewrite <-Nat.Div0.add_mod_idemp_r.
    rewrite Hab, Nat.add_0_r.
    reflexivity.
    assert (Hbt : 1 + (b - 1) = b).
    lia. rewrite Hbt in Hadd.
    rewrite Nat.mod_1_l in Hadd.
    exact Hadd.
    lia. exact Hp.
    exact Hp. exact Hp.
    exact Hu.
  Qed.
    
  
  
  Theorem fermat_little_coprime : forall (a p : nat), 
    prime (Z.of_nat p) ->
    Nat.modulo a p <> 0 ->
    Nat.modulo (Nat.pow a (p - 1)) p = 1.
  Proof.
    intros * Hp Hn.
    pose proof prime_ge_2 (Z.of_nat p) Hp as Hf.
    assert (Hnp : a ^ p = a * a ^ (p - 1)).
    destruct p. lia.
    destruct p. lia.
    simpl. lia.
    pose proof fermat_little_simp a p Hp as Ha.
    rewrite Hnp in Ha.
    apply mod_simpl with (a := a).
    exact Hp.
    exact Hn.
    exact Ha.
  Qed.

 

  Theorem fermat_little_Z : forall (a : N) (p : N),
    prime (Z.of_N p) -> Z.modulo (Z.of_N a) (Z.of_N p) <> 0%Z ->
    Zpow_mod (Z.of_N a) (Z.of_N (p - 1)) (Z.of_N p) = 1%Z.
  Proof.
    intros * Hp Hna.
    rewrite <-zmod_nmod,
    <-npow_mod_exp_unary_binary_eqv.
    pose proof npow_mod_nat (N.to_nat (p - 1)) (N.to_nat a)  (N.to_nat p).
    pose proof prime_ge_2 (Z.of_N p) Hp as Hf.
    rewrite N_nat_Z in H.
    specialize (H Hp).
    repeat rewrite N2Nat.id in H.
    rewrite H.
    rewrite <-N2Nat.inj_pow,
    <-N2Nat.inj_mod,
    N2Nat.id.
    assert (Hz : Z.of_N 1 = 1%Z). lia.
    rewrite <-Hz.
    apply N2Z.inj_iff.
    rewrite N_to_nat_exp.
    pose proof fermat_little_coprime
    (N.to_nat a) (N.to_nat p) as Hc.
    rewrite N_nat_Z in Hc.
    specialize (Hc Hp).
    assert (Hnz : N.to_nat a mod N.to_nat p <> 0).
    intro Htf. apply Hna.
    rewrite <-N2Nat.inj_mod in Htf.
    rewrite <-N2Z.inj_mod. lia.
    specialize (Hc Hnz).
    assert (Hnt: (N.to_nat p - 1) = 
    (N.to_nat (p - 1))). lia.
    rewrite Hnt in Hc.
    rewrite Hc. lia.
    exact Hp.
    exact Hp.
    exact Hp.
  Qed.
   

End Fermat_Little_Theorem.    
    
   
