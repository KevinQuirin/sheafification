Require Import Utf8_core.
Require Import HoTT.
Require Import Peano.

Set Universe Polymorphism.
Global Set Primitive Projections.

Local Open Scope path_scope.

Section Lemmas.

  Fixpoint IsSucc (n:nat) : Type :=
    match n with
      |0 => Empty
      |_ => Unit
    end.

  Lemma not_lt_0 (n:nat) : ~(n < 0).
    unfold lt; intros H.
    change (IsSucc 0). elim H. exact tt.
    intros m p HH. exact tt.
  Defined.

  Lemma le_succ (n m:nat) : (m <= n) -> (S m <= S n).
    intro H.
    induction H.
    auto. auto.
  Qed.

  Lemma eq_S (n m:nat) : (S m = S n) -> m = n.
    intro p.
    assert (X : m = pred (S m)) by auto. rewrite X; clear X.
    assert (X : n = pred (S n)) by auto. rewrite X; clear X.
    destruct p. reflexivity.
  Qed.

  Fixpoint binomial (n k:nat) : nat :=
    match n,k with
      | 0,0 => 1
      | 0,_ => 0
      | S m,0 => 1
      | S m, S l => (binomial m l) + (binomial m (S l))
    end.

      
    Lemma neq_symm (n m:nat) : (n <> m) -> (m <> n).
      intro H. intro x. destruct x. destruct H. reflexivity.
    Qed.

    Lemma le_neq_lt (n m :nat) : (n <> m) -> (n <= m) -> (n < m).
      intros H H'.
      induction H'.
      - destruct H. reflexivity.
      - unfold lt. apply le_succ. exact H'.
    Qed.
      
    Lemma neq_0_succ (n:nat) : (n <> 0) -> {m : nat & S m = n}.
      induction n.
      - intros H; destruct H. reflexivity.
      - intros H. exists n. reflexivity.
    Qed.

    Lemma gt_0_succ (n:nat) : (0 < n) -> {m : nat & S m = n}.
      induction n.
      - intro H. destruct H. exists 0; reflexivity.
        exists m; reflexivity.
      - intro H.
        exists n; reflexivity.
    Qed.

    Lemma ge_succ_succ (m:nat) : forall n, (S m <= n) -> {k : nat & S k = n}.
      intros n p.
      induction p.
      - exists m; reflexivity.
      - exists m0. reflexivity.
    Qed.

    Definition succ_not_0 (n:nat) : 0 <> S n
      := fun H => (λ H0 : S n = S n → Empty, H0 idpath)
                    match H in (_ = y) return (y = S n → Empty) with
                      | idpath => paths_ind 0 (λ (e : nat) _ , match e with
                                                                 | 0 => Unit
                                                                 | S _ => Empty
                                                               end) tt (S n)
                    end.

    Lemma le_0_is_0 (n:nat) : n <= 0 -> n = 0.
      induction n.
      - auto.
      - intro H. destruct (not_lt_0 n H).
    Qed.

    Lemma le_1_is_01 (n:nat) : n <= 1 -> (n=0) + (n=1%nat).
      induction n.
      { intro H. apply inl; reflexivity. }
      { intro H. apply le_pred in H. simpl in H.
        apply inr.
        apply ap. apply le_0_is_0. exact H. }
    Qed.  

    Lemma le_0 (n:nat) : 0 <= n.
      induction n.
      - apply le_n.
      - apply le_S. exact IHn.
    Qed.

    Lemma not_le_S (n:nat) : ~ (S n <= n).
      induction n.
      - intro H. destruct (not_lt_0 0 H).
      - intro H. apply IHn. apply le_pred in H; exact H.
    Qed.
        
End Lemmas.

Section HSet_nat.

  Lemma decidable_paths_nat : DecidablePaths nat.
    intros n; induction n.
    intro m; induction m.
    left; auto.
    right. intro H.
    exact (transport (fun n => match n with 0 => Unit |S _ => Empty end) H tt).
    intro m; induction m.
    right. intro H.
    exact (transport (fun n => match n with 0 => Empty | S _ => Unit end) H tt).
    destruct (IHn m) as [p | e].
    left. destruct p; reflexivity.
    right. intro H. apply e.
    apply eq_S. exact H.
  Defined.

  Lemma ishset_nat : IsHSet nat.
    apply hset_decpaths. exact decidable_paths_nat.
  Defined.

  Lemma decidable_le : forall (n m:nat), (n <= m) + ~(n <= m).
    intros n m.
    induction n, m.
    - left. apply le_n.
    - left. apply le_0.
    - destruct IHn.
      + right. intro H. destruct (not_lt_0 n H).
      + right. intro H. destruct (not_lt_0 n H).
    - destruct IHn.
      + destruct (decidable_paths_nat n (S m)).
        * destruct p.
          right.
          intro H. apply (not_le_S n H).
        * left. exact (le_neq_lt n (S m) n0 l).
      + destruct (decidable_paths_nat (S n) (S m)).
        * destruct p. left. apply le_n.
        * right. intro H. apply n0.
          apply le_S. apply le_pred in H; exact H.
  Qed.

  (* Adapted from https://coq.inria.fr/files/interval_discr.v *)
  Lemma IsHProp_le : forall (n m : nat), IsHProp (n <= m).
    intros n m.
    apply hprop_allpath.
    induction x; intro q.
    - path_via (transport (fun n0 => n <= n0) 1 (le_n n)). 
      generalize (idpath n).
      case q.
      { intro p.
        assert (1=p) by apply path_ishprop. destruct X. reflexivity. }
      { intros m l e.
        destruct e^.
        destruct (not_le_S _ l). }
    - path_via (transport (fun n0 => n <= n0) 1 (le_S n m x)).
      generalize (idpath (S m)).
      case q.
      { intros Heq.
        destruct Heq. destruct (not_le_S _ x). }
      { intros m0 l HeqS.
        assert (X:{Heq : m = m0 & ap S Heq = HeqS}).
        exists (ap pred HeqS). apply path_ishprop.
        destruct X as [Heq pp].
        destruct pp. destruct Heq.
        simpl.
        apply ap. apply IHx. }
  Qed.

End HSet_nat.

Section nat_interval.

  Definition nat_interval (n:nat) : Type :=
    {p: nat & p <= n}.
    
  Definition nat_interval_to_nat (n:nat) : nat_interval n -> nat.
    exact pr1.
  Defined.

  Global Coercion nat_interval_to_nat : nat_interval >-> nat.

  Lemma nat_interval_bounded (n:nat) : forall q:nat_interval n, q <= n.
    exact pr2.
  Qed.

End nat_interval.
