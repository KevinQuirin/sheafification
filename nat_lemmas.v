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
  Qed.

  Lemma ishset_nat : IsHSet nat.
    apply hset_decpaths. exact decidable_paths_nat.
  Defined.
  
End HSet_nat.

Section nat_interval.

  Fixpoint nat_interval (n:nat) : Type :=
    match n with
      |0 => Empty
      |S 0 => {p:nat & p = S 0}
      |S m => {p:nat & p = S m} + nat_interval m
    end.

  Definition nat_interval_to_nat (n:nat) : nat_interval n -> nat.
    induction n as [| m IH].
    - intros q; destruct q.
    - destruct m as [| p IH2].
      + intros q; exact q.1.
      + intros q. destruct q.
        * exact s.1.
        * exact (IH n).
  Defined.

  Global Coercion nat_interval_to_nat : nat_interval >-> nat.

  Lemma nat_interval_bounded (n:nat) : forall q:nat_interval n, q <= n.
    induction n as [| m IH].
    - intro q; destruct q.
    - induction m as [| p IH2].
      + intro q; simpl in q. destruct q as [q p]. simpl. destruct p. apply le_n.
      + intro q; destruct q. destruct s as [s k]. simpl. destruct k. apply le_n.
        specialize (IH n). auto.
  Qed.

  Lemma ishset_nat_interval (n:nat) : IsHSet (nat_interval n).
    induction n.
    - simpl. apply trunc_succ.
    - simpl.
      induction n.
      refine (trunc_sigma).
      exact ishset_nat.
      intro a. refine (trunc_succ).
      apply istrunc_paths. exact ishset_nat.


      pose (trunc_sum).
      specialize (i (minus_two)). simpl in i.
      specialize (i (∃ p : nat, p = n.+2)).
      assert ( IsTrunc 0 (∃ p : nat, p = n.+2)).
        refine trunc_sigma. exact ishset_nat.
        intro a. apply istrunc_paths. refine trunc_succ; exact ishset_nat.
      specialize (i X).
      specialize (i (nat_interval n.+1) IHn).
      (* exact i. *) admit.
  Qed.
End nat_interval.