Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import colimit.
Require Import Peano.
Require Import nat_lemmas.
Require Import sub_object_classifier equivalence.

Set Universe Polymorphism.
Global Set Primitive Projections.
(* Set Implicit Arguments. *)

Local Open Scope path_scope.
Local Open Scope equiv_scope.
Local Open Scope type_scope.

Lemma trunc_unit (m:trunc_index) : IsTrunc m Unit.
  induction m.
  exact contr_unit.
  apply trunc_succ.
Qed.

Section hProduct.

  Fixpoint hProduct (Y:Type) (n:nat) : Type :=
    match n with
      |0 => Unit
      |S m => Y /\ (hProduct Y m)
    end.

  Lemma trunc_hProduct (m:trunc_index) (Y:Type) (n:nat)
  : IsTrunc m Y -> IsTrunc m (hProduct Y n).
    intro TrY.
    induction n.
    - exact (trunc_unit m).
    - apply trunc_prod.
  Qed.

  Definition proj_hProduct (Y:Type) (n:nat) (P:hProduct Y n) : {p:nat & p < n} -> Y.
    induction n.
    - intros [p H]. apply not_lt_0 in H. destruct H.
    - intros [p H]. simpl in P.
      induction p.
      + exact (fst P).
      + apply le_pred in H. simpl in H.
        exact (IHn (snd P) (p;H)).
  Defined.

  Definition forget_hProduct (Y:Type) (n:nat) (P:hProduct Y (S n)) : {p:nat & p <= n} -> hProduct Y n.
    induction n.
    - intros [p H]. exact tt.
    - intros [p H]. simpl in P.
      induction p.
      + simpl. exact (fst (snd P), snd (snd P)).
      + apply le_pred in H. simpl in H.
        exact (fst P, (IHn (fst (snd P),snd (snd P)) (p;H))).
  Defined.
End hProduct.

Section hPullback.
  Context `{ua: Univalence}.
  
  Definition char_hPullback (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (P : hProduct Y (S n))
  : Trunk m.
    induction n.
    - exists Unit. apply trunc_unit.
    - simpl in P.
      exists ((f (fst P) = f (fst (snd P))) /\ (IHn (snd P)).1).
      refine trunc_prod.
      exact (IHn (snd P)).2.
  Defined.
  
  Definition char_hPullback_inv (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (P : hProduct Y (S n))
  : Trunk m.
    induction n.
    - exists Unit. apply trunc_unit.
    - simpl in P.
      exists ((IHn (snd P)).1 /\ (f (fst P) = f (fst (snd P)))).
      refine trunc_prod.
      exact (IHn (snd P)).2.
  Defined.
  
  Definition forget_char_hPullback (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat)
             (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y)
             (x : hProduct Y (S (S n)))
             (P : (char_hPullback m f (S n) TrX TrY x).1)
  : forall p:{p:nat & p <= n.+1}, (char_hPullback m f n TrX TrY (forget_hProduct Y (S n) x p)).1.
    intros [p Hp].
    induction (decidable_paths_nat 0 p) as [| a].
    { destruct a. simpl in *.
      exact (snd P). }
    
    induction (decidable_paths_nat (S n) p) as [| b].
    { destruct a0. simpl in *.
      induction n.
      simpl in *. exact tt.
      simpl in *.
      split. exact (fst P).
      apply IHn. exact (snd P).
      apply succ_not_0. }
    
    apply neq_symm in a.
    apply neq_0_succ in a.
    destruct a as [p' Hp'].
    destruct Hp'. 
    assert (l := le_neq_lt _ _ (neq_symm _ _ b) Hp).
    assert (l0 := le_pred _ _ l). simpl in l0. clear b l. simpl in *. destruct P as [P PP].
    generalize dependent n. generalize dependent p'. induction p'; intros.
    - simpl in *.
      assert (k := gt_0_succ n l0); destruct k as [k Hk]. destruct Hk. simpl in *.
      split.
      exact (P@ (fst PP)).
      exact (snd PP).
    - simpl in *.
      assert (n' := ge_succ_succ (S p') _ l0).
      destruct n' as [n' Hn']. destruct Hn'. simpl in PP. destruct PP as [PP PPP].
      specialize (IHp' n' (snd x) PP PPP). simpl. split.
      exact P.
      apply IHp'.
      exact (le_pred _ _ l0).
  Defined.

  (* Definition 7*)
  Definition hPullback (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y)
  : Type.
    induction n.
    - exact Unit.
    - exact {P : hProduct Y (S n) & (char_hPullback m f n TrX TrY P).1}.
  Defined.

  Lemma trunc_hPullback (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y)
  : IsTrunc (trunc_S m) (hPullback m f n TrX TrY).
    induction n.
    - apply trunc_unit.
    - simpl. refine trunc_sigma. refine trunc_prod.
      apply trunc_hProduct. assumption.
      intro a. refine trunc_succ. exact (char_hPullback m f n TrX TrY a).2.
  Qed.

  Definition proj_pullback (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (P : hPullback m f n TrX TrY) : forall p:{p:nat & p < n}, Y.
    apply proj_hProduct.
    induction n. exact P. simpl in *. exact P.1.
  Defined.

  (* This defines the canonical projections between the n+1-pullback of X to the n-pullback of X*)
  Definition forget_hPullback (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (P : hPullback m f (S n) TrX TrY) : forall p:{p:nat & p <= n}, hPullback m f n TrX TrY.
    intros [p Hp].
    induction n. exact tt.
    exists (forget_hProduct Y (S n) P.1 (p;Hp)).
    apply forget_char_hPullback.
    exact P.2.
  Defined.

End hPullback.

Section Cech_Nerve.
  
  Context `{ua: Univalence}.

  (* Definition 8*)
  Definition Cech_nerve_graph : graph.
    refine (Build_graph _ _).
    exact nat.
    intros m n.
    exact ((S n = m) /\ (nat_interval m)).
  Defined.

  Definition Cech_nerve_diagram (m:trunc_index) {X Y:Type} (f: Y -> X) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) : diagram (Cech_nerve_graph).
    refine (Build_diagram _ _ _).
    intro n.
    exact (hPullback m f (S n) TrX TrY).
    intros i j. 
    intros [p q] a.
    destruct p.
    apply forget_hPullback.
    exact a.
    exact q.
  Defined.

  Definition Cech_nerve_commute (m:trunc_index) {X Y:Type} (f: Y -> X) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y)
  : forall i, (Cech_nerve_diagram m f TrX TrY) i -> X.
    intro i. simpl. intro P.
    exact (f (fst P.1)).
  Defined.

  Definition Cech_nerve_pp (m:trunc_index) {X Y:Type} (f: Y -> X) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y)
  : forall i j, forall (g : Cech_nerve_graph i j), forall (x : (Cech_nerve_diagram m f TrX TrY) i),
      (Cech_nerve_commute m f TrX TrY) _ (diagram1 (Cech_nerve_diagram m f TrX TrY) g x) = (Cech_nerve_commute m f TrX TrY) _ x.
    intros i j g x. simpl in *.
    unfold Cech_nerve_commute. simpl.
    destruct g as [p [q Hq]]. destruct p. simpl.
    destruct q; [exact (fst (x.2))^ | reflexivity].
  Defined.

  (* Axiom 9*)
  Axiom Giraud : forall (m:trunc_index) {X Y:Type} (f : Y -> X) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (issurj_f : IsSurjection f),
                   is_colimit (Cech_nerve_graph)
                              (Cech_nerve_diagram m f TrX TrY)
                              X
                              (Cech_nerve_commute m f TrX TrY)
                              (Cech_nerve_pp m f TrX TrY).
  
  Axiom GiraudAxiom : forall (m:trunc_index) {X Y:Type} (f : Y -> X) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (issurj_f : IsSurjection f), colimit (Cech_nerve_diagram m f TrX TrY) <~> X.

  Lemma trunc_cech_nerve (m:trunc_index) {X Y:Type} (f : Y -> X) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (issurj_f : IsSurjection f)
  : IsTrunc (m.+1) (colimit (Cech_nerve_diagram m f TrX  TrY)).
    pose (e := GiraudAxiom m f TrX TrY issurj_f).
    apply path_universe_uncurried in e.
    rewrite e.
    exact TrX.
  Qed.
  
End Cech_Nerve.
