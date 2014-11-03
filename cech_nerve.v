Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
(* Require Import lemmas epi_mono equivalence truncation univalence sub_object_classifier limit_colimit modalities. *)
(* Require Import sheaf_base_case. *)
Require Import colimit.
Require Import Peano.
Require Import nat_lemmas.


Set Universe Polymorphism.
Global Set Primitive Projections.
(* Set Implicit Arguments. *)

Local Open Scope path_scope.
Local Open Scope equiv_scope.
Local Open Scope type_scope.

Context `{ua: Univalence}.
Context `{fs: Funext}.

Section hPullback.

  Generalizable Variables X Y. 
  Generalizable Variable f.
      
  Fixpoint hPullback' {X Y:Type} (f:Y -> X) (n:nat) (x:X) : Type :=
    match n with
      |0 => Unit
      (* |S 0 => {y:Y & f y = x} *)
      |S m => {yy' : Y * (hPullback' f m x) & f (fst yy') = x}
    end.

  Definition hPullback {X Y:Type} (f:Y -> X) (n:nat) : Type := {x:X & hPullback' f n x}.


  Lemma trunc_unit (m:trunc_index) : IsTrunc m Unit.
    induction m.
    exact contr_unit.
    apply trunc_succ.
  Qed.
  
  Lemma trunc_hPullback' (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat)
  : IsTrunc m Y -> IsTrunc m X -> forall x, IsTrunc m (hPullback' f n x).
    intros TrY TrX x.
    induction n.
    - exact (trunc_unit m).
    - refine trunc_sigma.
  Qed.

  Lemma trunc_hPullback (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat)
  : IsTrunc m Y -> IsTrunc m X -> IsTrunc m (hPullback f n).
    intros TrY TrX.
    refine trunc_sigma.
    intro a. apply (trunc_hPullback' m f n TrY TrX a).
  Qed.

  Lemma test_pullback {X Y:Type} (f:Y -> X) : hPullback f 2 <~> pullback f f.
    unfold hPullback, hPullback', pullback. simpl.

    refine (equiv_adjointify _ _ _ _).
    - intros [x [[y [[y' tt] q]] p]]. simpl in *.
      exists y. exists y'. exact (p@q^).
    - intros [y [y' p]].
      exists (f y).
      exists (y,((y',tt);p^)).
      reflexivity.
    - intros [y [y' p]]. simpl.
      hott_simpl.
    - intros [x [[y [[y' tt] q]] p]]. simpl in *.
      destruct p. destruct tt.
      hott_simpl. 
  Qed.

  Definition proj_pullback {X Y:Type} (f:Y -> X) (n:nat) (P : hPullback f n) : forall p:{p:nat & p < n}, Y.
    induction n.
    - intros [p H]. apply not_lt_0 in H. destruct H.
    - destruct P as [x [[y y'] q]]. simpl in *.
      intros [p H].
      induction p.
      * exact y.
      * apply le_pred in H; simpl in H.
        pose (Q := (x;y') : hPullback f n).
        exact (IHn (x;y') (p;H)).
  Defined.

  Definition forget_pullback {X Y:Type} (f:Y -> X) (n:nat) (P:hPullback f (S n)) : forall p:{p:nat & p < S n}, hPullback f n.
    intros p. exists P.1.
    revert p.
    induction n.
    - intros [p H]; simpl in *. exact tt.
    - intros [p H].
      destruct P as [x [[y1 y'] q]].  
      induction p.
      + destruct y' as [[y2 y'] r]. exists (y2,y'). exact r.
      + simpl.
        apply le_pred in H. simpl in H.
        specialize (IHn (x;y') (p;H)). simpl in IHn.
        exists (y1,IHn).
        exact q.
  Defined.

  Lemma one_pullback {X Y:Type} (f:Y -> X)
  : hPullback f (S 0) <~> Y.
    transparent assert (ff: (hPullback f 1 -> Y)).
    { intros [x [[y tt] p]].
      simpl in *. 
      exact y. }
    transparent assert (gg : (Y -> hPullback f 1)).
    { intro y. exists (f y).
      exists (y,tt).
      reflexivity. }
    refine (equiv_adjointify ff gg _ _).
    - intro x. unfold ff, gg. 
      reflexivity.
    - intros [x [[y tt] p]]. unfold ff, gg.
      simpl in *.
      destruct p, tt.
      reflexivity.
  Qed.

End hPullback.

Section Cech_Nerve.
  
  Definition Cech_nerve_graph {X Y:Type} (f: Y -> X) : graph.
    refine (Build_graph _ _).
    exact nat.
    intros m n.
    exact ((m = S n) /\ (nat_interval m)).
  Defined.

  Definition Cech_nerve_diagram {X Y:Type} (f: Y -> X) : diagram (Cech_nerve_graph f).
    refine (Build_diagram _ _ _).
    intro n.
    exact (hPullback f (S n)).
    intros i j; simpl in *.
    intros [p q] a. destruct p.
    apply forget_pullback.
    exact a.
    exists (nat_interval_to_nat i q).
    abstract (unfold lt; apply le_succ; apply (nat_interval_bounded i q)).
  Defined.

  Axiom GiraudAxiom : forall {X Y:Type} (f : Y -> X) (issurj_f : IsSurjection f), colimit (Cech_nerve_diagram f) <~> X.

  Lemma istrunc_cech_nerve {X Y:Type} (f : Y -> X) (m:trunc_index) (TrX : IsTrunc m X) (TrY : IsTrunc m Y) (issurj_f : IsSurjection f)
  : IsTrunc m (colimit (Cech_nerve_diagram f)).
    pose (GiraudAxiom f issurj_f).
    apply path_universe_uncurried in e.
    rewrite e.
    exact TrX.
  Qed.

  
End Cech_Nerve.