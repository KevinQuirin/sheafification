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


  Goal forall (Y:Type) (a b c d:Y), forget_hProduct Y 3 (a,(b,(c,(d,tt)))) ((S 0); (le_S 1 2 (le_S 1 1 (le_n 1)))) = (a,(c,(d,tt))).
    intros Y a b c d.
    simpl.
    reflexivity.
  Qed.
End hProduct.

Section hPullback.

  Context `{ua: Univalence}.


  Definition char_hPullback' (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (x:X)  : (hProduct Y n) ->  Trunk m.
    induction n.
    - simpl. intro tt.
      exists (tt=tt). apply istrunc_paths. apply trunc_unit.
    - simpl. intros [y pp]. exists (f y = x /\ (IHn pp).1).
      refine trunc_prod.
      exact (IHn pp).2.
  Defined.

  Definition char_hPullback (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y)
  : (hProduct Y n) ->  Trunk m.
    induction n.
    - intro P. exists {P' : hProduct Y 0 & P = P'}.
      refine trunc_sigma.
    - intro P. exists {x:X & (char_hPullback' m f (S n) TrX TrY x P).1}. simpl.
      destruct P as [y P]. simpl.
      assert ((∃ x : X, f y = x ∧ (char_hPullback' m f n TrX TrY x P).1) <~> (char_hPullback' m f n TrX TrY (f y) P).1).
        refine (equiv_adjointify _ _ _ _).
        + intros [x [p q]].
          destruct p. exact q.
        + intros x.
          exists (f y).
          split; [reflexivity | exact x].
        + intros x. reflexivity.
        + intros [x [p q]].
          simpl. destruct p. reflexivity.
      + rewrite (path_universe_uncurried X0).
        exact (char_hPullback' m f n TrX TrY (f y) P).2.
  Defined.

  Definition forget_char_hPullback' (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (P : hProduct Y (S n)) (p: {p:nat & p <= n}) (x:X)
  : (char_hPullback' m f (S n) TrX TrY x P).1 -> (char_hPullback' m f n TrX TrY x (forget_hProduct Y n P p)).1.
    induction n.
    - simpl in *. intros. reflexivity.
    - destruct p as [p H].
      induction p.
      + intros a. simpl in *.
        exact (snd a).
      + intros a. simpl. simpl in a.
        specialize (IHn (snd P) (p;le_pred _ _ H)).
        split; try exact (fst a).
        simpl in IHn.
        exact (IHn (snd a)).
  Defined.
        
  Definition forget_char_hPullback (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (P:hProduct Y (S n)) (p : {p:nat & p <= n})
  : (char_hPullback m f (S n) TrX TrY P).1 -> (char_hPullback m f n TrX TrY (forget_hProduct Y n P p)).1.
    induction n.
    - simpl. intros. exact (tt;1).
    - intros [x a].
      exists x.
      apply forget_char_hPullback'. exact a.
  Defined.

  Definition hPullback (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) : Type
    := {y : hProduct Y n & (char_hPullback m f n TrX TrY y).1}.
  
  Lemma trunc_hPullback (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y)
  : IsTrunc (trunc_S m) (hPullback m f n TrX TrY).
    induction n.
    - refine trunc_sigma. 
    - refine trunc_sigma. apply trunc_hProduct. exact TrY.
      intros [y P]. simpl in *.
      assert ((∃ x : X, f y = x ∧ (char_hPullback' m f n TrX TrY x P).1) <~> (char_hPullback' m f n TrX TrY (f y) P).1).
        refine (equiv_adjointify _ _ _ _).
        + intros [x [p q]].
          destruct p. exact q.
        + intros x.
          exists (f y).
          split; [reflexivity | exact x].
        + intros x. reflexivity.
        + intros [x [p q]].
          simpl. destruct p. reflexivity.
      + rewrite (path_universe_uncurried X0).
        refine trunc_succ. exact (char_hPullback' m f n TrX TrY (f y) P).2.
  Qed.


  Lemma test_pullback (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) : hPullback m f 2 TrX TrY <~> pullback f f.
    unfold hPullback, pullback. simpl.

    refine (equiv_adjointify _ _ _ _).
    - intros [[y1 [y2 tt]] [x [p [q r]]]]; simpl in *. 
      exists y1. exists y2. exact (p@q^).
    - intros [y1 [y2 p]].
      exists (y1,(y2,tt)).
      exists (f y1).
      simpl.
      exact (1,(p^,1)).
    - intros [y1 [y2 p]]. simpl. hott_simpl. 
    - intros [[y1 [y2 tt]] [x [p [q r]]]]; simpl in *. destruct tt. hott_simpl.
      apply path_sigma' with 1. simpl.
      destruct p, q.
      apply path_sigma' with 1. simpl.
      refine (path_prod _ _ _ _).
      reflexivity.
      refine (path_prod _ _ _ _).
      reflexivity.
      simpl.
      apply path_ishprop.
  Qed.

  Definition proj_pullback (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (P : hPullback m f n TrX TrY) : forall p:{p:nat & p < n}, Y.
    apply proj_hProduct. exact P.1.
  Defined.

  Definition forget_pullback (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (P : hPullback m f (S n) TrX TrY) : forall p:{p:nat & p <= n}, hPullback m f n TrX TrY.
    intros p.
    exists (forget_hProduct Y n P.1 p).
    apply forget_char_hPullback.
    exact P.2.
  Defined.

  Lemma one_pullback (m:trunc_index) {X Y:Type} (f:Y -> X) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y)
  : hPullback m f (S 0) TrX TrY <~> Y.
    refine (equiv_adjointify _ _ _ _).
    - intros [[y tt] [x [q r]]]. exact y.
    - intro y. exists (y,tt). exists (f y). exact (1,1).
    - intro y. reflexivity.
    - intros [[y tt] [x [q r]]]. destruct tt. simpl in *.
      destruct q.
      simpl.
      repeat apply path_sigma' with 1. simpl.
      apply path_prod; [exact 1 | apply path_ishprop].
  Qed.

  Definition hPullback_into_product (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y)
  : hPullback m f n TrX TrY -> hProduct Y n
    := pr1.    
End hPullback.

Section Cech_Nerve.
  
  Context `{ua: Univalence}.
  
  Definition Cech_nerve_graph {X Y:Type} (f: Y -> X) : graph.
    refine (Build_graph _ _).
    exact nat.
    intros m n.
    exact ((m = S n) /\ (nat_interval m)).
  Defined.

  Definition Cech_nerve_diagram (m:trunc_index) {X Y:Type} (f: Y -> X) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) : diagram (Cech_nerve_graph f).
    refine (Build_diagram _ _ _).
    intro n.
    exact (hPullback m f (S n) TrX TrY).
    intros i j; simpl in *.
    intros [p q] a. destruct p.
    apply forget_pullback.
    exact a.
    exists (nat_interval_to_nat i q).
    abstract (apply (nat_interval_bounded i q)).
  Defined.

  Axiom GiraudAxiom : forall (m:trunc_index) {X Y:Type} (f : Y -> X) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (issurj_f : IsSurjection f), colimit (Cech_nerve_diagram m f TrX TrY) <~> X.

  Lemma trunc_cech_nerve (m:trunc_index) {X Y:Type} (f : Y -> X) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (issurj_f : IsSurjection f)
  : IsTrunc (m.+1) (colimit (Cech_nerve_diagram m f TrX  TrY)).
    pose (GiraudAxiom m f TrX TrY issurj_f).
    apply path_universe_uncurried in e.
    rewrite e.
    exact TrX.
  Qed.

  
End Cech_Nerve.