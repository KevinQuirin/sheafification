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

End hPullback.

Section Old_pullback.

  Context `{ua : Univalence}.
  
  Definition char_hPullback'' (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (x:X)  : (hProduct Y n) ->  Trunk m.
    induction n.
    - simpl. intro tt.
      exists (tt=tt). apply istrunc_paths. apply trunc_unit.
    - simpl. intros [y pp]. exists (f y = x /\ (IHn pp).1).
      refine trunc_prod.
      exact (IHn pp).2.
  Defined.

  Definition char_hPullback' (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y)
  : (hProduct Y n) ->  Trunk m.
    induction n.
    - intro P. exists {P' : hProduct Y 0 & P = P'}.
      refine trunc_sigma.
    - intro P. exists {x:X & (char_hPullback'' m f (S n) TrX TrY x P).1}. simpl.
      abstract (destruct P as [y P]; simpl; rewrite (path_universe_uncurried (equiv_adjointify
          (λ X0 : ∃ x : X, f y = x ∧ (char_hPullback'' m f n TrX TrY x P).1,
           (λ (x : X)
            (proj2_sig : f y = x ∧ (char_hPullback'' m f n TrX TrY x P).1),
            (λ (p : f y = x) (q : (char_hPullback'' m f n TrX TrY x P).1),
             match
               p in (_ = y0)
               return
                 ((char_hPullback'' m f n TrX TrY y0 P).1
                  → (char_hPullback'' m f n TrX TrY (f y) P).1)
             with
             | 1 => idmap
             end q) (fst proj2_sig) (snd proj2_sig)) X0.1 X0.2)
          (λ x : (char_hPullback'' m f n TrX TrY (f y) P).1, (f y; (1, x)))
          (λ x : (char_hPullback'' m f n TrX TrY (f y) P).1, 1)
          (λ x : ∃ x : X, f y = x ∧ (char_hPullback'' m f n TrX TrY x P).1,
           (λ (x0 : X)
            (proj2_sig : f y = x0 ∧ (char_hPullback'' m f n TrX TrY x0 P).1),
            (λ (p : f y = x0) (q : (char_hPullback'' m f n TrX TrY x0 P).1),
             match
               p as p0 in (_ = y0)
               return
                 (∀ q0 : (char_hPullback'' m f n TrX TrY y0 P).1,
                  (f y;
                  (1,
                  match
                    p0 in (_ = y1)
                    return
                      ((char_hPullback'' m f n TrX TrY y1 P).1
                       → (char_hPullback'' m f n TrX TrY (f y) P).1)
                  with
                  | 1 => idmap
                  end q0)) = (y0; (p0, q0)))
             with
             | 1 => λ q0 : (char_hPullback'' m f n TrX TrY (f y) P).1, 1
             end q) (fst proj2_sig) (snd proj2_sig)) x.1 x.2))); exact (char_hPullback'' m f n TrX TrY (f y) P).2).
  Defined.

  Definition forget_char_hPullback'' (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (P : hProduct Y (S n)) (p: {p:nat & p <= n}) (x:X)
  : (char_hPullback'' m f (S n) TrX TrY x P).1 -> (char_hPullback'' m f n TrX TrY x (forget_hProduct Y n P p)).1.
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
        
  Definition forget_char_hPullback' (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (P:hProduct Y (S n)) (p : {p:nat & p <= n})
  : (char_hPullback' m f (S n) TrX TrY P).1 -> (char_hPullback' m f n TrX TrY (forget_hProduct Y n P p)).1.
    induction n.
    - simpl. intros. exact (tt;1).
    - intros [x a].
      exists x.
      apply forget_char_hPullback''. exact a.
  Defined.

  Definition hPullback' (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) : Type
    := {y : hProduct Y n & (char_hPullback' m f n TrX TrY y).1}.
  
  Lemma trunc_hPullback' (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y)
  : IsTrunc (trunc_S m) (hPullback' m f n TrX TrY).
    induction n.
    - refine trunc_sigma. 
    - refine trunc_sigma. apply trunc_hProduct. exact TrY.
      intros [y P]. simpl in *.
      assert ((∃ x : X, f y = x ∧ (char_hPullback'' m f n TrX TrY x P).1) <~> (char_hPullback'' m f n TrX TrY (f y) P).1).
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
        refine trunc_succ. exact (char_hPullback'' m f n TrX TrY (f y) P).2.
  Qed.

  Definition proj_pullback' (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (P : hPullback' m f n TrX TrY) : forall p:{p:nat & p < n}, Y.
    apply proj_hProduct. exact P.1.
  Defined.

  Definition forget_pullback' (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (P : hPullback' m f (S n) TrX TrY) : forall p:{p:nat & p <= n}, hPullback' m f n TrX TrY.
    intros p.
    exists (forget_hProduct Y n P.1 p).
    apply forget_char_hPullback'.
    exact P.2.
  Defined.

  Definition hPullback_into_product (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y)
  : hPullback' m f n TrX TrY -> hProduct Y n
    := pr1.

  Lemma char_hPullbacks_are_same (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) : char_hPullback m f n TrX TrY = char_hPullback' m f (S n) TrX TrY.
    apply path_forall; intros [y P]; simpl in P.
    simpl. apply truncn_unique; simpl.
    
    assert ((∃ x : X, f y = x ∧ (char_hPullback'' m f n TrX TrY x P).1) <~> (char_hPullback'' m f n TrX TrY (f y) P).1).
        refine (equiv_adjointify _ _ _ _).
        + intros [x [p q]].
          destruct p. exact q.
        + intros x.
          exists (f y).
          split; [reflexivity | exact x].
        + intros x. reflexivity.
        + intros [x [p q]].
          simpl. destruct p. reflexivity.
      + rewrite (path_universe_uncurried X0); clear X0.
        
    
        revert y. revert P. induction n.
        * intros P y. simpl in *.
          apply path_universe_uncurried.
          refine (equiv_adjointify (λ _, 1) (λ _, tt) _ _).
          intro x. apply path_ishprop.
          intro x. destruct x; reflexivity.
        * simpl. intros P y.
          destruct P as [y' P]. specialize (IHn P y'). simpl in *.
          apply path_universe_uncurried.
          refine (equiv_adjointify _ _ _ _).
          intros [p Q].
          split; try exact p^.
          destruct p. apply (equiv_path _ _ IHn Q).
          intros [p Q].
          split; try exact p^.
          destruct p. apply (equiv_path _ _ IHn^ Q).
          intros [p Q]. destruct p.
          simpl. apply path_prod; try reflexivity.
          simpl.
          rewrite transport_pV. reflexivity.
          intros [p Q]. destruct p.
          simpl. apply path_prod; try reflexivity.
          simpl. rewrite transport_Vp. reflexivity.
  Defined.

  Lemma hPullbacks_are_same (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) : hPullback m f n TrX TrY = hPullback' m f n TrX TrY.
    induction n.
    - unfold hPullback'. simpl.
      apply path_universe_uncurried.
      refine (equiv_adjointify (λ tt, (tt;(tt;1))) (λ _, tt) _ _).
      intros [tt [tt' p]]. destruct tt, tt', p. reflexivity.
      intro tt; destruct tt. reflexivity.
    - simpl. unfold hPullback'.
      apply path_universe_uncurried.
      refine (equiv_functor_sigma' _ _).
      simpl. exact (equiv_adjointify idmap idmap (λ _, 1) (λ _, 1)).
      intro a.
      apply equiv_path. simpl.
      pose (char_hPullbacks_are_same m f n TrX TrY).
      apply ap10 in p. specialize (p a). exact (p..1).
  Qed.

  Definition forget_hPullback (m:trunc_index) {X Y:Type} (f:Y -> X) (n:nat) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) (P : hPullback m f (S n) TrX TrY) : forall p:{p:nat & p <= n}, hPullback m f n TrX TrY.
    intro p.
    apply (equiv_path _ _ (hPullbacks_are_same m f n TrX TrY)).
    apply forget_pullback'.
    apply (equiv_path _ _ (hPullbacks_are_same m f (S n) TrX TrY)^).
    exact P.
    exact p.
  Defined.

End Old_pullback.

Section Cech_Nerve.
  
  Context `{ua: Univalence}.
  
  Definition Cech_nerve_graph : graph.
    refine (Build_graph _ _).
    exact nat.
    intros m n.
    exact ((m = S n) /\ (nat_interval m)).
  Defined.

  Definition Cech_nerve_diagram (m:trunc_index) {X Y:Type} (f: Y -> X) (TrX : IsTrunc (trunc_S m) X) (TrY : IsTrunc (trunc_S m) Y) : diagram (Cech_nerve_graph).
    refine (Build_diagram _ _ _).
    intro n.
    exact (hPullback m f (S n) TrX TrY).
    intros i j.
    intros [p q] a. destruct p.
    apply forget_hPullback.
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
