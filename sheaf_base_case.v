
Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import reflective_subuniverse modalities.

Set Universe Polymorphism.
Global Set Primitive Projections.
Set Implicit Arguments.

Local Open Scope path_scope.
Local Open Scope equiv_scope.
Local Open Scope type_scope.

(* Readability *)
Arguments trunc_arrow {H} {A} {B} {n} H0: simpl never.
Arguments trunc_sigma {A} {P} {n} H H0: simpl never.
Arguments istrunc_paths {A} {n} H x y: simpl never.

Section Reflective_Subuniverse_base_case.

  Context `{ua: Univalence}.
  Context `{fs: Funext}.
  
  Definition j (P:hProp) : hProp := BuildTruncType _ (~ ~P).
  Definition is_classical (P:hProp) : hProp := BuildTruncType _ ((j P) -> P).
  
  Definition Oj (P:hProp) : {P : hProp & is_classical P}.
    exists (j P). exact (λ X X0, X (λ X1, X1 X0)). Defined.
    
  Definition Oj_unit (P:hProp) : P -> (Oj P).1 := fun x k => k x.

  Definition Oj_equiv (P : TruncType -1) (Q : {T : TruncType -1 & is_classical T}) :
    (P -> Q.1) -> (Oj P).1 -> Q.1.
  Proof.
    intros f jp. apply (pr2 Q). intro notQ. unfold Oj in jp; simpl in jp.
    apply jp. intro p. exact (notQ (f p)).
  Defined.
  
  Definition subuniverse_Prop : subuniverse_struct -1.
  Proof.
    refine (Build_subuniverse_struct -1 is_classical Oj Oj_unit _).
    intros P Q.
    refine (isequiv_iff_hprop _ _).
    exact (Oj_equiv _).
  Defined.

  Definition modality_Prop : Modality -1.
    refine (Build_Modality _ subuniverse_Prop _).
    apply subuniverse_sigma. exact ua. exact fs.
    intros A B g; simpl in *.
    refine (exist _ _ _).
    intro z. apply (equiv_inv (IsEquiv := O_modal_equiv _ _ _)).
    Transparent O. cbn in *. Opaque O.
    intro nBz.
    apply z; intro a.
    specialize (g a).
    pose (f := Oj_unit ((B (Oj_unit A a))) g).
    unfold Oj in f; simpl in f.
    apply f.
    exact (transport (λ x, ~ (B x)) (path_ishprop (Oj_unit A a) z)^ nBz).

    intro a; simpl.
    refine (path_ishprop _ _).
  Defined.

  Definition islex_modality_Prop : IsLex modality_Prop.
    intros A x y [c cc]. simpl in *.
    apply (contr_inhabited_hprop).
    apply hprop_allpath.
    intros p q.
    apply path_forall; intro u.
    destruct (p u).
    Transparent O. cbn in *. Opaque O.
    intro p. apply p. refine (path_ishprop x y). 
  Defined.

End Reflective_Subuniverse_base_case.

Section Formalization.

  (** In this section is the proof of Proposition 23, base case of the induction *)

  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  Let OP := subuniverse_Prop.

  Let helper_trunc0 : forall (T:hSet), IsHSet (T -> subuniverse_Type OP).
  Proof.
    intro T. refine (trunc_arrow _).
    apply subuniverse_Type_is_TruncTypeSn.
    exact ua.
  Qed.             

  Let helper_trunc1 : forall (T:hSet) (u: T -> subuniverse_Type OP),
      IsHSet (O OP (BuildhProp (Trunc (-1) {a:T & u = (λ t, O OP (BuildhProp (a = t)))}))).
  Proof.
    intros T u.
    apply trunc_succ. auto with typeclass_instances.
  Qed.
  
  Definition O0 : hSet -> hSet
    := λ T:hSet, @BuildhSet ({u: T -> subuniverse_Type OP & O OP (BuildhProp (Trunc (-1) {a:T & u = (λ t, O OP (BuildhProp (a = t)))}))}) (trunc_sigma (helper_trunc0 T) (helper_trunc1 T)).

  Definition OP_to_O0 (P:hProp)
    : O OP P -> O0 (BuildhSet P).
  Proof.
    intro nnp. refine (exist _ _ _).
    intro p.
    refine (Build_subuniverse_Type _ _ (BuildhProp Unit) _).
    revert nnp; apply O_rec; intro p.
    apply O_unit, tr. exists p.
    apply path_forall; intro x. cbn in *.
    apply unique_subuniverse; apply path_trunctype; cbn.
    apply equiv_iff_hprop.
    intro tt; apply O_unit; apply path_ishprop.
    intro t; exact tt.
  Defined.

  Definition O0_to_OP (P:hProp)
    : O0 (BuildhSet P) -> O OP P.
  Proof.
    intros [u p].
    revert p; apply O_rec; apply Trunc_rec.
    intros [a q]. exact (O_unit OP P a).
  Defined.

  Definition equiv_OP_O0 (P:hProp)
    : O OP P <~> O0 (BuildhSet P).
  Proof.
    refine (equiv_iff_hprop (@OP_to_O0 P) (@O0_to_OP P)).
    (** Here should be the proof that [O0] defines a modality, combined with [hprop_stability] *)
  Admitted.
    
  
End Formalization.