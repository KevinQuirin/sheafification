(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

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

