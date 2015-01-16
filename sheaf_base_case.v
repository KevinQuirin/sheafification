Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import equivalence univalence sub_object_classifier reflective_subuniverse modalities.

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
Arguments truncn_unique _ {n} A B H: simpl never.

Section Reflective_Subuniverse_base_case.

  Context `{ua: Univalence}.
  Context `{fs: Funext}.
  
  Instance _j (P:HProp) : IsHProp (not (not (pr1 P))).
  repeat (apply trunc_forall; intro). Defined.

  Definition j (P:HProp) := (not (not (pr1 P));_j _).

  Instance _is_classical (P:HProp) : IsHProp (pr1 (j P) -> pr1 P).
  apply (@trunc_forall _ _ (fun _ => P.1)). intro. exact (pr2 P). Defined.  
  
  Definition is_classical (P:HProp) := (pr1 (j P) -> pr1 P ; _is_classical (P:=P)).

  Definition Oj (P:HProp) : {P : HProp & pr1 (is_classical P)}.
    exists (j P). exact (λ X X0, X (λ X1, X1 X0)). Defined.
    
  Definition Oj_unit (P:HProp) : pr1 P -> pr1 (pr1 (Oj P)) := fun x k => k x.

  Definition Oj_equiv (P : Trunk -1) (Q : {T : Trunk -1 & pr1 (is_classical T)}) :
      (pr1 P -> pr1 (pr1 Q)) -> pr1 (pr1 (Oj P)) -> pr1 (pr1 Q).
    intros f jp. apply (pr2 Q). intro notQ. unfold Oj in jp; simpl in jp. apply jp. intro p. exact (notQ (f p)). Defined.
  
  Definition subuniverse_Prop : subuniverse_struct -1.
    apply (Build_subuniverse_struct is_classical Oj Oj_unit). 
    intros. eapply log_equiv_is_equiv.
    apply (@trunc_forall _ _ (fun P => _)); intro. exact Q.1.2.
    apply (@trunc_forall _ _ (fun P => _)); intro. exact Q.1.2.
    exact (Oj_equiv _).
  Defined.

  Definition modality_Prop : Modality -1.
    refine (Build_Modality _ subuniverse_Prop _).
    apply subuniverse_sigma. exact ua. exact fs.
    intros A B g; simpl in *.
    refine (exist _ _ _).
    intro z. apply (equiv_inv (IsEquiv := O_modal_equiv _)).
    intro nBz.
    apply z; intro a.
    specialize (g a).
    pose (f := Oj_unit ((B (Oj_unit A a)).1) g).
    unfold Oj in f; simpl in f.
    apply f.
    exact (transport (λ x, ~ (B x).1.1) (path_ishprop (Oj_unit A a) z)^ nBz).

    intro a; simpl.
    refine (path_ishprop _ _).
    exact ((B (Oj_unit A a)).1).2.
  Defined.

  Definition islex_modality_Prop : IsLex modality_Prop.
    intros A x y [c cc]. simpl in *.
    apply (contr_inhabited_hprop).
    apply hprop_allpath.
    intros p q.
    apply path_forall; intro u.
    destruct (p u).

    intro p. apply p. refine (path_ishprop x y). exact A.2.
  Defined.

End Reflective_Subuniverse_base_case.

