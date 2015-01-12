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

(* Record Notnot_Modality := Notnot {}. *)

Set Printing Universes.

Module Reflective_Subuniverse_base_case <: subuniverse_struct.

  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  (* Definition subu_family : Type2le@{a} := Notnot_Modality. *)

  Definition notnot (P:HProp@{i' i a}) : Type@{j} := not@{i i i} (not@{i i i} (pr1 P)).

  Instance _j (P:HProp@{i' i a}) : IsHProp (notnot@{i' i a j} P).
  repeat (refine trunc_forall; intro). Defined.


  Definition j (P:HProp@{i' i a}) : HProp@{j' j a} := existT (fun P => IsTrunc -1 P)
                                                       (notnot P) (@_j P).

  Instance _is_classical (P:HProp@{i' i a}) : IsHProp (pr1 (j@{i' i a j' j} P) -> pr1 P).
  apply (@trunc_forall _ _ (fun _ => P.1)). intro. exact (pr2 P). Defined.

  Definition is_classical (P:HProp@{i' i a}) : HProp@{j' j a}
    := existT (fun P => IsTrunc -1 P)
              (pr1 (j P) -> pr1 P ) (_is_classical (P:=P)).

  Definition n0 : trunc_index := -2.

  Definition n : trunc_index := -1.

  Definition subu_family := Unit : Type2le@{u a}.
  
  Definition subuniverse_HProp : forall (sf : subu_family@{u a}) (T:Trunk@{i' i a} n), HProp@{i' i a}.
    intros sf T.
    refine (exist _ ((j T).1 -> T.1) _).
  Defined.
  
  Definition O : forall (sf : subu_family@{u a}), Trunk@{i' i a} n -> Trunk@{i' i a} n
    := λ sf T, (j T).

  Definition subuniverse_O : forall (sf : subu_family@{u a}) (T:Trunk@{i' i a} n),
                                   (subuniverse_HProp@{u a i' i} sf (O@{u a i' i} sf T)).1.
    intros sf T.
    intros X X0.
    apply X.
    intros X1.
    unfold O in X1. simpl in X1. unfold notnot in X1. 
    apply X1. exact X0.
  Defined.
  
  Definition O_unit : forall (sf : subu_family@{u a}), forall T:Trunk@{i' i a} n, T.1 -> (O@{u a i' i} sf T).1.
    intros sf T x. simpl.
    unfold notnot. intro X. apply X. exact x.
  Defined.
  
  Definition O_equiv : forall (sf : subu_family@{u a}), forall (P : Trunk@{i' i a} n) (Q : Trunk@{j' j a} n) (modQ : (subuniverse_HProp@{u a j' j} sf Q).1),
                        IsEquiv@{i j} (fun f : (O@{u a i' i} sf P).1 -> Q.1 => f o (O_unit@{u a i' i} sf P)).
    intros sf P Q modQ.
    apply log_equiv_is_equiv.
    unfold O, j, notnot. simpl.
    refine (trunc_arrow _). exact (Q.2).
    refine (trunc_arrow _). exact Q.2.
    intros f jp. unfold subuniverse_HProp in modQ. simpl in modQ. apply modQ. intros notQ.
    unfold O, j, notnot in jp. simpl in jp. apply jp.
    intro p.
    exact (notQ (f p)).
  Defined.

End Reflective_Subuniverse_base_case.

Module Modality_base_case <: Modality Reflective_Subuniverse_base_case.
  
  Import Reflective_Subuniverse_base_case.
  
  Definition subu_sigma : forall sf:subu_family@{u a}, (forall (A:Trunk@{i' i a} n) (modA : (subuniverse_HProp@{u a i' i} sf A).1) (B:A.1 -> Trunk@{j' i a} n) (modB : forall a, (subuniverse_HProp@{u a j' i} sf (B a)).1), (subuniverse_HProp@{u a k' i} sf (({x:A.1 & (B x).1} ; trunc_sigma@{i i i' i} (A.2) (λ x, (B x).2)) : Trunk@{k' i a} n)).1).
    intros sf A modA B modB z.
    simpl in *.
    refine (exist _ _ _).
    { apply modA. unfold notnot in *.
      intro k.
      apply z. intro l.
      apply k.
      exact l.1. }

    { apply modB.
      unfold notnot in *.
      intro k. apply z. intro l. apply k.
      assert ((modA (λ k0 : ~ A.1, z (k0 o pr1))) = l.1).
      refine (path_ishprop _ _). exact A.2.
      apply (transport (λ U, (B U).1) X^).
      exact l.2. }
  Defined.


  Definition islex : forall sf:subu_family@{u a}, forall (A:Trunk@{i' i a} n), forall (x y:A.1),
                      Contr ((O@{u a i' i} sf A).1) -> Contr ((O@{u a i' i} sf (existT (IsTrunc n) (x = y) ((@istrunc_paths A.1 n (trunc_succ A.2) x y)))).1).
    intros sf A x y [c cc]. simpl in *.
    apply (contr_inhabited_hprop).
    apply hprop_allpath.
    intros p q.
    apply path_forall; intro u.
    destruct (p u).
    
    intro p. apply p. refine (path_ishprop x y). exact A.2.
  Defined.
  
End Modality_base_case.

Module HProp_sheaves (subU : subuniverse_struct) (mod : Modality subU).
  Import subU.
  Import mod.

  Definition subu_family_j := Reflective_Subuniverse_base_case.subu_family.
  Definition j := Reflective_Subuniverse_base_case.j.
  Definition subuniverse_HProp_j := Reflective_Subuniverse_base_case.subuniverse_HProp.
  Definition Oj := Reflective_Subuniverse_base_case.O.
  Definition Oj_unit := Reflective_Subuniverse_base_case.O_unit.
  Definition Oj_equiv := Reflective_Subuniverse_base_case.O_equiv.
  
  Module Import RS_Prop := Reflective_Subuniverse subU.
  (* Import Base_case. *)

  Definition fs := RS_Prop.fs.
  (* Context `{fs : Funext}. *)

  (* Definition sf := RS_Prop.sf. *)

  (* If T is a modal type, then [IsTrunc p T] is a HProp-sheaf *)
  Lemma is_classical_IsTrunc (sf:subu_family)
        (p: trunc_index)
        (j_is_subU : forall P, (j P).1 = (O sf (P.1; IsHProp_IsTrunc P.2 n0)).1)
        (j_is_subU_unit : forall P x ,
                            transport idmap (j_is_subU P) (Oj_unit tt P x) = O_unit sf (P.1; IsHProp_IsTrunc P.2 n0) x)
  : forall (T : subuniverse_Type sf), (subuniverse_HProp_j tt (existT (IsTrunc -1) (IsTrunc p T.1.1) (hprop_trunc _ _))).1.
    induction p.
    - intros T.
      pose (rew := j_is_subU (Contr (T.1).1; hprop_trunc (-2) (T.1).1)). simpl in *.
      rewrite rew; clear rew.
      intro X.
      refine (@contr_inhabited_hprop (T.1.1) _ _).
      apply hprop_allpath. intros x y.
      transparent assert (sheaf : (subuniverse_Type sf)).
      { refine (exist _ _ _).
        refine (exist _ (x=y) _).
        apply istrunc_paths. apply trunc_succ. exact T.1.2.
        apply subuniverse_paths. }
      revert X.
      apply (O_rec sf _ sheaf.1 sheaf.2).
      intros [c pc]. unfold sheaf. simpl.
      apply hprop_allpath.
      intros u v. exact ((pc u)^ @ (pc v)).

      revert X. apply O_rec. exact T.2.
      simpl.
      intros. exact (center _ X).
    - simpl in *. intros T X.
      unfold IsTrunc in *.
      intros x y.
      transparent assert (sheaf : (subuniverse_Type sf)).
      { refine (exist _ _ _).
        refine (exist _ (x=y) _).
        apply istrunc_paths. apply trunc_succ. exact T.1.2.
        apply subuniverse_paths. }
      specialize (IHp sheaf).
      unfold sheaf in *; clear sheaf. apply IHp.
      simpl in *.
      intros f.
      apply X. intro H.
      apply f.
      exact (H x y).
  Defined.
  
End HProp_sheaves.

