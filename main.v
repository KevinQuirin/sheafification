(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import PathGroupoid_ Forall_ Equivalences_ epi_mono reflective_subuniverse modalities.

Context (mod : forall i:trunc_index, Modality (trunc_S i)).

Let rs := λ i, underlying_subu _ (mod i).

Record NNModality := NN {uaNN: Univalence ; fsNN : Funext }.

Parameter (i0 : trunc_index).
Let i := trunc_S i0.


Module NNModality <: EasyModalities.

  Definition Modality : Type2@{u a}
    := NNModality.

  Definition O_reflector : Modality@{u a} -> Type@{i} -> Type@{i}
    := fun foo X => O (rs i0) (BuildTruncType i (Trunc i X)).

  Instance IsTrunc_O_reflector : forall foo X, IsTrunc i (O_reflector foo X).
  Proof.
    intros foo X.
    unfold O_reflector.
    apply istrunc_trunctype_type.
  Qed.

  Definition to (O : Modality@{u a}) (T : Type@{i})
  : T -> O_reflector O T.
  Proof.
    intro t; cbn.
    apply O_unit. apply tr. exact t.
  Defined.

  Definition O_indO (foo : Modality@{u a}) (A : Type@{i})
             (B : O_reflector foo A -> Type@{j})
    : (forall a : A, O_reflector foo (B (to foo A a))) ->
      forall z : O_reflector foo A, O_reflector foo (B z).
  Proof.
    pose (ua := uaNN foo).
    pose (fs := fsNN foo).
    intros f z.
    revert z.
    simple refine (O_rec_dep _ _ _).1.
    simple refine (Trunc_ind _ _).
    intro a; cbn.
    apply f.
  Defined.

  Definition O_indO_beta (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector O A -> Type@{j})
             (f : forall a, O_reflector O (B (to O A a))) (a:A)
    : O_indO O A B f (to O A a) = f a.
  Proof.
    Opaque O_rec_dep.
    unfold O_indO; cbn.
    match goal with
    |[|- ?ff.1 _ = _] => exact (ff.2 (tr a))
    end.
  Defined.

  Definition minO_pathsO (foo : Modality@{u a}) (A : Type@{i})
             (z z' : O_reflector foo A)
    : IsEquiv@{i i} (to foo (z = z')).
  Proof.
    pose (ua := uaNN foo).
    pose (fs := fsNN foo).
    unfold to.
    (* simple refine (isequiv_compose (f := tr) (g:= O_unit _ _)). *)

    simple refine (isequiv_adjointify _ _ _ _).
    -
      match goal with
      |[|- _ -> ?XX] => assert (IsSubu _ (rs i0) (BuildTruncType _ XX))
      end.
      simple refine (subuniverse_paths _ _ (Build_subuniverse_Type _ _ (BuildTruncType _ (O_reflector foo A)) _) z z').
      unfold O_reflector.
      match goal with
      |[|- IsSubu ?ii ?oo ?XX] => assert (@st _ _ (O (rs i0)
                         {|
                         trunctype_type := Trunc i A;
                         istrunc_trunctype_type := istrunc_truncation i A |}) = XX)
      end.
      apply path_trunctype. apply equiv_idmap.
      destruct X.
      apply subu_struct.
      simple refine (O_rec _ _ _ (Build_subuniverse_Type _ _ _ X) _).
      cbn. simple refine (Trunc_rec _).
      exact idmap.
    - cbn.
      match goal with
      |[|- Sect ?ff ?gg] => set (F := ff); set (G := gg)
      end.
      simple refine (O_rec_dep _ (λ u, Build_subuniverse_Type _ _ (BuildTruncType _ (G (F u) = u)) _) _).1.
      simple refine (Trunc_ind _ _).
      intro x; unfold F; clear F; unfold G; clear G; cbn.
      rewrite (λ P Q f, ap10 (O_rec_retr _ (rs i0) P Q f)).
      reflexivity.
    - intro u; cbn.
      rewrite (λ P Q f, ap10 (O_rec_retr _ (rs i0) P Q f)).
      reflexivity.
  Defined.

  Definition foo (A B:Type) (e e': Equiv A B)
    : {f:A -> B & f == e} <~> {g:A -> B & g == e'} -> e == e'.
  Proof.
    intros H x.
    pose (foo := (H (λ x, e x;λ x, idpath)).2 x).
    cbn in foo.
    etransitivity; try exact foo. clear foo.
    pose (foo := (H^-1 (λ x, e' x;λ x, idpath)).2 x).
    etransitivity; try exact foo^. clear foo.
    
End NNModality.
