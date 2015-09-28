(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import Limit.
Require Import T T_telescope.
Require Import Forall_ Equivalences_ epi_mono reflective_subuniverse modalities OPaths.
Require Import sheaf_base_case.
Require Import sheaf_def_and_thm.


Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
Local Open Scope type_scope.

Section Foo.

  Lemma foo (A B C:Type) (f:A -> C) (g: B -> C) (m:trunc_index) (TrC: IsTrunc m C)
  : Trunc m (Pullback f g)
          <~>
          Trunc m (Pullback (Trunc_rec f) (Trunc_rec g)).
  Proof.
    refine (equiv_adjointify _ _ _ _).
    - refine (Trunc_rec _).
      intros [a [b c]]. apply tr.
      exists (tr a). exists (tr b).
      exact c.
    - refine (Trunc_rec _).
      intros [a [b p]].
      revert p; revert b; revert a.
      refine (Trunc_ind _ _); intro a.
      refine (Trunc_ind _ _); intro b. intro p.
      apply tr. exact (a;(b;p)).
    - refine (Trunc_ind _ _).
      intros [a [b p]]. revert p; revert b; revert a.
      refine (Trunc_ind _ _). intro a.
      refine (Trunc_ind _ _). intro b. intro p.
      reflexivity.
    - refine (Trunc_ind _ _).
      intros [a [b p]].
      reflexivity.
  Defined.

End Foo.