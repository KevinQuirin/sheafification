Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import Forall_ Equivalences_ epi_mono reflective_subuniverse modalities.
Require Import nat_lemmas.
(* Require Import colimit. *)
(* Require Import VD_truncation gpd. *)
Require Import sheaf_base_case.
Require Import sheaf_def_and_thm.
Require Import Limit.

Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
(* Local Open Scope equiv_scope. *)
Local Open Scope type_scope.

(* Readability *)
Arguments trunc_arrow {H} {A} {B} {n} {H0}: simpl never.
Arguments trunc_sigma {A} {P} {n} {H H0}: simpl never.
Arguments trunc_forall {H} {A} {P} {n} {H0}: simpl never. 
Arguments istrunc_paths {A} {n} {H} x y: simpl never.
Arguments isequiv_functor_sigma {A P B Q} f {H} g {H0}: simpl never.
             
Section Foo.

  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  
  Local Definition n0 := sheaf_def_and_thm.n0.
  Local Definition n := sheaf_def_and_thm.n.
  Local Definition mod_nj := sheaf_def_and_thm.mod_nj.
  Local Definition nj := sheaf_def_and_thm.nj.
  Local Definition j_is_nj := sheaf_def_and_thm.j_is_nj.
  Local Definition j_is_nj_unit := sheaf_def_and_thm.j_is_nj_unit.
  Local Definition islex_mod_nj := sheaf_def_and_thm.islex_mod_nj.
  Local Definition islex_nj := sheaf_def_and_thm.islex_nj.
  Local Definition lex_compat := sheaf_def_and_thm.lex_compat.

  Definition BTT (T:Type) `{Tr: IsTrunc n T} := @BuildTruncType n T Tr.

  Definition T := Unit.


End Foo.