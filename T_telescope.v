(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import Limit.
Require Import T.

Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
Local Open Scope type_scope.

Section T_telescope.

  Context {X Y: Type} (f: X -> Y).

  Definition Ttelescope_aux (n: nat) : {T: Type & T -> Y}.
    induction n as [|n [U g]].
    - exists X. exact f.
    - exists (T g).
      refine (T_rec _ _ _ _). exact g.
      intros a b; exact idmap.
      intro a; reflexivity.
  Defined.

  Definition Ttelescope : diagram mappingtelescope_graph.
    refine (Build_diagram _ _ _).
    - intros n. exact (Ttelescope_aux n).1.
    - intros n m q; destruct q; simpl. apply t.
  Defined.

  Axiom Colimit_Ttelescope : IsSurjection f -> is_colimit Ttelescope Y.
  
End T_telescope.

