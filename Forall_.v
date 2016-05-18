(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about dependent products *)

Require Import HoTT.Basics.
Require Import Types.Paths.

Local Open Scope path_scope.


Generalizable Variables A B f g e n.

Section AssumeFunext.
  Context `{Funext}.

  (** ** Composition *)
  Lemma path_forall_precompose (A B C:Type) (f:A -> B) (g h:B -> C) (eq:forall x, g x = h x)              
: ap (fun u => u o f) (path_forall g h eq) = path_forall (g o f) (h o f) (fun x => (eq (f x))).
  apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
  unfold path_forall at 2; rewrite eisretr.
  apply path_forall; intro a.
  pose (r:= @ap10_ap_precompose); unfold ap10 in r; rewrite r; clear r.
  unfold path_forall; rewrite eisretr. reflexivity.
  Qed.

  Lemma ap_path_forall_postcompose (A B C:Type) (f:B -> C) (g h:A -> B) (eq:forall x, g x = h x) 
: ap (fun u => f o u) (path_forall g h eq) = path_forall (f o g) (f o h) (fun x => ap f (eq x)).
  apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
  unfold path_forall at 2; rewrite eisretr.
  apply path_forall; intro a.
  pose (r:= @ap10_ap_postcompose); unfold ap10 in r; rewrite r; clear r.
  unfold path_forall; rewrite eisretr. reflexivity.
Qed.
End AssumeFunext.
