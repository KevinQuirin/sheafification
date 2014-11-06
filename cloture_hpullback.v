Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import colimit.
Require Import Peano.
Require Import nat_lemmas.
Require Import cech_nerve.
Require Import equivalence sub_object_classifier modalities.
Require Import sheaf_def_and_thm.


Set Universe Polymorphism.
Global Set Primitive Projections.
(* Set Implicit Arguments. *)

Local Open Scope path_scope.
Local Open Scope equiv_scope.
Local Open Scope type_scope.

(* Readability *)
Arguments trunc_arrow {H} {A} {B} {n} H0: simpl never.
Arguments trunc_sigma {A} {P} {n} H H0: simpl never.
Arguments istrunc_paths {A} {n} H x y: simpl never.
Arguments truncn_unique _ {n} A B H: simpl never.


Definition n0 := sheaf_def_and_thm.n0.
Definition n := sheaf_def_and_thm.n.
Definition nj := sheaf_def_and_thm.nj.
Definition j_is_nj := sheaf_def_and_thm.j_is_nj.
Definition j_is_nj_unit := sheaf_def_and_thm.j_is_nj_unit.
Definition islex_nj := sheaf_def_and_thm.islex_nj.
Definition lex_compat := sheaf_def_and_thm.lex_compat.

Section Cloture_hPullback.
  
Context `{ua: Univalence}.
Context `{fs: Funext}.

Fixpoint _cl_hPullback' {X Y:Trunk n} (f:Y.1 -> X.1) (k:nat) (x:X.1) : Type :=
  match k with
    |0 => Unit
    (* |S 0 => {y:Y & f y = x} *)
    |S m => {yy' : Y.1 * (_cl_hPullback' f m x) & (nj.(O) (f (fst yy') = x ; @trunc_succ n0 _ (@istrunc_paths _ n0 X.2 _ _))).1.1}
  end.

Definition _cl_hPullback {X Y:Trunk n} (f:Y.1 -> X.1) (k:nat) : Type := {x:X.1 & _cl_hPullback' f k x}.

Definition cl_hPullback {X Y:Trunk n} (f:Y.1 -> X.1) (k:nat) : Type
  := (cloture' (subobject_hPullback_into_product n f k X.2 Y.2)).1.

Lemma _cl_cl_hPullback {X Y:Trunk n} (f:Y.1 -> X.1) (k:nat)
: _cl_hPullback f k <~> cl_hPullback f k.
Admitted.

Definition cl_hPullback_proj {X Y:Trunk n} (f:Y.1 -> X.1) (k:nat)
: cl_hPullback f (S k) -> forall p:{p:nat & p < S k}, cl_hPullback f k.
  induction k.
  - intros x [p q].
    unfold cl_hPullback, cloture', cloture, nchar_to_sub, nsub_to_char, subobject_hPullback_into_product, compose in *; simpl in *.
    exists tt.
    destruct x as [[y tt] x]; destruct tt; simpl in *.
    revert x. apply O_rec. intro x; simpl in x.
    apply O_unit. simpl.
    unfold hfiber in *. unfold hPullback in *. simpl in *.
    exists (x.1.1;tt). reflexivity.
  - intros P [p H].
    unfold cl_hPullback, cloture', cloture, nchar_to_sub, nsub_to_char, subobject_hPullback_into_product, compose in *; simpl in *.
      destruct P as [x [[y1 y'] q]].  
      induction p.
      + destruct y' as [[y2 y'] r]. exists (y2,y'). exact r.
      + simpl.
        apply le_pred in H. simpl in H.
        specialize (IHn (x;y') (p;H)). simpl in IHn.
        exists (y1,IHn).
        exact q.


  
End Cloture_hPullback.

Section Cech_Nerve_cloture.

Context `{ua: Univalence}.
Context `{fs: Funext}.

Definition Δ1 (Y:Trunk n) := @hPullback Y.1 Y.1 idmap 1.

Lemma Δ1_is_Y (Y:Trunk n) : Δ1 Y <~> Y.1.
  refine (equiv_adjointify _ _ _ _).
  - unfold Δ1, hPullback. simpl.
    intros [x [[y tt] p]]; simpl in *.
    exact x.
  - unfold Δ1, hPullback. simpl.
    intro y. exists y. exists (y,tt). reflexivity.
  - intro y. reflexivity.
  - intros [x [[y tt] p]]; simpl in *. destruct tt.
    destruct p. reflexivity.
Defined.

Definition diagonal_diagram (Y:Trunk n) := @Cech_nerve_diagram Y.1 (Δ1 Y) (Δ1_is_Y Y).

Definition prod_diagram (Y:Trunk n) := @Cech_nerve_diagram Unit Y.1 (λ _, tt).

Definition cloture_cech_nerve_graph (Y:Trunk n) : graph.
  refine (Build_graph _ _).
  exact nat.
  intros m n.
  exact ((m = S n) /\ (nat_interval m)).
Defined.

Definition cloture_cech_nerve_diagram (Y:Trunk n) : diagram (cloture_cech_nerve_graph Y).
  
    
  
End Cech_Nerve_cloture.