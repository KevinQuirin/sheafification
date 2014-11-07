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
Arguments istrunc_paths {A} {n} H x y: simpl never.
Arguments truncn_unique _ {n} A B H: simpl never.

Section Cloture_hPullback.
  
Context `{ua: Univalence}.
Context `{fs: Funext}.

Local Definition n0 := sheaf_def_and_thm.n0.
Local Definition n := sheaf_def_and_thm.n.
Local Definition nj := sheaf_def_and_thm.nj.
Local Definition j_is_nj := sheaf_def_and_thm.j_is_nj.
Local Definition j_is_nj_unit := sheaf_def_and_thm.j_is_nj_unit.
Local Definition islex_nj := sheaf_def_and_thm.islex_nj.
Local Definition lex_compat := sheaf_def_and_thm.lex_compat.


Definition cl_char_hPullback {X Y:Trunk (trunc_S n)} (f:Y.1 -> X.1) (k:nat) : hProduct Y.1 (S k) → Trunk n
  := (cloture (char_hPullback n f k X.2 Y.2)).

Set Printing Universes.


Definition cl_char_hPullback' {X Y:Type} (f:Y -> X) (k:nat) (TrX : IsTrunc (trunc_S n) X) (TrY : IsTrunc (trunc_S n) Y) (P : hProduct Y (S k)) : Trunk n.
    induction k.
    - simpl. exists Unit. apply trunc_unit. 
    - simpl. exists ((O nj (f (fst P) = f (fst (snd P)) ; istrunc_paths TrX (f (fst P)) (f (fst (snd P))))).1.1 /\ (IHk (snd P)).1).
      refine trunc_prod; [exact ((O nj
         (f (fst P) = f (fst (snd P));
         istrunc_paths TrX (f (fst P)) (f (fst (snd P))))).1).2 | exact (IHk (snd P)).2].
Defined.

Theorem cl_char_hPullback_is_' {X Y:Trunk (trunc_S n)} (f:Y.1 -> X.1) (k:nat) (P:hProduct Y.1 k.+1) : cl_char_hPullback f k P = cl_char_hPullback' f k X.2 Y.2 P.
  apply truncn_unique. exact fs.
  induction k.
  - simpl. unfold cl_char_hPullback, cloture, compose. simpl.
    symmetry.
    pose (p := (O_modal ((Unit;trunc_unit n); subuniverse_unit nj))..1..1).
    etransitivity; try exact p.
    repeat apply (ap pr1). apply ap.
    apply path_sigma' with 1.
    apply path_ishprop.
  - simpl. unfold cl_char_hPullback, cloture, compose in *. simpl in *.
    specialize (IHk (snd P)).
    pose subuniverse_product'.
    rewrite <- IHk.
    exact (p n nj (f (fst P) = f (fst (snd P));
        istrunc_paths X.2 (f (fst P)) (f (fst (snd P)))) (char_hPullback n f k X.2 Y.2 (snd P))). 
Qed.

  
End Cloture_hPullback.

Section Cech_Nerve_cloture.

  
End Cech_Nerve_cloture.