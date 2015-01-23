Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import colimit.
Require Import Peano.
Require Import nat_lemmas.
Require Import cech_nerve.
Require Import equivalence sub_object_classifier reflective_subuniverse modalities.
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
Local Definition mod_nj := sheaf_def_and_thm.mod_nj.
Local Definition nj := sheaf_def_and_thm.nj.
Local Definition j_is_nj := sheaf_def_and_thm.j_is_nj.
Local Definition j_is_nj_unit := sheaf_def_and_thm.j_is_nj_unit.
Local Definition islex_mod_nj := sheaf_def_and_thm.islex_mod_nj.
Local Definition islex_nj := sheaf_def_and_thm.islex_nj.
Local Definition lex_compat := sheaf_def_and_thm.lex_compat.


Definition cl_char_hPullback {X Y:Trunk (trunc_S n)} (f:Y.1 -> X.1) (k:nat) : hProduct Y.1 (S k) → Trunk n
  := (cloture (char_hPullback n f k X.2 Y.2)).

Definition cl_char_hPullback' {X Y:Trunk (trunc_S n)} (f:Y.1 -> X.1) (k:nat) (P : hProduct Y.1 (S k)) : Trunk n.
    induction k.
    - simpl. exists Unit. apply trunc_unit. 
    - simpl. exists ((O nj (f (fst P) = f (fst (snd P)) ; istrunc_paths X.2 (f (fst P)) (f (fst (snd P))))).1.1 /\ (IHk (snd P)).1).
      refine trunc_prod; [exact ((O nj
         (f (fst P) = f (fst (snd P));
         istrunc_paths X.2 (f (fst P)) (f (fst (snd P))))).1).2 | exact (IHk (snd P)).2].
Defined.

Theorem cl_char_hPullback_is_' {X Y:Trunk (trunc_S n)} (f:Y.1 -> X.1) (k:nat) (P:hProduct Y.1 k.+1) : cl_char_hPullback f k P = cl_char_hPullback' f k P.
  apply truncn_unique. exact fs.
  induction k.
  - simpl. unfold cl_char_hPullback, cloture. simpl.
    symmetry.
    pose (p := (O_modal ((Unit;trunc_unit n); subuniverse_unit nj))..1..1).
    etransitivity; try exact p.
    repeat apply (ap pr1). apply ap.
    apply path_sigma' with 1.
    apply path_ishprop.
  - simpl. unfold cl_char_hPullback, cloture in *. simpl in *.
    specialize (IHk (snd P)).
    pose subuniverse_product'.
    rewrite <- IHk.
    exact (p n nj ua fs (f (fst P) = f (fst (snd P));
        istrunc_paths X.2 (f (fst P)) (f (fst (snd P)))) (char_hPullback n f k X.2 Y.2 (snd P)) _). 
Defined.

Theorem cl_char_hPullback_is_'_1 {X Y:Trunk (trunc_S n)} (f:Y.1 -> X.1) (k:nat) (P:hProduct Y.1 k.+1) : (cl_char_hPullback f k P).1 = (cl_char_hPullback' f k P).1.
  induction k.
  - simpl. unfold cl_char_hPullback, cloture. simpl.
    apply OUnit_is_Unit. exact ua. exact fs.
  - simpl. unfold cl_char_hPullback, cloture in *. simpl in *.
    specialize (IHk (snd P)).
    pose subuniverse_product'.
    apply (transport (λ U, _ = _ * U) IHk).
    exact (p n nj ua fs (f (fst P) = f (fst (snd P));
        istrunc_paths X.2 (f (fst P)) (f (fst (snd P)))) (char_hPullback n f k X.2 Y.2 (snd P)) _). 
Defined.

Theorem cl_char_hPullback_is_'_fun : @cl_char_hPullback = @cl_char_hPullback'.
  repeat (apply path_forall; intros ? ).
  apply cl_char_hPullback_is_'.
Defined.

Theorem cl_hPullback_is_' {X Y:Trunk (trunc_S n)} (f:Y.1 -> X.1) (k:nat)
: {P:hProduct Y.1 k.+1 & (cl_char_hPullback f k P).1 } <~> {P:hProduct Y.1 k.+1 & (cl_char_hPullback' f k P).1}.
  refine (@equiv_functor_sigma_id _ _ _ _).
  intro P.
  apply equiv_path. 
  apply cl_char_hPullback_is_'_1.
Defined.

Lemma cl_char_hPullback'_is_dense (X Y:Trunk (trunc_S n)) (f : Y.1 -> X.1) (k:nat)
: EnJ {P : hProduct Y.1 (S k) & (cl_char_hPullback' f k P).1}.
  refine (@transport_density_sigma _ _ _ _ _ _).
  (* exact ((hProduct Y.1 k.+1)). *)
  exact ((char_hPullback _ f k X.2 Y.2)).
  (* apply path_universe_uncurried. *)
  intro x; simpl.
  apply (cl_char_hPullback_is_'_1 f k).
Defined.
  
Lemma density_lemma_hPullback (X Y:Trunk (trunc_S n)) (f : Y.1 -> X.1) (k:nat) (x : ∃ P : Y.1 ∧ hProduct Y.1 (S k), (cl_char_hPullback' f (S k) P).1) (u : (char (cl_char_hPullback'_is_dense X Y f (S k)) x).1)
      : (fst x.2) = O_unit nj (f (fst x.1) = f (fst (snd x.1)); istrunc_paths X.2 (f (fst x.1)) (f (fst (snd x.1)))) (fst u.1).
  destruct x as [x [q q']]; destruct u as [[π π'] u]; simpl in *.
  assert (v := moveR_transport_p idmap _ _ _ u).
  clear u.
  etransitivity; try exact (ap fst v)^.
  clear v.
  unfold cl_char_hPullback_is_'_1. simpl.
  repeat rewrite transport_paths_FlFr. simpl.
  rewrite ap_const. simpl. rewrite concat_1p.
  rewrite transport_pp.
  unfold subuniverse_product'. simpl.
  unfold equiv_adjointify. rewrite transport_path_universe_uncurried.
  unfold OUnit_is_Unit, O_modal.
  assert (rew := λ T T', eissect _ (IsEquiv := @isequiv_unique_subuniverse n nj T T')).
  unfold Sect in rew; simpl in rew.
  rewrite rew; clear rew.

  assert (rew := λ T T', eissect _ (IsEquiv := @isequiv_truncn_unique fs n T T')).
  unfold Sect in rew; simpl in rew.
  unfold pr1_path.
  rewrite rew; clear rew.
  
  rewrite <- transport_idmap_ap.
  rewrite transport_prod.
  rewrite transport_const. simpl.
  Arguments trunc_equiv A B f {n} H H0.

  set (foo := ( λ
     x0
      y : f (fst x) = f (fst (snd x))
          ∧ (char_hPullback n f k X.2 Y.2 (snd x)).1,
     trunc_equiv (fst x0 = fst y ∧ snd x0 = snd y) 
                 (x0 = y) (path_prod_uncurried x0 y) trunc_prod isequiv_path_prod)).
  exact (ap10 (O_rec_retr (existT (IsTrunc n) (f (fst x) = f (fst (snd x)) ∧ (char_hPullback n f k X.2 Y.2 (snd x)).1) foo)
                   (O nj
                      (f (fst x) = f (fst (snd x));
                       istrunc_paths X.2 (f (fst x)) (f (fst (snd x)))))
                   (λ
                      x0 : f (fst x) = f (fst (snd x))
                           ∧ (char_hPullback n f k X.2 Y.2 (snd x)).1,
                           O_unit nj
                                  (f (fst x) = f (fst (snd x));
                                   istrunc_paths X.2 (f (fst x)) (f (fst (snd x)))) 
                                  (fst x0))) (π, π')).
Defined.

Definition forget_cl_char_hPullback' {X Y:Trunk (trunc_S n)} (f:Y.1 -> X.1) (k:nat)
           (x : hProduct Y.1 (S (S k)))
           (P : (cl_char_hPullback' f (S k) x).1)
: forall p:{p:nat & p <= k.+1}, (cl_char_hPullback' f k (forget_hProduct Y.1 (S k) x p)).1.
  intros [p Hp].
  induction (decidable_paths_nat 0 p) as [| a].
  { destruct a. simpl in *.
    exact (snd P). }
  
  induction (decidable_paths_nat (S k) p) as [| b].
  { destruct a0. simpl in *.
    induction k.
    simpl in *. exact tt.
    simpl in *.
    split. exact (fst P).
    apply IHk. exact (snd P).
    apply succ_not_0. }
  
  apply neq_symm in a.
  apply neq_0_succ in a.
  destruct a as [p' Hp'].
  (* destruct Hp'. *)
  assert (l := le_neq_lt _ _ (neq_symm _ _ b) Hp).
  assert (l0 := le_pred _ _ l). simpl in l0. clear b l. simpl in *. 
  generalize dependent k. generalize dependent p. generalize dependent p'. induction p'; intros.
  - simpl in *.
    destruct Hp'.
    assert (k' := gt_0_succ k l0); destruct k' as [k' Hk]. destruct Hk. simpl in *.
    destruct P as [P PP].
    split.
    generalize dependent P; apply O_rec; intro P.
    generalize dependent (fst PP); apply O_rec; intro PPP.
    apply O_unit.
    exact (P @ PPP).
    exact (snd PP).
  - simpl in *.
    destruct Hp'.
    destruct P as [P PP].
    assert (n' := ge_succ_succ (S p') _ l0).
    destruct n' as [n' Hn']. destruct Hn'. simpl in PP. 
    specialize (IHp' (p'.+1) 1 n' (snd x) PP). simpl. split.
    exact P.
    apply IHp'.
    exact (le_pred _ _ l0).
Defined.


  
End Cloture_hPullback.
