(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import PathGroupoid_.

Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
Local Open Scope type_scope.

Module Export T.

  Private Inductive T {A B:Type} (f: A -> B) : Type :=
    | t : A -> (T f).

  Arguments t {A B f} a.

  Axiom tp : forall {A B f} (a b:A), f a = f b -> @t A B f a = @t A B f b.

  Axiom tp_1 : forall {A B f} (a:A), @tp A B f a a 1 = 1.

  Definition T_ind {A B:Type} {f:A -> B} (P : T f -> Type)
             (t' : forall a, P (t a))
             (tp' : forall a b p, transport P (tp a b p) (t' a) = t' b)
             (tp_1' : forall a, transport2 P (tp_1 a) (t' a) = tp' a a 1)
    : forall w, P w
    := fun w => match w with
                |t a => fun _ => t' a
                end tp_1'.

  Axiom T_ind_beta_tp : forall {A B:Type} {f:A -> B} (P : T f -> Type)
             (t' : forall a, P (t a))
             (tp' : forall a b p, transport P (tp a b p) (t' a) = t' b)
             (tp_1' : forall a, transport2 P (tp_1 a) (t' a) = tp' a a 1)
             a b p,
      apD (T_ind P t' tp' tp_1') (tp a b p) = tp' a b p.

  Axiom T_ind_beta_tp_1 : forall {A B:Type} {f:A -> B} (P : T f -> Type)
             (t' : forall a, P (t a))
             (tp' : forall a b p, transport P (tp a b p) (t' a) = t' b)
             (tp_1' : forall a, transport2 P (tp_1 a) (t' a) = tp' a a 1)
             a,
      apD02 (T_ind P t' tp' tp_1') (tp_1 a) @ (concat_p1 _) @ (tp_1' a) = T_ind_beta_tp P t' tp' tp_1' a a 1.
        
End T.

Definition T_rec {A B:Type} {f:A -> B} (P:Type)
           (t': A -> P)
           (tp' : forall (a b:A) (p:f a = f b), t' a = t' b)
           (tp_1' : forall a, tp' a a 1 = 1)
  : T f -> P.
Proof.
  refine (T_ind _ t' (fun a b p => transport_const _ _ @ tp' a b p)  _).
  intro a.
  pose (p:=whiskerR (transport2_const (A:=T f) (B:= P) (tp_1 a) (t' a) @ concat_p1 _)^ (tp' a a 1)). cbn in p.
  pose (p1:=(whiskerL (transport2 (λ _ : T f, P) (tp_1 a) (t' a)) (tp_1' a) @ concat_p1 _)^).
  exact (p1 @ p).
Defined.

Definition T_rec_beta_tp {A B:Type} {f:A -> B} (P:Type)
           (t': A -> P)
           (tp' : forall (a b:A) (p:f a = f b), t' a = t' b)
           (tp_1' : forall a, tp' a a 1 = 1)
           a b p
  : ap (T_rec P t' tp' tp_1') (tp a b p) = tp' a b p.
Proof.
Admitted.

Definition T_rec_beta_tp_1 {A B:Type} {f:A -> B} (P:Type)
           (t': A -> P)
           (tp' : forall (a b:A) (p:f a = f b), t' a = t' b)
           (tp_1' : forall a, tp' a a 1 = 1)
           a
  : ap02 (T_rec P t' tp' tp_1') (tp_1 a) = T_rec_beta_tp P t' tp' tp_1' a a 1 @ (tp_1' a).
Proof.
Admitted.

Lemma path_T {A A' B:Type} (f: A -> A')
      (α β : T f -> B)
      (eq1: α o t == β o t)
      (eq2: forall a b p, eq1 a @ ap β (tp a b p) = ap α (tp a b p) @ eq1 b)
      (eq3: forall a,  (eq2 a a 1)
                      = transport (λ U, eq1 a @ ap β U = ap α U @ eq1 a) (tp_1 a)^ (concat_p1 (eq1 a) @ (concat_1p (eq1 a))^))
  : α == β.
Proof.
  (* We refer to the general case in R.v *)
Admitted.


Lemma T_trunc `{fs: Funext} (m:trunc_index) (A:Type) (B:TruncType m) (f:A -> B)
    : Trunc m (T f) <~> Trunc m (T (Trunc_rec (n:=m) f)).
  Proof.
    refine (equiv_adjointify _ _ _ _).
    - refine (Trunc_rec _).
      refine (T_rec _ _ _ _).
      intro a. exact (tr (t (tr a))).
      intros a b p; cbn. apply ap. apply tp. exact p.
      intros a; cbn.
      match goal with |[|- ap ?ff ?pp =_] => path_via (ap (x:=t (tr a)) ff 1) end.
      apply ap.
      apply (tp_1 (f:=Trunc_rec (n:=m) f) (tr a)).
    - refine (Trunc_rec _).
      refine (T_rec _ _ _ _).
      refine (Trunc_rec _).
      intro a; exact (tr (t a)).
      refine (Trunc_ind _ _). intro a. 
      refine (Trunc_ind _ _). intros b p.
      cbn in *.
      apply ap. apply tp. exact p.
      refine (Trunc_ind _ _).
      intro a. cbn.
      match goal with |[|- ap ?ff ?pp =_] => path_via (ap (x:=t a) ff 1) end.
      apply ap. apply tp_1.
    - refine (Trunc_ind _ _).
      refine (path_T _ _ _ _ _ _).
      refine (Trunc_ind _ _). intro a; reflexivity.
      refine (Trunc_ind _ _). intro a.
      refine (Trunc_ind _ _). intros b p.
      cbn in *.
      refine (concat_1p _ @ _). refine (_ @ (concat_p1 _)^).
      match goal with
      |[|- _ = ap (λ x, Trunc_rec ?ff (?gg x)) ?pp]
       => refine (_ @ (ap_compose gg (Trunc_rec ff) pp)^)
      end.
      match goal with
      |[|- _ = ap ?ff (ap (T_rec ?X1 ?X2 ?X3 ?X4) (tp ?aa ?bb ?pp)) ]
       => refine (_ @ (ap02 ff (T_rec_beta_tp X1 X2 X3 X4 aa bb pp)^))
      end. cbn.
      match goal with
      |[|- _ = ap ?ff (ap ?gg ?pp)]
       => refine (_ @ (ap_compose gg ff pp))
      end. cbn.
      match goal with
      |[|- _ = (ap (λ x, T_rec ?X1 ?X2 ?X3 ?X4 x) (tp ?aa ?bb ?pp)) ]
       => refine ((T_rec_beta_tp X1 X2 X3 X4 aa bb pp)^)
      end.

      refine (Trunc_ind _ _). cbn.
      intro a. rewrite transport_paths_FlFr.
      repeat rewrite ap_V. repeat rewrite inv_V.
      match goal with
      |[|- _ = (?pp @ 1) @ _]
       => rewrite (concat_p1 pp)
      end.
      repeat rewrite concat_p_pp. apply moveL_Mp.
      match goal with
      |[|- ?XX = _] => path_via (XX^^); apply ap
      end.
      match goal with
      |[|- _ = ap (λ x, ap ?ff x @ 1) ?pp] => 
       assert (rr: ap (λ x, ap ff x @ 1) pp = concat_p1 _ @ ap02 ff pp @ (concat_1p _)^)
      end.
      { rewrite concat_ap_Fpq.
        apply moveL_pV.
        apply moveL_Mp.
        rewrite concat_p_pp.
        match goal with
        |[|- (_ @ whiskerR ?hh _) @ _ = _]
         => pose (rew := whiskerR_p1 hh)
        end.
        cbn in *. rewrite rew; clear rew.
        rewrite ap02_is_ap. reflexivity. }
      rewrite rr; clear rr.
      repeat rewrite inv_pp.
      repeat rewrite concat_pp_p.
      repeat rewrite inv_V.
      apply whiskerL. cbn. rewrite concat_p1.
      rewrite ap02_V. rewrite inv_V.
      match goal with
      |[|- _ = ap02 (λ x, Trunc_rec ?ff (?gg x)) ?pp]
       => rewrite (ap02_compose _ _ _ gg (Trunc_rec ff) _ _ _ _ pp)
      end.
      apply whiskerL.
      rewrite T_rec_beta_tp_1. cbn. rewrite concat_p1.
      rewrite ap02_pp. apply whiskerL.
      rewrite ap02_pp. cbn. rewrite concat_p1.        
      rewrite <- ap02_is_ap. apply moveR_Vp.
      match goal with
      |[|- _ = _ @ (ap02 ?ff (ap02 ?gg ?pp))] =>
       pose (rew := ap02_compose _ _ _ gg ff _ _ _ _ pp)
      end.
      cbn in rew. rewrite concat_p1 in rew. rewrite <- rew; clear rew.
      rewrite T_rec_beta_tp_1.
      apply whiskerL. 
      rewrite concat_ap_pFq. apply moveL_pM.
      match goal with
      |[|- (_ @ whiskerL _ ?hh) @ _ = _] => exact (whiskerL_1p hh)
      end.
    - refine (Trunc_ind _ _).
      refine (path_T _ _ _ _ _ _).
      intro a; reflexivity.
      intros a b p; cbn.
      refine (concat_1p _ @ _). refine (_ @ (concat_p1 _)^).
      match goal with
      |[|- _ = ap (λ x, Trunc_rec ?ff (?gg x)) ?pp]
       => refine (_ @ (ap_compose gg (Trunc_rec ff) pp)^)
      end.
      match goal with
      |[|- _ = ap ?ff (ap (T_rec ?X1 ?X2 ?X3 ?X4) (tp ?aa ?bb ?pp)) ]
       => refine (_ @ (ap02 ff (T_rec_beta_tp X1 X2 X3 X4 aa bb pp)^))
      end. cbn.
      match goal with
      |[|- _ = ap ?ff (ap ?gg ?pp)]
       => refine (_ @ (ap_compose gg ff pp))
      end. cbn.
      match goal with
      |[|- _ = (ap (λ x, T_rec ?X1 ?X2 ?X3 ?X4 x) (tp ?aa ?bb ?pp)) ]
       => refine ((T_rec_beta_tp X1 X2 X3 X4 aa bb pp)^)
      end.

      intro a. rewrite transport_paths_FlFr.
      repeat rewrite ap_V. repeat rewrite inv_V.
      cbn.
      match goal with
      |[|- _ = (?pp @ 1) @ _]
       => rewrite (concat_p1 pp)
      end.
      repeat rewrite concat_p_pp. apply moveL_Mp.
      match goal with
      |[|- ?XX = _] => path_via (XX^^); apply ap
      end.
      match goal with
      |[|- _ = ap (λ x, ap ?ff x @ 1) ?pp] => 
       assert (rr: ap (λ x, ap ff x @ 1) pp = concat_p1 _ @ ap02 ff pp @ (concat_1p _)^)
      end.
      { rewrite concat_ap_Fpq.
        apply moveL_pV.
        apply moveL_Mp.
        rewrite concat_p_pp.
        match goal with
        |[|- (_ @ whiskerR ?hh _) @ _ = _]
         => pose (rew := whiskerR_p1 hh)
        end.
        cbn in *. rewrite rew; clear rew.
        rewrite ap02_is_ap. reflexivity. }
      rewrite rr; clear rr.
      repeat rewrite inv_pp.
      repeat rewrite concat_pp_p.
      repeat rewrite inv_V.
      apply whiskerL. cbn. rewrite concat_p1.
      rewrite ap02_V. rewrite inv_V.
      match goal with
      |[|- _ = ap02 (λ x, Trunc_rec ?ff (?gg x)) ?pp]
       => rewrite (ap02_compose _ _ _ gg (Trunc_rec ff) _ _ _ _ pp)
      end.
      apply whiskerL.
      rewrite T_rec_beta_tp_1. cbn. rewrite concat_p1.
      rewrite ap02_pp. apply whiskerL.
      rewrite ap02_pp. cbn. rewrite concat_p1.        
      rewrite <- ap02_is_ap. apply moveR_Vp.
      match goal with
      |[|- _ = _ @ (ap02 ?ff (ap02 ?gg ?pp))] =>
       pose (rew := ap02_compose _ _ _ gg ff _ _ _ _ pp)
      end.
      cbn in rew. rewrite concat_p1 in rew. rewrite <- rew; clear rew.
      rewrite (T_rec_beta_tp_1 (f:= Trunc_rec f)).
      apply whiskerL. 
      rewrite concat_ap_pFq. apply moveL_pM.
      match goal with
      |[|- (_ @ whiskerL _ ?hh) @ _ = _] => exact (whiskerL_1p hh)
      end.
  Defined.

  Definition equiv_T_fun {A B C D:Type}
           (f: A -> B) 
           (g: C -> D)
           (α: A -> C)
           (φ: forall a b, (f a = f b) -> g (α a) = g (α b))
           (κ: forall a, (φ a a) 1 = 1)
  : T f -> T g.
Proof.
  refine (T_rec _ _ _ _).
  - intro a. apply t. exact (α a).
  - intros a b p; cbn. apply tp.
    apply φ. exact p.
  - intro a; cbn.
    refine (ap (tp (α a) (α a)) (κ a) @ _).
    apply tp_1.
Defined.

Definition equiv_T {A B C D:Type}
           (f: A -> B) 
           (g: C -> D)
           (α: A = C)
           (φ: forall a b, (f a = f b) <~> g (equiv_path _ _ α a) = g (equiv_path _ _ α b))
           (κ: forall a, (φ a a) 1 = 1)
  : IsEquiv (equiv_T_fun f g (equiv_path _ _ α) φ κ).
Admitted.
