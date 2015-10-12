(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import Limit.
Require Import PathGroupoid_ Forall_ Equivalences_ epi_mono reflective_subuniverse modalities OPaths.
Require Import T.
(* Require Import T_telescope OT OT_Tf. *)

(* Require Import sheaf_base_case. *)
(* Require Import sheaf_def_and_thm. *)
(* Require Import sheaf_induction. *)



Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
Local Open Scope type_scope.

Lemma path_path_prod (A B : Type) (z z' : A ∧ B) (p q: z = z')
  : (ap fst p = ap fst q) -> (ap snd p = ap snd q) -> p=q.
Proof.
  intros r s.
  refine ((eta_path_prod _)^ @ _ @ (eta_path_prod _)).
  destruct r,s. reflexivity.
Defined.

Generalizable All Variables.

Lemma transport_T `{f: forall (z: Z), A z -> B z} `(p: z1 = z2 :> Z) (x: A z1)
  : transport (λ z, T (f z)) p (t x) = t (p # x).
      by destruct p.
Defined.

Lemma bar (Y:Type) (A:Y -> Type) 
  : T (λ x : ∃ y : Y, A y, pr1 x) <~> (∃ y : Y, T (λ _ : A y, tt)).
Proof.
  transparent assert (F : ((∃ y : Y, T (λ _ : A y, tt)) -> T (λ x : ∃ y : Y, A y, pr1 x))).
  { intros [y a].
    refine (T_rec _ _ _ _ a).
    intro x. apply t.
    exists y.
    exact x.
    intros u v p; cbn.
    apply tp; cbn. reflexivity.
    intro u; cbn.
    match goal with |[|- @tp _ _ ?ff ?aa ?bb _ = _] => exact (tp_1 (f:=ff) aa)  end. }

  transparent assert (G: (T (λ x : ∃ y : Y, A y, pr1 x) -> (∃ y : Y, T (λ _ : A y, tt)))).
  { refine (T_rec _ _ _ _).
    intros x. exists x.1. apply t. exact x.2.
    intros a b p. cbn.
    refine (path_sigma' _ _ _).
    exact p.
    cbn.
    refine (transport_T (f:=(λ y a, tt)) p (pr2 a) @ _).
    apply tp. apply path_ishprop.
    intro a; cbn.
    match goal with
    |[|- ?XX _ = _] => path_via (XX 1)
    end.
    apply ap.
    
    refine (concat_1p _ @ _).
    cbn.
    match goal with
    |[|- tp _ _ ?pp = _] => assert (r: 1 = pp) by apply path_ishprop
    end.
    destruct r. 
    match goal with |[|- @tp _ _ ?ff ?aa ?bb _ = _] => exact (tp_1 (f:=ff) aa) end. }
  refine (equiv_adjointify G F _ _).
  - intros [y x]. revert x.
    unfold F; clear F; unfold G; clear G.
    refine (path_T _ _ _ _ _ _).
    intro x; reflexivity.
    intros a b p; cbn.
    refine (concat_1p _ @ _ @ (concat_p1 _)^).
    match goal with
    |[|- _ = ap (λ x, ?gg (?ff x)) ?pp] =>
     refine (_ @ (ap_compose ff gg pp)^)
    end.
    refine (_ @ (ap02 _ (T_rec_beta_tp _ _ _ _ _ _ _)^)).
    refine (_ @ (T_rec_beta_tp _ _ _ _ _ _ _)^).
    cbn.
    refine (ap_existT _ _ _ _ _ @ _).
    apply ap. symmetry; refine (concat_1p _ @ _).
    apply ap; apply path_ishprop.

    intro a; cbn. rewrite transport_paths_FlFr.
    rewrite concat_ap_Fpq. rewrite concat_ap_pFq.
    simpl. rewrite (concat_p1 (whiskerL 1 (ap (ap (exist (λ y0 : Y, T (λ _ : A y0, tt)) y)) (tp_1 a)^))^).
    repeat rewrite ap_V.
    match goal with
    |[|- _ = _ @ whiskerR (ap (ap (λ x, ?gg (?ff x))) ?pp)^ 1]
     => rewrite <- (ap02_is_ap _ _ (λ x, gg (ff x)) _ _ _ _ pp);
       rewrite (ap02_compose _ _ _ ff gg _ _ _ _ pp)
    end.
    apply moveL_Vp.
    rewrite whiskerR_RV.
    rewrite whiskerR_pp. rewrite inv_pp.
    match goal with
    |[|- _ = (whiskerR (ap02 _ (ap02 (T_rec ?P1 ?P2 ?P3 ?P4) (tp_1 a)) @ _) _)^ @ _]
     => rewrite (T_rec_beta_tp_1 P1 P2 P3 P4 a)
    end.
    rewrite whiskerR_pp. rewrite inv_pp.
    do 3 rewrite <- whiskerR_RV. rewrite inv_V.
    unfold ap_compose at 2. cbn.
    match goal with
    |[|- _ = (_ @ ?P) @ _] => rewrite (concat_1p P)
    end.
    repeat rewrite concat_p_pp.

    match goal with
    |[|- ((((((whiskerL ?P1 ?P2 @ concat_1p _) @_)@_)@_)@_)@_)@_= _] =>
     pose (rew:=  whiskerL_1p P2); rewrite concat_pp_p in rew
    end.
    apply moveL_Vp in rew. rewrite rew; clear rew. cbn.
    rewrite (concat_1p (ap (ap (exist (λ y0 : Y, T (λ _ : A y0, tt)) y)) (tp_1 a))^).
    apply moveR_pV.
    match goal with
    |[|- _ = (?P1 @ whiskerR ?hh 1) @ _] =>
     rewrite (concat_pp_p (p:=P1));
       pose (rew := whiskerR_p1 hh); rewrite concat_pp_p in rew;
       apply moveL_Vp in rew
    end.
    rewrite rew; clear rew; cbn. rewrite inv_V.
    match goal with
    |[|- _ = whiskerR ?hh _ @ (?P1 @ _)]
     => rewrite (concat_p_pp (q:=P1));
       pose (rew := whiskerR_p1 hh); rewrite concat_pp_p in rew;
       apply moveL_Vp in rew
    end.
    rewrite rew; clear rew; cbn.
    match goal with
    |[|- _ = (1 @ ?P1) @ _] =>
     rewrite (concat_1p P1)
    end.
    apply whiskerR. 
    rewrite ap02_pp. rewrite inv_pp. rewrite ap02_V. apply whiskerR.
    match goal with
    |[|- _ = (ap02 (T_rec ?P1 ?P2 ?P3 ?P4) (tp_1 ?P5))^]
     => rewrite (T_rec_beta_tp_1 P1 P2 P3 P4 P5)
    end. cbn.
    rewrite inv_pp. apply whiskerR.
    match goal with
    |[|- _ = (ap _ (_ @ match path_ishprop ?bar ?foo in (_ = y0) return _ with |_=>_ end) @ _)^] =>
     assert (r: 1 = foo) by apply path_ishprop; destruct r;
     assert (r: 1 = path_ishprop bar 1) by apply path_ishprop; destruct r                     
    end. cbn.
    repeat rewrite ap_pp. repeat rewrite inv_pp. cbn.
    hott_simpl. apply whiskerR.
    rewrite concat_1p.
    apply moveR_Vp.
    pose (p := tp_1 (f:=λ _:A y, tt) a).
    pose (r := apD (λ U, ap_existT (λ y0 : Y, T (λ _ : A y0, tt)) y (t a) (t a) U) p^).
    cbn in r; rewrite <- r; clear r; unfold p; clear p.
    rewrite transport_paths_FlFr.
    rewrite concat_p1. rewrite ap_V. rewrite inv_V. rewrite ap_V. reflexivity.
  - refine (path_T _ _ _ _ _ _).
    intro x. reflexivity.
    intros [a x] [b y] p; cbn.
    refine (concat_1p _ @ (ap_idmap _) @ _ @ (concat_p1 _)^).

    refine (_ @ (ap_compose G F (tp (a;x) (b;y) p))^).
    unfold G.
    refine (_ @ (ap02 F (T_rec_beta_tp _ _ _ _ _ _ _)^)).
    cbn in *.
    destruct p. cbn. unfold F; clear F.
    pose (F := λ x:Y, λ x':T (λ _ : A x, tt),
                         T_rec (T (λ x0 : ∃ y : Y, A y, pr1 x0))
                               (λ x0 : A x, t (x; x0))
                               (λ (u v : A (x)) (_ : tt = tt),
                                tp (x; u) (x; v) (idpath x))
                               (λ u : A (x), tp_1 (x; u)) 
                               x').
    refine (_ @ (ap_path_sigma_1 F a (1 @ tp x y (path_ishprop tt tt)))^).
    refine (_ @ (ap_pp _ _ _)^). cbn.
    refine (_ @ (concat_1p _)^).
    refine (_ @ (T_rec_beta_tp _ _ _ _ _ _ _)^). reflexivity.

    intros [a x]; cbn.
    match goal with |[|- ?XX = _] => set (X := XX) end.
    rewrite transport_paths_FlFr.
    rewrite concat_ap_Fpq. rewrite concat_ap_pFq.
    do 2 rewrite ap_V.
    rewrite <- (ap02_is_ap _ _ (λ x : T (λ x : ∃ y : Y, A y, pr1 x), F (G x))).
    rewrite ap02_compose.
    cbn.
    rewrite whiskerR_RV. rewrite whiskerR_pp.
    match goal with
    |[|- _ = (?P1 @ ?P2) @ (?P3 @ ?P4)^ ] =>
     rewrite (concat_p1 P1)
    end.
    apply moveL_Vp. rewrite inv_pp. apply moveL_pV.
    (* unfold G at 12. rewrite T_rec_beta_tp_1. *)
    match goal with
    |[|- _ = (whiskerR (?P1 @ _) _)^ ]
     => rewrite (concat_p1 P1)
    end.
    (* rewrite ap02_pp. *)
    rewrite <- whiskerR_RV.
    (* rewrite inv_pp. rewrite whiskerR_pp. *)
    unfold X; clear X.
    match goal with
    |[|- (whiskerL _ ?hh @ (((?P @ _) @ _) @ _)) @ _ = _] =>
     repeat rewrite (concat_pp_p (p:=P));
       rewrite (concat_p_pp (q := P));
       pose (rew := whiskerL_1p hh); rewrite concat_pp_p in rew;
       apply moveL_Vp in rew
    end.
    rewrite rew; clear rew. cbn.
    match goal with
    |[|- ( _ @ (_ @ ?P)) @ (whiskerR ?hh _) = _] =>
     repeat rewrite (concat_p_pp (r := P));
       rewrite (concat_pp_p (q:=P));
       pose (rew := whiskerR_p1 hh); 
       apply moveL_pV in rew
    end.
    rewrite rew; clear rew.
    repeat rewrite concat_p_pp. apply moveR_pV.
    match goal with
    |[|- _ = whiskerR ?hh _ @ _] =>
     pose (rew := whiskerR_p1 hh);
       rewrite concat_pp_p in rew;
       apply moveL_Vp in rew
    end.
    rewrite rew; clear rew; cbn.
    rewrite (concat_1p (ap02 F (ap02 G (tp_1 (a;x))))^).
    unfold G at 23.
    rewrite T_rec_beta_tp_1.
    rewrite <- ap02_V. rewrite inv_pp.
    rewrite ap02_pp.
    cbn. rewrite concat_pV_p. apply whiskerR.
    rewrite inv_pp. rewrite ap02_pp. cbn.
    match goal with |[|- _ = 1 @ ?P] => rewrite (concat_1p P) end.
    assert (r: 1 = (path_ishprop tt tt)) by apply path_ishprop.
    destruct r.
    match goal with
    |[|- (((((( 1 @ ?P) @ ?Q) @ _) @_)@_)@_)@ _ = _] =>
     rewrite (concat_1p P);
       rewrite (concat_p1 (P @ Q))
    end.

    pose (p :=apD (λ U, ap_idmap U) (tp_1 (f:=(λ x : ∃ y : Y, A y, pr1 x)) (a;x))^). cbn in p.
    rewrite <- p; clear p.
    rewrite transport_paths_FlFr. cbn. repeat rewrite ap_V. repeat rewrite inv_V.
    match goal with
    |[|- ((((?P @ ((?Q @ 1) @ _)) @_)@_)@_)@_ = _] =>
     rewrite (concat_p1 Q)
    end.
    rewrite concat_V_pp.

    pose (p := apD (λ U, (ap_path_sigma_1
      (λ (x0 : Y) (x' : T (λ _ : A x0, tt)),
       T_rec (T (λ x1 : ∃ y : Y, A y, pr1 x1)) (λ x1 : A x0, t (x0; x1))
         (λ (u v : A x0) (_ : tt = tt), tp (x0; u) (x0; v) (idpath x0))
         (λ u : A x0, tp_1 (x0; u)) x') a (1 @ U))) (tp_1 x)^). cbn in p.
    rewrite <- p; clear p.
    rewrite transport_paths_FlFr.
    cbn.
    pose (p := apD (λ U, ap_pp
       (λ x' : T (λ _ : A a, tt),
        T_rec (T (λ x0 : ∃ y : Y, A y, pr1 x0)) (λ x0 : A a, t (a; x0))
          (λ (u v : A a) (_ : tt = tt), tp (a; u) (a; v) (idpath a))
          (λ u : A a, tp_1 (a; u)) x') 1 U) (tp_1 x)^); cbn in p.
    rewrite <- p; clear p.
    rewrite transport_paths_FlFr.
    repeat rewrite inv_pp. repeat rewrite ap_V.
    repeat rewrite inv_V.
    cbn.
    match goal with
    |[|- _ @ (_ @ (1 @ ?P)) = _ ] => rewrite (concat_1p P)
    end.
    rewrite ap_idmap. repeat rewrite concat_pp_p. do 3  apply moveR_Vp.
    match goal with
    |[|- _ @ (1 @ ?P) = _] => rewrite (concat_1p P)
    end.
    rewrite concat_V_pp.
    rewrite concat_ap_pFq.
    apply moveR_pV. repeat rewrite concat_pp_p. apply moveL_Mp.
    match goal with
    |[|- _ @ whiskerL 1 ?hh = _]
     => pose (rew := whiskerL_1p hh);
       (* rewrite concat_pp_p in rew *)
       apply moveL_pV in rew
    end.
    rewrite rew; clear rew.
    rewrite <- (ap02_is_ap _ _ (λ x' : T (λ _ : A a, tt),
         T_rec (T (λ x0 : ∃ y : Y, A y, pr1 x0)) (λ x0 : A a, t (a; x0))
           (λ (u v : A a) (_ : tt = tt), tp (a; u) (a; v) (idpath a))
           (λ u : A a, tp_1 (a; u)) x')).
    rewrite (T_rec_beta_tp_1 (T (λ x0 : ∃ y : Y, A y, pr1 x0)) (λ x0 : A a, t (a; x0))
        (λ (u v : A a) (_ : tt = tt), tp (a; u) (a; v) (idpath a))
        (λ u : A a, tp_1 (a; u))).
    repeat rewrite concat_pp_p.
    do 2 apply whiskerL.
    rewrite ap02_is_ap.
    cbn.
    rewrite ap_V. apply moveL_Vp. rewrite concat_p1.
    match goal with
    |[|- ap _ (ap _ (_ @ match ?foo in (_=y) return _ with |_ => _ end)) = _]
     => assert (r: 1 = foo) by apply path_ishprop; destruct r; cbn
    end.
    match goal with
    |[|- _ = ap (λ x0, ?ff ((path_sigma' (λ x1 : Y, T (λ _ : A x1, tt)) 1 (1 @ x0)))) ?pp ] =>
     rewrite (ap_compose (λ x0, (path_sigma' (λ x1 : Y, T (λ _ : A x1, tt)) 1 (1 @ x0))) ff pp)             
    end. cbn.
    apply ap.
    rewrite ap_pp.
    pose (p := apD (λ U,  ap (path_sigma' (λ y : Y, T (λ _ : A y, tt)) 1)
                             (concat_1p U)) (tp_1 x)^); cbn in p.
    rewrite <- p; clear p.
    rewrite transport_paths_FlFr. simpl. rewrite ap_V. rewrite inv_V.
    rewrite concat_p1. rewrite ap_V.
    rewrite concat_pV_p. reflexivity.
Defined.

Definition equiv_T_equiv_fun `{ua: Univalence} {A B C:Type}
           (f: A -> B)
           (g: C -> B)
           (α: A -> C)
           (e: g o α = f)
  : T f -> T g.
Proof.
  refine (T_rec _ _ _ _).
  intro a; apply t. exact (α a).
  intros a b p; cbn.
  apply tp. exact (ap10 e a @ p @ (ap10 e b)^).
  intro a; cbn.
  path_via (tp (f:=g) (α a) (α a) 1).
  apply ap.
  refine ((concat_p1 _ @@ 1) @ _).
  apply concat_pV.
  apply tp_1.
Defined.

Definition isequiv_T_equiv_fun_path `{ua: Univalence} {A B C:Type}
           (f: A -> B)
           (g: C -> B)
           (α: A = C)
           (e: g o (equiv_path _ _ α) = f)
  : IsEquiv (equiv_T_equiv_fun f g (equiv_path _ _ α) e).
Proof.
  destruct α. cbn. destruct e.
  unfold equiv_T_equiv_fun; cbn.
  assert ((T_rec (T g) (λ a : A, t a)
        (λ (a b : A) (p : g a = g b), tp a b ((1 @ p) @ 1))
        (λ a : A, 1 @ tp_1 a)) == idmap).
  { refine (path_T _ _ _ _ _ _).
    intro; reflexivity.
    intros a b p; cbn.
    refine (concat_1p _ @ _ @ (concat_p1 _)^).
    refine (_ @ (T_rec_beta_tp _ _ _ _ _ _ _)^).
    refine (ap_idmap _ @ _).
    apply ap.
    refine (_ @ (concat_p1 _)^). exact (concat_1p _)^.
    intro a; cbn.
    rewrite transport_paths_FlFr. cbn.
    rewrite ap_V. rewrite inv_V.
    rewrite concat_ap_pFq.
    rewrite concat_ap_Fpq.
    apply moveR_pV. 
    match goal with
    |[|- _ = ((?P1 @ _) @ ?P2) @ ?P3] =>
     rewrite (concat_p1 P1);
       rewrite (concat_pp_p (r:= P3))
    end.
    match goal with
    |[|- _ = _ @ (whiskerR ?hh 1 @ _) ]
     => pose (rew := whiskerR_p1 hh);
       rewrite concat_pp_p in rew;
       apply moveL_Vp in rew;
       rewrite rew; clear rew
    end.
    rewrite inv_V.
    apply moveR_Mp.
    match goal with
    |[|- _ = ?P1 @ ((whiskerL 1 ?hh) @ ?P3)] =>
     rewrite (concat_p_pp (p := P1));
       pose (rew := whiskerL_1p hh);
       apply moveL_pV in rew;
       rewrite rew; clear rew
    end. cbn.
    repeat rewrite concat_p1; repeat rewrite concat_1p.
    rewrite <- (apD (λ U, ap_idmap U) (tp_1 a)^).
    rewrite transport_paths_FlFr. cbn. rewrite ap_V. rewrite inv_V.
    rewrite concat_p1.
    repeat rewrite concat_pp_p. apply whiskerL.
    repeat rewrite ap_V.
    rewrite <- (ap02_is_ap _ _ (T_rec (T g) (λ a0 : A, t a0)
            (λ (a0 b : A) (p : g a0 = g b), tp a0 b ((1 @ p) @ 1))
            (λ a0 : A, 1 @ tp_1 a0))).
    rewrite T_rec_beta_tp_1.
    rewrite ap_idmap. rewrite (concat_1p (tp_1 a)).
    rewrite inv_pp.  reflexivity. }
  refine (isequiv_homotopic idmap  _).
  exact (λ x, (X x)^).
Defined.

Definition isequiv_T_equiv_fun `{ua: Univalence} {A B C:Type}
           (f: A -> B)
           (g: C -> B)
           (α: A <~> C)
           (e: g o α = f)
  : IsEquiv (equiv_T_equiv_fun f g α e).
Proof.
  assert ((equiv_T_equiv_fun f g α e) = (equiv_T_equiv_fun f g (equiv_path _ _ (path_universe_uncurried α)) ((ap (λ u, g o u) (ap (@equiv_fun A C) (equiv_path_path_universe_uncurried α))) @ e))).
  { cbn.
    pose (ap (@equiv_fun A C) (equiv_path_path_universe_uncurried α)).
    pose (apD (λ U, equiv_T_equiv_fun f g U) p^).
    cbn in p0. rewrite <- p0. cbn.
    rewrite transport_arrow. rewrite transport_const.
    apply ap.
    cbn. rewrite transport_paths_Fl. apply moveL_Vp.
    rewrite inv_V. reflexivity. }
  refine (isequiv_homotopic _ (λ x, ap10 X^ x)).
  exact (isequiv_T_equiv_fun_path f g ((path_universe_uncurried α)) (ap (λ (u : A → C) (x : A), g (u x))
                                                                       (ap (equiv_fun (B:=C)) (equiv_path_path_universe_uncurried α)) @ e)).
Qed.  

Lemma foobar `{ua: Univalence}  (A B:Type) (f: A -> B)
  : T f <~> {y:B & T (λ _:hfiber f y, tt)}.
Proof.
  etransitivity; [idtac | exact (bar B (hfiber f))].
  refine (BuildEquiv (isequiv_T_equiv_fun _ _ _ _)).
  refine (equiv_adjointify _ _ _ _).
  intro x; exact (f x; (x;1)).
  intros [y [x p]]. exact x.
  intros [y [x p]].
  destruct p; reflexivity.
  intro x; reflexivity.
  reflexivity.
Defined.

Definition G_simon  (A B:Type) (f: A -> B) : T f -> {y:B & T (λ _:hfiber f y, tt)}.
Proof.
  refine (T_rec _ _ _ _).
  - intro a. exact (f a ; (t (a; 1))).
  - intros a b p; cbn.
    refine (path_sigma' _ p _).
    etransitivity. refine (transport_T _ _).
      by apply tp.
  - intros a; cbn. exact (ap _ (ap _ (tp_1 _))).
Defined.

Definition KP_lift  (A B:Type) (f: A -> B) : T f -> B.
Proof.
  refine (T_rec _ _ _ _). exact f. intros a b; exact idmap.
  intro a; reflexivity.
Defined.

Lemma G_simon_eq `{ua: Univalence} (A B:Type) (f: A -> B) :
  (foobar A B f) == G_simon A B f.
Proof.
  intro x; cbn. unfold G_simon.
  revert x.
  refine (path_T _ _ _ _ _ _).
  - intro; reflexivity.
  - intros a b p; cbn.
    refine (concat_1p _ @ _ @ (concat_p1 _)^).
    unfold equiv_T_equiv_fun.
    match goal with
    |[|- _ = ap (λ x, ?gg (?ff x)) ?pp ] =>
     refine (_ @ (ap_compose ff gg pp)^);
       refine (_ @ (ap02 gg (T_rec_beta_tp _ _ _ _ _ _ _)^))
    end.
    refine (_ @ (T_rec_beta_tp _ _ _ _ _ _ _)^).    
    refine ((T_rec_beta_tp _ _ _ _ a b p) @ _).
    cbn.
    etransitivity.
    2: exact (apD (λ U, path_sigma' (λ y : B, T (λ _ : hfiber f y, tt)) 
                                    U
                                    (transport_T U (a; 1) @
                                                 tp (transport (λ y : B, hfiber f y) U (a; 1)) 
                                                 (b; 1) (path_ishprop tt tt))) (concat_p1 (1 @ p) @ (concat_1p p))^).
    refine (_ @ (transport_const _ _)^).
    apply ap.
    apply ap. apply ap. apply path_ishprop.
  - intro a; cbn.
    rewrite transport_paths_FlFr. cbn.
    do 2 rewrite concat_ap_pFq.
    match goal with
    |[|- (?P1 @ ?P2) @ ?P3 = (?P4^ @ _) @ _] =>
     rewrite (concat_p1 P4^);
       apply moveL_Vp;
       rewrite (concat_pp_p (p := P1));
       rewrite (concat_p_pp (p := P4))
    end.
    match goal with
    |[|- (whiskerL 1 ?hh @ _) @ _ = _] =>
     pose (rew := whiskerL_1p hh);
       rewrite concat_pp_p in rew; apply moveL_Vp in rew;
       rewrite rew; clear rew
    end.
    rewrite inv_V.
    rewrite concat_ap_Fpq.
    match goal with
    |[|- ?P1 @ (?P2 @ ?P3^) = _ ]
     => rewrite (concat_p_pp (r := P3^));
       apply moveR_pV
    end.
    match goal with
    |[|- _ = whiskerR ?hh 1 @ _] =>
     pose (rew := whiskerR_p1 hh);
       rewrite concat_pp_p in rew; apply moveL_Vp in rew;
       rewrite rew; clear rew
    end.
    rewrite inv_V.
    match goal with
    |[|- _ = _ @ ap (ap (λ x, ?gg (?ff x))) ?pp] =>
     rewrite <- (ap02_is_ap _ _ (gg o ff) _ _ _ _ pp);
       rewrite (ap02_compose _ _ _ ff gg _ _ _ _ pp)
    end. cbn.
    match goal with
    |[|- ?P1 @ (?P2 @ ?P3^) = 1 @ (1 @ (?P5 @ ?P6))]
     => rewrite (concat_1p (1 @ (P5 @ P6)));
       rewrite (concat_1p (P5 @ P6));
       rewrite (concat_p_pp (r:=P3^)) 
    end.
    apply whiskerR.
    unfold equiv_T_equiv_fun.
    repeat rewrite ap02_V.
    rewrite (T_rec_beta_tp_1). cbn.
    rewrite (ap02_pp). rewrite inv_pp.
    match goal with
    |[|- (_ @ ?P1) @ (?P2 @ ?P3) = _] =>
     rewrite (concat_p_pp (r:=P3));
       rewrite (concat_1p P1)
    end.
    apply whiskerR.
    rewrite ap02_pp. cbn.
    match goal with |[|- _ = (_ @ ?P)^] => rewrite (concat_1p P) end.
    rewrite <- ap02_is_ap.
    match goal with
    |[|- _ = (ap02 (T_rec ?P1 ?P2 ?P3 ?P4) (tp_1 ?aa))^] =>
     rewrite (T_rec_beta_tp_1 P1 P2 P3 P4 aa)
    end.
    rewrite inv_pp. cbn.
    rewrite concat_p_pp. apply whiskerR.
    match goal with
    |[|- ap (ap ?ff) ?pp @ _ = _] =>
     rewrite <- (ap02_is_ap _ _ ff _ _ _ _ pp);
       rewrite ap02_V
    end.
    rewrite (T_rec_beta_tp_1).
    rewrite inv_pp. rewrite concat_p_pp. rewrite concat_pV_p.
    repeat rewrite <- ap02_is_ap.
    do 3 rewrite concat_p1.
    rewrite <- (ap02_V _ _ (exist (λ y : B, T (λ _ : hfiber f y, tt)) (f a)) _ _ _ _ (ap (concat 1) (tp_1 (a; 1)))).
    match goal with
    |[|- ap02 ?ff ?pp @ ap02 _ ?qq = (ap02 ?hh ?rr)^] =>
     rewrite <- (ap02_pp ff pp qq);
       rewrite <- (ap02_V _ _ hh _ _ _ _ rr)
    end.
    apply ap.
    assert (r: 1 = path_ishprop tt tt) by apply path_ishprop.
    destruct r; cbn.
    assert (r: 1 = path_ishprop (idpath tt) 1) by apply path_ishprop.
    destruct r.
    rewrite ap_idmap. cbn. rewrite concat_p1. rewrite inv_pp.
    pose (p:= apD (λ U, (concat_1p U)^) (tp_1 (f:=(λ _ : hfiber f (f a), tt)) (a;1))^).
    cbn in p; rewrite <- p; clear p.
    rewrite transport_paths_FlFr.
    rewrite ap_idmap. cbn.
    rewrite concat_p1. rewrite inv_V. rewrite concat_V_pp.
    rewrite ap_V.
    reflexivity.
Defined.


    
End Foo.