Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness Types.Record.
Require Import equivalence lemmas.

Set Universe Polymorphism.
Global Set Primitive Projections.

Local Open Scope path_scope.

Section Diagram.

  (* From https://github.com/peterlefanulumsdaine/hott-limits *)
  (* Definition 5 *)
  Record graph :=
    { graph0 :> Type;
      graph1 :> graph0 -> graph0 -> Type }.

  Record diagram (G : graph) :=
    { diagram0 :> G -> Type;
      diagram1 : forall (i j : G), G i j -> (diagram0 i -> diagram0 j) }.
  
  Global Arguments diagram0 [G] D i : rename.
  Global Arguments diagram1 [G] D [i j] f x : rename.
  
  Context `{fs : Funext}.
  Context `{ua : Univalence}.
  
  Lemma path_diagram (G:graph) (D1 D2: diagram G)
  : {path_type : (diagram0 D1) = (diagram0 D2) 
    & forall (i j:G), forall x:G i j, diagram1 D1 x == (equiv_path _ _ (ap10 path_type j)^) o (diagram1 D2 x) o (equiv_path _ _ (ap10 path_type i)) }
    -> D1 = D2.
  Proof.
    intros [path_type path_map].
    destruct D1 as [T1 m1], D2 as [T2 m2]; simpl in *.
    destruct path_type. simpl in path_map.
    assert (p : m1 = m2).

    apply path_forall; intro i.
    apply path_forall; intro j.
    apply path_forall; intro x.
    apply path_forall; intro X.
    exact (path_map i j x X).
    destruct p.
    reflexivity.
  Defined.
  
End Diagram.

(* In this module is the higher inductive definition of colimits *)
Module Export colimit_HIT.

  Private Inductive colimit {G:graph} (D : diagram G) : Type:=
    colim : forall i, (D i -> colimit D).

  Global Arguments colim {G D} {i} x.
  
  Axiom pp : forall (G:graph) (D:diagram G), forall i j:G, forall (f : G i j),
               forall (x:D i), colim (diagram1 D f x) = colim x.

  Definition colimit_rect (G:graph) (D: diagram G) (P : colimit D -> Type)
             (q : forall {i}, forall x, P (colim x))
             (pp_q : forall (i j:G) (f : G i j) (x:D i), (@pp G D i j f x) # (q (diagram1 D f x)) = q x)
  : forall w, P w
    := fun w => match w with colim i a => fun _ => q a end pp_q.

  Axiom colimit_rect_beta_pp
  : forall (G:graph) (D: diagram G) (P : colimit D -> Type)
           (q : forall i, forall x, P (colim x))
           (pp_q : forall (i j:G) (f : G i j) (x:D i), (@pp G D i j f x) # (q _ (diagram1 D f x)) = q _ x)
           (i j:G) (f: G i j) (x: D i),
      apD (@colimit_rect G D P q pp_q) (@pp G D i j f x) = pp_q i j f x.

  Definition colimit_rect_compute (G:graph) (D: diagram G) (P : colimit D -> Type)
             (q : forall {i}, forall x, P (colim x))
             (pp_q : forall (i j:G) (f : G i j) (x:D i), (@pp G D i j f x) # (q (diagram1 D f x)) = q x) i (x:D i)
  : colimit_rect G D P (@q) pp_q (@colim _ _ i x) = q x.
    reflexivity.
  Defined.
  
End colimit_HIT.

Section colimit_nondep.

  Definition colimit_rectnd (G : graph) (D:diagram G) (P:Type)
             (q:forall i, D i -> P)
             (pp_q : forall (i j:G) (f: G i j) (x: D i), q _ (diagram1 D f x) = q _ x)
  : colimit D -> P.
    refine (colimit_rect G D _ _ _).
    - exact q.
    - intros i j f x.
      exact ((transport_const (pp G D i j f x) (q _ (diagram1 D f x))) @ (pp_q i j f x)).
  Defined.

  Definition colimit_rectnd_compute (G : graph) (D:diagram G) (P:Type)
             (q:forall i, D i -> P)
             (pp_q : forall (i j:G) (f: G i j) (x: D i), q _ (diagram1 D f x) = q _ x)
             i (x:D i)
  : colimit_rectnd G D P (@q) pp_q (@colim _ _ i x) = @q i x.
    reflexivity.
  Defined.
  
  Definition colimit_rectnd_beta_pp (G:graph) (D:diagram G) (P:Type)
             (q:forall i, D i -> P)
             (pp_q : forall (i j:G) (f: G i j) (x: D i), q _ (diagram1 D f x) = q _ x)
             (i j:G) (f: G i j) (x: D i)
  : ap (colimit_rectnd G D P q pp_q) (@pp G D i j f x) = pp_q i j f x.
    unfold colimit_rectnd.
    eapply (cancelL (transport_const (pp G D i j f x) _)).
    refine ((apD_const (colimit_rect G D (λ _ : colimit D, P) q _) (pp G D i j f x))^ @ _).
    refine (colimit_rect_beta_pp G D (λ _, P) q _ i j f x).
  Defined.
  
End colimit_nondep.

Section colimit_universal_property.

  Context `{fs : Funext}.

  (* Definition 6*)
  Definition is_colimit (G:graph) (D:diagram G) (P:Type)
             (q:forall i, D i -> P)
             (pp_q : forall (i j:G) (f: G i j) (x: D i), q _ (diagram1 D f x) = q _ x)
             
    := forall X:Type,
         IsEquiv (λ f : P -> X,
                        (existT (λ qq : forall i, D i -> X, forall (i j:G) (f: G i j) (x: D i), qq j (diagram1 D f x) = qq i x)
                                       (λ i, λ x, f (q i x))
                                       ( λ i j g x, ap f (pp_q i j g x)))).

  Theorem colimit_is_colimit (G:graph) (D:diagram G) 
  : is_colimit G D (colimit D) (@colim G D) (@pp G D).
    intro Y; simpl.
    refine (isequiv_adjointify _ _ _ _).
    - intros [q pp_q].
      apply (colimit_rectnd G D Y q pp_q).
    - intros [q pp_q]. simpl.
      refine (path_sigma' _ _ _).
      reflexivity.
      simpl.
      repeat (apply path_forall; intro).
      apply colimit_rectnd_beta_pp.
    - intro φ. simpl.
      apply path_forall. refine (colimit_rect _ _ _ _ _).
      intros i x. reflexivity.
      intros i j f x. simpl.
      rewrite transport_paths_FlFr.
      rewrite colimit_rectnd_beta_pp. hott_simpl.
  Qed.

  Definition colimit_equiv (G:graph) (D:diagram G)
    := λ X, BuildEquiv _ _ _ (colimit_is_colimit G D X).

  Definition transport_is_colimit `{ua : Univalence} (G:graph) (D1 D2:diagram G)
             (path_type : forall i, diagram0 D1 i <~> diagram0 D2 i)
             (path_comm : forall (i j:G), forall x:G i j, diagram1 D1 x == (path_type j)^-1 o (diagram1 D2 x) o (path_type i))
             (P:Type)
             (q1:forall i, D1 i -> P)
             (pp_q1 : forall (i j:G) (f: G i j) (x: D1 i), q1 _ (diagram1 D1 f x) = q1 _ x)
             (q2:forall i, D2 i -> P)
             (pp_q2 : forall (i j:G) (f: G i j) (x: D2 i), q2 _ (diagram1 D2 f x) = q2 _ x)
             (Hq : (λ i, (q1 i) o (path_type i)^-1) = q2)
             (Hpp : (λ (i j : G) (f : G i j) (x : D1 i),
                     ap (q1 j) (path_comm i j f x) @
                        (apD10 (apD10 Hq j)
                               (diagram1 D2 f (path_type i x)) @
                               (pp_q2 i j f (path_type i x) @
                                      ((apD10 (apD10 Hq i) (path_type i x))^ @ ap (q1 i) (eissect (path_type i) x))))) = pp_q1)
             (H : is_colimit G D1 P q1 pp_q1)
  : is_colimit G D2 P q2 pp_q2.
    destruct Hq.
    destruct Hpp.
    simpl in *.    
    intros X. specialize (H X); destruct H as [inv retr sect _].
    unfold Sect in *; simpl in *.
    refine (isequiv_adjointify _ _ _ _).
    - intros [x1 x2]. apply inv.
      refine (exist _ _ _).
      intros i y. apply (x1 i).
      apply (path_type i). exact y.
      intros i j f x.
      simpl.
      specialize (x2 i j f (path_type i x)).
      etransitivity; [idtac | exact x2].
      apply ap.
      pose (path_comm i j f x). simpl in p.
      path_via ((path_type j) ((path_type j)^-1 (diagram1 D2 f (path_type i x)))).
      apply ap. exact p.
      simpl.
      apply (eisretr (path_type j)).
    - intros [x1 x2].
      simpl.
      transparent assert (foo : ( ∃ qq : ∀ i : G, D1 i → X,
                                    ∀ (i j : G) (f : G i j) (x : D1 i),
                                      qq j (diagram1 D1 f x) = qq i x)).
      { refine (exist _ _ _).
        exact (λ (i0 : G) (y : D1 i0), x1 i0 (path_type i0 y)).
        exact (λ (i0 j : G) (f : G i0 j) (x0 : D1 i0),
               ap (x1 j)
                  (ap (path_type j) (path_comm i0 j f x0) @
                      eisretr (path_type j)
                      (diagram1 D2 f (path_type i0 x0))) @
                  x2 i0 j f (path_type i0 x0)). }
      specialize (retr foo).
      unfold foo in *; clear foo. simpl in *.
      refine (path_sigma' _ _ _).
      { apply path_forall; intro i. apply path_forall; intro x.
        apply pr1_path in retr. simpl in retr.
        
        pose (apD10 (apD10 retr i) ((path_type i)^-1 x)). simpl in p.
        etransitivity; try exact p.
        apply ap.
        apply (eisretr (path_type i)). }
      simpl.
      apply path_forall; intro i.
      apply path_forall; intro j.
      apply path_forall; intro f.
      apply path_forall; intro x.
      repeat rewrite transport_forall_constant.
      rewrite transport_paths_FlFr. simpl.
      assert (r:= retr..2). simpl in r.
      apply apD10 in r; specialize (r i).
      apply apD10 in r; specialize (r j).
      apply apD10 in r; specialize (r f). 
      apply apD10 in r; specialize (r ((path_type i)^-1 x)).
      repeat rewrite transport_forall_constant in r.
      rewrite transport_paths_FlFr in r.
      apply moveR_Vp in r. simpl in r.
      repeat rewrite concat_pp_p.
      match goal with
        |[|- (ap _ (path_forall ?ff ?gg _))^ @ _ = _] => set (u := ff); set (v := gg)
      end.
      pose (@ap_ap2_path_forall fs
                                G
                                (λ x, D2 x)
                                (λ u v, X)
                                u v
                                (λ i0, λ x0 : D2 i0,
                                        apD10 (apD10 retr ..1 i0)
                                              ((path_type i0)^-1 x0) @
                                              ap (v i0) (eisretr (path_type i0) x0))
                                ). simpl in p.
      unfold u, v in *; clear u; clear v.
      rewrite p. rewrite p. clear p.
      etransitivity; [idtac | exact (apD (x2 i j f) (eisretr (path_type i) x))].
      apply (@equiv_inj _ _ (transport (λ x0 : D2 i, x1 j (diagram1 D2 f x0) = x1 i x0)
                                       (eisretr (path_type i) x)^) (isequiv_transport (λ x0 : D2 i, x1 j (diagram1 D2 f x0) = x1 i x0) _ _ (eisretr (path_type i) x)^)).
      rewrite transport_Vp.
      etransitivity; [idtac | exact r].
      clear r.
      rewrite transport_paths_FlFr.
      rewrite ap_V. rewrite inv_V. hott_simpl.
      simpl.
      rewrite ap_V; apply moveR_pV; apply whiskerR.
      match goal with
        |[|- _ @ ?xx = _ @ ?yy] => set (foo := xx); set (bar := yy)
      end.
      simpl in foo, bar.
      assert (rew : foo = bar).
      { unfold foo, bar. simpl.
        rewrite (ap_compose (λ f, f i) (λ f, f ((path_type i)^-1 x)) (retr..1)).
        reflexivity. }
      destruct rew; apply whiskerR; clear foo.
      
      match goal with
        |[|- _ @ ap ?ff _ = _] => set (foo := ff) in *
      end.

      apply moveR_pM. repeat rewrite concat_pp_p. rewrite ap_V.
      apply moveL_Vp. apply moveL_Vp.
      rewrite <- ap_V.
      rewrite <- ap_pp.
      rewrite inv_pp. simpl.
      assert (X0 : ((ap (q1 j) (path_comm i j f ((path_type i)^-1 x)) @
       (pp_q2 i j f ((path_type i) ((path_type i)^-1 x)) @
        ap (q1 i) (eissect (path_type i) ((path_type i)^-1 x)))) @
      (pp_q2 i j f x)^) = (ap (q1 j)
          (path_comm i j f ((path_type i)^-1 x) @
           ap ((path_type j)^-1)
           (ap (diagram1 D2 f) (eisretr (path_type i) x))))).
      { rewrite ap_pp. rewrite concat_pp_p. apply whiskerL.
        apply moveR_pV.
        simpl.
        pose (apD (λ U, pp_q2 i j f U) (eisretr (path_type i) x)^). simpl in p.
        rewrite <- p; clear p.
        rewrite transport_paths_FlFr. simpl.
        rewrite ap_V. rewrite inv_V. simpl.
        assert (X0 : (ap (λ x0 : D2 i, q1 i ((path_type i)^-1 x0))
       (eisretr (path_type i) x)^ @
     ap (q1 i)
       (eissect (path_type i)
                     ((path_type i)^-1 x))) = 1).
        { rewrite ap_compose. rewrite <- ap_pp.
          assert (X0 : (ap ((path_type i)^-1)
        (eisretr (path_type i) x)^ @
      eissect (path_type i)
      ((path_type i)^-1 x)) = 1).
          { rewrite ap_V. apply moveR_Vp. hott_simpl.
            apply (other_adj (path_type i)). }
          rewrite X0; clear X0. reflexivity. }
        repeat rewrite concat_pp_p. 
        apply moveR_Mp. 
        rewrite X0; clear X0. rewrite concat_p1.
        path_via (1 @ pp_q2 i j f x).
        rewrite concat_p_pp. apply whiskerR.
        apply moveL_Vp. rewrite concat_p1.
        rewrite ap_compose. apply ap.
        rewrite ap_compose. reflexivity. }
      rewrite X0; clear X0.
      rewrite <- ap_compose.
      etransitivity; try exact (apD (λ u, ap u
     (path_comm i j f ((path_type i)^-1 x) @
      ap ((path_type j)^-1)
      (ap (diagram1 D2 f) (eisretr (path_type i) x)))) (apD10 retr..1 j)^).
      rewrite transport_paths_FlFr. simpl.
      
      assert (X0 : (apD10 (apD10 retr ..1 j)
                   ((path_type j)^-1 (diagram1 D2 f x)))^ = (ap
     (λ x0 : D1 j → X,
      x0 ((path_type j)^-1 (diagram1 D2 f x)))
     (apD10 retr ..1 j)^)).
      { destruct retr..1. reflexivity. }
      rewrite X0; clear X0. repeat rewrite concat_p_pp. apply whiskerR.
      simpl.

      rewrite ap_V. rewrite inv_V.
      assert (X0 : (ap
     (λ x0 : D1 j → X,
      x0 (diagram1 D1 f ((path_type i)^-1 x)))
     (apD10 retr ..1 j)) = (ap
       (λ x0 : ∀ i0 : G, D1 i0 → X,
        x0 j (diagram1 D1 f ((path_type i)^-1 x)))
       retr ..1)).
      { destruct retr..1. reflexivity. }
      rewrite X0; clear X0.
      repeat rewrite concat_pp_p. apply whiskerL.
      repeat rewrite ap_pp.
      assert (X0 : (ap (x1 j)
      (ap (path_type j)
          (path_comm i j f ((path_type i)^-1 x)))) = (ap (λ y : D1 j, x1 j (path_type j y))
                                                                            (path_comm i j f ((path_type i)^-1 x)))).
      { destruct (path_comm i j f ((path_type i)^-1 x)). reflexivity. }
      rewrite X0; clear X0. repeat rewrite concat_pp_p. apply whiskerL.
      destruct (eisretr (path_type i) x). hott_simpl.
      rewrite ap_V. apply concat_pV.
    - intros φ.
      specialize (sect φ).
      etransitivity; try exact sect.
      apply ap.
      simpl.
      refine (path_sigma' _ _ _).
      { simpl.
        apply path_forall; intro i. apply path_forall; intro y.
        repeat apply ap. apply eissect. }
      apply path_forall; intro i.
      apply path_forall; intro j.
      apply path_forall; intro f.
      apply path_forall; intro x.
      repeat rewrite transport_forall_constant.
      rewrite transport_paths_FlFr. simpl.
      hott_simpl.
      repeat rewrite ap_pp. simpl.
      clear retr; clear sect. clear inv.
      repeat rewrite (@ap_ap2_path_forall fs G
                                (λ x, D1 x)
                                (λ u v, X)
                                (λ (i0 : G) (y : D1 i0), φ
                                                           (q1 i0
                                                               ((path_type i0)^-1
                                                                (path_type i0 y))))
                                (λ (i0 : G) (x0 : D1 i0), φ (q1 i0 x0))
                                (λ i0, λ y : D1 i0, ap φ (ap (q1 i0) (eissect (path_type i0) y)))). 
      repeat apply whiskerR.
      apply moveR_Vp.
      rewrite <- ap_pp. rewrite <- ap_pp. rewrite <- (ap_pp (λ x0 : D2 j, φ (q1 j ((path_type j)^-1 x0)))).
      simpl.
      rewrite ap_compose; apply ap.
      rewrite ap_compose. apply ap.
      rewrite ap_pp.
      rewrite <- (other_adj (path_type j)).
      pose (other_adj (path_type j)).
      destruct (path_comm i j f x). simpl.
      hott_simpl.
  Defined.
  
End colimit_universal_property.

