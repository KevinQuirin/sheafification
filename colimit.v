Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness Types.Record.


Set Universe Polymorphism.
Global Set Primitive Projections.

Section Diagram.

  (* From Peter Lumsdaine *)
  Record graph :=
    { graph0 :> Type;
      graph1 :> graph0 -> graph0 -> Type }.

  Record diagram (G : graph) :=
    { diagram0 :> G -> Type;
      diagram1 : forall (i j : G), G i j -> (diagram0 i -> diagram0 j) }.
  
  Global Arguments diagram0 [G] D i : rename.
  Global Arguments diagram1 [G] D [i j] f x : rename.
  
  (* Notation "D .1" := (@diagram1 _ D _ _) (at level 3). *)

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
    
End colimit_universal_property.

