Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness Types.Record.
Require Import equivalence.

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

  Definition transport_is_colimit' G (D1 D2:diagram G)
             (path_type : forall i, (diagram0 D1 i) <~> (diagram0 D2 i))
             (path_comm : forall (i j:G), forall f:G i j, (diagram1 D1 f) o (path_type i)^-1 = (path_type j)^-1 o (diagram1 D2 f) )
             (P : Type)
             (q1:forall i, D1 i -> P)
             (pp_q1 : forall (i j:G) (f: G i j), (q1 j) o (diagram1 D1 f) == q1 i)
             (q2:forall i, D2 i -> P)
             (pp_q2 : forall (i j:G) (f: G i j), (q2 j) o (diagram1 D2 f) == q2 i)
             (Hq : forall i, (q1 i) o (path_type i)^-1 = q2 i)
             (Hpp_q : forall (i j:G) (f:G i j),
                        (Hq i)^ @
                                  ((ap (λ (u : D1 i → P) (x : D2 i), u ((path_type i)^-1 x))
                                       (path_forall _ _ (pp_q1 i j f)))^ @
                                                         ap (λ (u : D2 i → D1 j) (x : D2 i), q1 j (u x)) (path_comm i j f))
                        =
                        (path_forall _ _ (pp_q2 i j f))^ @
                                         (ap (λ (u : D2 j → P) (x : D2 i), u (diagram1 D2 f x)) (Hq j))^)
                            
             
  : is_colimit G D1 P q1 pp_q1 -> is_colimit G D2 P q2 pp_q2.
    intros H X. specialize (H X). destruct H as [inv retr sect _].
    refine (isequiv_adjointify _ _ _ _).
    - intros [f pp] p.
      apply inv.
      refine (exist _ _ _).
      intros i d1.
      apply (f i).
      apply (path_type i).
      exact d1.
      intros i j g x. simpl.
      etransitivity; try exact (pp i j g ((path_type i) x)).
      apply ap.
      apply (@equiv_inj _ _ (path_type j)^-1 _).
      etransitivity; [idtac | exact (ap10 (ap (λ u:D2 i → D1 j, u o (path_type i)) (path_comm i j g)) x)].
      etransitivity; try exact (eissect (path_type j) (diagram1 D1 g x)).
      apply ap.
      symmetry. apply eissect.
      exact p.
    - intros [f pp].
      refine (path_sigma' _ _ _). simpl.
      apply path_forall; intro i.
      apply path_forall; intro x. simpl.
      unfold Sect in *; simpl in *.
Abort.

  Definition transport_colimit (G:graph) (D1 D2:diagram G) (eq : D1=D2)
  : colimit D1 = colimit D2.
    destruct eq. reflexivity.
  Qed.

  Lemma path_colimit_is_colimit (G:graph) (D:diagram G) 
          (q : forall i, D i -> colimit D)
          (pp_q : forall (i j:G) (f: G i j) (x: D i), q _ (diagram1 D f x) = q _ x)
          (p_q : (@colim G D) = q)
          (p_pp : transport (λ U, forall (i j:G) (f: G i j) (x: D i), U _ (diagram1 D f x) = U _ x) p_q (@pp G D) =  pp_q)
  : is_colimit G D (colimit D) q pp_q.
    destruct p_q.
    simpl.
    destruct p_pp.
    simpl.
    apply colimit_is_colimit.
  Qed.

  Lemma path_path_colimit_is_colimit (G:graph) (D:diagram G) (P:Type)
        (eq : colimit D = P)
        (μ := equiv_path _ _ eq^)
        (ν := equiv_path _ _ eq)
        (q : forall i, D i -> P)
        (pp_q : forall (i j:G) (f: G i j) (x: D i), q _ (diagram1 D f x) = q _ x)
        (p_q : (λ i, (equiv_path _ _ eq) o (@colim G D i)) = q)
        (p_pp : transport
                  (λ U : ∀ x : G, D x → P,
                     ∀ (i j : G) (f : G i j) (x : D i), U j (diagram1 D f x) = U i x)
                  p_q
                  (λ (i j : G) (f : G i j) (x : D i),
                   ap (transport idmap eq) (pp G D i j f x)) = pp_q)
  : is_colimit G D P q pp_q.
    destruct eq. simpl in *.
    destruct p_q. simpl in *.
    destruct p_pp. simpl in *.
    refine (path_colimit_is_colimit _ _ _ _ _ _).
    reflexivity.
    simpl.
    apply path_forall; intro i. apply path_forall; intro j. apply path_forall; intro f.     apply path_forall; intro x.
    unfold transport.
    symmetry; apply ap_idmap.
  Qed.
                   
  Definition transport_is_colimit (G:graph) (D1 D2:diagram G)
             (eq : D1 = D2)
             (P:Type)
             (q1:forall i, D1 i -> P)
             (pp_q1 : forall (i j:G) (f: G i j) (x: D1 i), q1 _ (diagram1 D1 f x) = q1 _ x)
             (q2:forall i, D2 i -> P)
             (pp_q2 : forall (i j:G) (f: G i j) (x: D2 i), q2 _ (diagram1 D2 f x) = q2 _ x)
             (H : is_colimit G D1 P q1 pp_q1)
             (Hq : transport (λ U:diagram G, forall i, U i -> P) eq q1 = q2)
             (Hpp : match
           eq as p in (_ = y)
           return
             (∀ q0 : ∀ i : G, y i → P,
              (∀ (i j : G) (f : G i j) (x : y i),
               q0 j (diagram1 y f x) = q0 i x)
              → transport (λ U : diagram G, ∀ i : G, U i → P) p q1 = q0
                → ∀ (i j : G) (f : G i j) (x : y i),
                  q0 j (diagram1 y f x) = q0 i x)
         with
         | 1 =>
             λ (q0 : ∀ i : G, D1 i → P)
             (pp_q0 : ∀ (i j : G) (f : G i j) (x : D1 i),
                      q0 j (diagram1 D1 f x) = q0 i x) 
             (Hq0 : q1 = q0),
             match
               Hq0 in (_ = y)
               return
                 ((∀ (i j : G) (f : G i j) (x : D1 i),
                   y j (diagram1 D1 f x) = y i x)
                  → ∀ (i j : G) (f : G i j) (x : D1 i),
                    y j (diagram1 D1 f x) = y i x)
             with
             | 1 =>
                 λ
                 _ : ∀ (i j : G) (f : G i j) (x : D1 i),
                     q1 j (diagram1 D1 f x) = q1 i x, pp_q1
             end pp_q0
         end q2 pp_q2 Hq = pp_q2)
  : is_colimit G D2 P q2 pp_q2.
    destruct eq. destruct Hq. destruct Hpp. exact H.
  Defined.
  
End colimit_universal_property.

