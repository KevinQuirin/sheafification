Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import coequalizers.


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
  

  Notation "D .1" := (@diagram1 _ D _ _) (at level 3).
  
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

