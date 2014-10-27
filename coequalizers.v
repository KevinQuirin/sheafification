Require Export Utf8_core.
Require Import HoTT TruncType.
Require Import Types.Forall.
(* Require Import hit.Connectedness hit.minus1Trunc. *)
(* Require Import univalence lemmas epi_mono. *)

Set Universe Polymorphism.
Global Set Primitive Projections.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

Module Export Coequalizer.
  
  Private Inductive coequalizer {A B:Type} (f g : A -> B) : Type :=
| coeq : B -> coequalizer f g.

  Arguments coeq {A B f g} b.
  
  Definition coeql {A B:Type} {f g:A -> B} (a:A) : coequalizer f g
    := coeq (f a).

  Definition coeqr {A B:Type} {f g:A -> B} (a:A) : coequalizer f g
    := coeq (g a).

  Axiom path_coeq : forall {A B:Type} {f g: A -> B} (a:A), @coeql A B f g a = coeqr a.

  Definition coequalizer_rect {A B} (f g: A -> B) (P : coequalizer f g -> Type)
             (coeq' : forall b : B, P (coeq b))
             (path_coeq' : forall a : A, (@path_coeq A B f g a) # (coeq' ((f a))) = coeq' ((g a)))
  : forall w, P w
    := fun w => match w with coeq a => fun _ => coeq' a end path_coeq'.

  Definition coequalizer_rect_compute {A B} (f g: A -> B) (P : coequalizer f g -> Type)
             (coeq' : forall b : B, P (coeq b))
             (path_coeq' : forall a : A, (@path_coeq A B f g a) # (coeq' ((f a))) = coeq' ((g a)))
             x
  : coequalizer_rect f g P coeq' path_coeq' (coeq x) = coeq' x.
  Proof.
    reflexivity.
  Defined.

  Axiom coequalizer_rect_beta_pp
  : forall {A B f g} (P : @coequalizer A B f g -> Type)
           (coeq' : forall b : B, P (coeq b))
           (path_coeq' : forall a : A, (@path_coeq A B f g a) # (coeq' ((f a))) = coeq' ((g a)))
           (a : A),
      apD (@coequalizer_rect _ _ f g P coeq' path_coeq') (path_coeq a) = path_coeq' a.
End Coequalizer.

Definition coequalizer_rect2 {A B} (f g: A -> B)
           (P : coequalizer f g -> coequalizer f g -> Type)
           (coeq' : forall b c: B, P (coeq b) (coeq c))
           (path_coeq1' : forall w, forall a : A, transport (λ U, P _ U) (@path_coeq A B f g a) (coeq' w (f a)) = coeq' w (g a))
           (path_coeq3' : forall w, forall a : A, transport (λ U, P U _) (@path_coeq A B f g a) (coeq' (f a) w) = coeq' (g a) w)
: forall v w, P v w.
  intro v.
  refine (coequalizer_rect f g _ _ _).
  { intro b.
    generalize dependent v.
    refine (coequalizer_rect f g _ _ _).
    { exact (λ c, coeq' c b). }

    intro a. apply path_coeq3'.
  }
  
  { intro a. simpl.
    generalize dependent v.
    refine (coequalizer_rect _ _ _ _ _).
    {
      intro b.
      rewrite coequalizer_rect_compute.
      rewrite coequalizer_rect_compute.
      apply path_coeq1'.
    }

    intro b. simpl.
    pose (p := @transport_paths_FlFr_D).
    specialize (p (coequalizer f g)
                  _
                  (λ w : coequalizer f g,
                         transport (P w) (path_coeq a)
                                   (coequalizer_rect f g (λ w0 : coequalizer f g, P w0 (coeq (f a)))
                                                     (λ c : B, coeq' c (f a)) (λ a0 : A, path_coeq3' (f a) a0) w))
               (λ w, coequalizer_rect f g (λ w0 : coequalizer f g, P w0 (coeq (g a)))
        (λ c : B, coeq' c (g a)) (λ a0 : A, path_coeq3' (g a) a0) w)
               _
               _
               (path_coeq b) (path_coeq1' (f b) a)).
    simpl in p.
    rewrite p; clear p.
    pose (p := coequalizer_rect_beta_pp (λ w0 : coequalizer f g, P w0 (coeq (g a))) (λ c : B, coeq' c (g a)) (λ a0 : A, path_coeq3' (g a) a0) b). simpl in p.
    apply (transport (λ U, _ @ U = _) p^). clear p.
    pose (λ w, (coequalizer_rect f g (λ w0 : coequalizer f g, P w0 (coeq (f a)))
             (λ c : B, coeq' c (f a)) (λ a0 : A, path_coeq3' (f a) a0) w)). simpl in p.
    admit. }
Qed.
    
Definition coequalizer_rectnd {A B:Type} {f g:A -> B} (P:Type) (coeq' : B -> P) (pp' : forall a:A, coeq' (f a) = coeq' (g a))
: @coequalizer A B f g -> P
  := coequalizer_rect f g (λ _, P) coeq' (λ a, (transport_const (path_coeq a) (coeq' (f a))) @ (pp' a)).

Definition coequalizer_rectnd_compute {A B:Type} {f g:A -> B} (P:Type) (coeq' : B -> P) (pp' : forall a:A, coeq' (f a) = coeq' (g a)) (x:B)
: coequalizer_rectnd P coeq' pp' (coeq x) = coeq' x.
Proof. reflexivity. Defined.

Definition coequalizer_rectnd_beta_pp {A B:Type} {f g:A -> B} (P:Type) (coeq' : B -> P) (pp' : forall a:A, coeq' (f a) = coeq' (g a)) (a:A)
: ap (coequalizer_rectnd P coeq' pp') (path_coeq a) = pp' a.
  unfold coequalizer_rectnd.
  eapply (cancelL (transport_const (path_coeq a) _)).
  refine ((apD_const (@coequalizer_rect A B f g (fun _ => P) coeq' _) (path_coeq a))^ @ _).
  refine (coequalizer_rect_beta_pp (λ _, P) coeq' (λ a, (transport_const (path_coeq a) (coeq' (f a))) @ (pp' a)) a).
Defined.

Section Coequalizer_universal_property.

  Context `{fs : Funext}.

  Definition is_coequalizer {A B} {f g : A -> B} {X} (coequalizer : {m : B -> X & m o f =  m o g}) :=
    forall Y, IsEquiv (fun x : X -> Y => 
                         existT (fun m => m o f =  m o g) (x o pr1 coequalizer) (ap (fun u => x o u) (pr2 coequalizer))).

  Theorem coequalizer_is_coequalizer A B (f g : A -> B)
  : @is_coequalizer A B f g (coequalizer f g) ((coeq (f:=f) (g:=g)); path_forall _ _ (@path_coeq A B f g)).
    intro Y. simpl.
    apply @isequiv_adjointify with (g := λ m, (@coequalizer_rectnd A B f g Y m.1 (ap10 m.2))).
    - intros [m p]. simpl.
      apply @path_sigma' with (p := path_forall _ _ (coequalizer_rect_compute f g (λ _ : coequalizer f g, Y) m (λ a : A, transport_const (path_coeq a) (m (f a)) @ ap10 p a))).

      simpl.
      unfold coequalizer_rect_compute.
      rewrite path_forall_1. simpl. 
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv :=  isequiv_path_forall _ _))).
        apply isequiv_inverse. simpl.
      apply path_forall; intro x.
      rewrite (apD10_ap_postcompose (λ _, coequalizer_rectnd Y m (ap10 p)) (path_forall coeql coeqr path_coeq)).
      unfold ap10, path_forall; rewrite eisretr.
      apply coequalizer_rectnd_beta_pp.
    - intro φ. simpl.

      assert ((ap10
                 (ap (λ u : A → coequalizer f g, φ o u)
                     (path_forall coeql coeqr path_coeq))) = λ x, ap φ (path_coeq x)).

      apply path_forall; intro x. rewrite ap10_ap_postcompose. unfold ap10, path_forall; rewrite eisretr. exact 1.

      apply (transport (λ U, coequalizer_rectnd Y (φ o (coeq (f:=f) (g:=g))) U = φ) X^); clear X.
      (* unfold coequalizer_rectnd. *)

      apply path_forall. unfold pointwise_paths.

      refine (coequalizer_rect f g (λ x, _) _ _).
        intro b.
        reflexivity.

        intro a; simpl. 
        pose (rew := @transport_paths_FlFr (coequalizer f g) Y (coequalizer_rectnd Y (φ o coeq) (λ x0 : A, ap φ (path_coeq x0))) φ (coeql a) (coeqr a) (path_coeq a) 1).
        apply (transport (λ U, U=1) rew^); clear rew.
        rewrite (coequalizer_rectnd_beta_pp).
        hott_simpl.
  Qed.
  
End Coequalizer_universal_property.

Section CoequalizersTransport.

  Context `{fs : Funext}.

  Lemma coequalizer_transport_end
          (A B X Q:Type)
          (f g:A -> B)
          (pp : Q = X)
          (p := (equiv_path _ _ pp))
          (n : (∃ n : B → Q, n o f = n o g))
          (n_coeq : is_coequalizer n)
          (m : (∃ m : B → X, m o f = m o g))
          (mn_p : m.1 = p o n.1)
          (compat : transport (λ U, U o f = U o g) mn_p m.2 = ((ap (λ u, p o u) n.2)))
  : @is_coequalizer A B f g X m.
  Proof.
    destruct pp; simpl in *.
    assert (X : m=n).
      apply @path_sigma with (p := mn_p).
      rewrite ap_idmap in compat. exact compat.
    destruct X.
    exact n_coeq.
  Qed.

  Lemma coequalizer_transport_source_comm
        {A B X Q:Type}
        {f g:A -> B}
        {φ Ɣ:X -> B}
        (p : X <~> A)
        (m : (∃ m : B → Q, m o f = m o g))
        (eq1 : φ o p^-1 = f)
        (eq2 : Ɣ o p^-1 = g)
  : m.1 o φ = m.1 o Ɣ .
    destruct m as [m cm]; simpl in *.
    destruct p as [p ep]; destruct ep as [q retr sect adj]; simpl in *.
    apply path_forall; intro x.
    transitivity ((m o φ o q o p) x).
    unfold compose; simpl. repeat apply ap. exact (sect x)^.
    transitivity ((m o Ɣ o q o p) x).
    unfold compose; simpl. generalize (p x); intro y. 
    exact ((ap m (ap10 eq1 y)) @ (ap10 cm y) @ (ap m (ap10 eq2 y))^).

    unfold compose; simpl. repeat apply ap; apply sect.
  Defined.

    
  Lemma coequalizer_transport_source
        (A B X Q:Type)
        (f g:A -> B)
        (φ Ɣ:X -> B)
        (p : X <~> A)
        (* (m : (∃ m : B → Q, m o f = m o g)) *)
        (m : B -> Q)
        (cm : m o f = m o g)
        (m_coeq : is_coequalizer (m;cm))
        (eq1 : φ o p^-1 = f)
        (eq2 : Ɣ o p^-1 = g)
  : @is_coequalizer X B φ Ɣ Q (m; coequalizer_transport_source_comm p (m;cm) eq1 eq2).
    (* destruct m as [m cm]; simpl in *. *)
    pose (oadj := @other_adj _ _ p (equiv_isequiv p)).
    assert (Eq : IsEquiv p^-1) by apply isequiv_inverse.
    assert (Ep : IsEquiv p) by exact (equiv_isequiv p).
      
    destruct p as [p ep]; destruct ep as [q retr sect adj]; simpl in *.

    destruct eq1; destruct eq2. simpl in *.
    assert (rew : (λ x : X,
                   ap m (ap φ (sect x)^) @
                      (((1 @ ap10 cm (p x)) @ 1) @ ap m (ap Ɣ (sect x))))
            =
            (λ x : X,
                   (ap (m o φ) (sect x)^) @
                      ((ap10 cm (p x)) @ (ap (m o Ɣ) (sect x))))).
    apply path_forall; intro x; hott_simpl.
    repeat rewrite ap_compose; exact 1.
    apply (transport (λ U, is_coequalizer (m; path_forall _ _ U)) rew^); clear rew.

    intro Y. specialize (m_coeq Y).
    destruct m_coeq as [invc retrc sectc _]. simpl in *.

    apply @isequiv_adjointify with (g := λ n, invc (n.1; (ap (λ u, u o q) n.2))).

    - intros [n cn]. simpl. unfold Sect in retrc, sectc.
      specialize (retrc (n;(ap (λ u, u o q) cn))). simpl in *.
      apply @path_sigma' with (p:= retrc..1). simpl.
      
      assert (Eapq : IsEquiv (ap (x := n o φ) (y := n o Ɣ) (λ u : X → Y, u o q))) by
          apply (@isequiv_ap _ _ (λ u : X → Y, u o q) (isequiv_precompose q) (n o φ) (n o Ɣ)).

      apply (@equiv_inj _ _ _ Eapq).
      etransitivity; try exact retrc..2.
      simpl.

      pose (foo := @ap_transport (B -> Y)
                                 (λ m0 : B → Y, m0 o φ = m0 o Ɣ)
                                 (λ m0 : B → Y, m0 o (φ o q) = m0 o (Ɣ o q))
                                 (invc (n; ap (λ u : X → Y, u o q) cn) o m)
                                 n
                                 (retrc..1)
                                 (λ x, (ap (x := x o φ) (y := x o Ɣ) (λ u : X → Y, u o q)))
                                 (ap (λ u : X → Q, invc (n; ap (λ u0 : X → Y, u0 o q) cn) o u)
                                     (path_forall (m o φ) (m o Ɣ)
                                                  (λ x : X,
                                                         ap (m o φ) (sect x)^ @ (ap10 cm (p x) @ ap (m o Ɣ) (sect x)))))).
      etransitivity; try exact foo. clear foo.
      apply ap.

      set (foo := invc (n; ap (λ u0 : X → Y, u0 o q) cn)).

      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_path_forall _ _))).
        apply isequiv_inverse.
      apply path_forall; intro x.

      apply (transport (λ U, U = _) (ap10_ap_precompose q (ap (λ u : X → Q, foo o u)
           (path_forall (m o φ) (m o Ɣ)
              (λ x0 : X,
               ap (m o φ) (sect x0)^ @
               (ap10 cm (p x0) @ ap (m o Ɣ) (sect x0))))) x)^).
      rewrite ap10_ap_postcompose.

      unfold ap10 at 1, path_forall; rewrite eisretr.

      apply (transport (λ U, _ = U) (ap10_ap_postcompose foo cm x)^).
      apply ap.

      unfold Sect in *.

      repeat rewrite (oadj x). rewrite ap_V. repeat rewrite <- ap_compose.
      rewrite concat_p_pp.
      (* exact (@ap_conjug_ap10 A Q (m o φ o q) (m o Ɣ o q) (p o q) cm retr x). *)
      admit.
    - intro x. simpl. unfold Sect in retrc, sectc. specialize (sectc x).
      simpl.
      assert ((ap (λ u : X → Y, u o q)
       (ap (λ u : X → Q, x o u)
          (path_forall (m o φ) (m o Ɣ)
             (λ x0 : X,
              ap (m o φ) (sect x0)^ @ (ap10 cm (p x0) @ ap (m o Ɣ) (sect x0)))))) = ap (λ u : A → Q, x o u) cm).
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_path_forall _ _))).
        apply isequiv_inverse.
      apply path_forall; intro u. simpl.

      apply (transport (λ U, U = _) (apD10_ap_precompose (A:=A) (B:=X) (C:= λ _, Y) q (ap (λ u : X → Q, x o u)
          (path_forall (m o φ) (m o Ɣ)
             (λ x0 : X,
              ap (m o φ) (sect x0)^ @ (ap10 cm (p x0) @ ap (m o Ɣ) (sect x0))))) u)^).
      apply (transport (λ U, U=_) (ap10_ap_postcompose x (path_forall (m o φ) (m o Ɣ)
           (λ x0 : X,
            ap (m o φ) (sect x0)^ @ (ap10 cm (p x0) @ ap (m o Ɣ) (sect x0)))) (q u))^).
      
      unfold ap10 at 1, path_forall; rewrite eisretr.
      apply (transport (λ U, _ = U) (ap10_ap_postcompose x cm u)^).
      apply ap.
      
      repeat rewrite (oadj u). rewrite ap_V. repeat rewrite <- ap_compose.
      rewrite concat_p_pp.
      (* exact (@ap_conjug_ap10 A Q (m o φ o q) (m o Ɣ o q) (p o q) cm retr u). *)
      admit.
      apply (transport (λ U, invc (x o m; U) = x) X0^).
      exact sectc.
  Qed.

        
      
  
End CoequalizersTransport.

(* Section CoequalizersEpimorphisms. *)

(*   (** Coequalizers are epimorphisms *) *)

(*   (* Lemma coeq_is_epi (A B:Type) (f g:A -> B) (q := @coeq A B f g) *) *)
(*   (* : is_epi q. *) *)

(*   (*   unfold is_epi. *) *)
(*   (*   refine (coequalizer_rect f g _ _ _). *) *)
(*   (*     intro b. apply min1. exists b. reflexivity. *) *)

(*   (*     intro a; simpl. *) *)
      
(*   (*   intros x; destruct x. *) *)
(*   (*   apply min1. exists b. exact 1. *) *)
(*   (* Defined. *) *)

(*   (** Epimorphisms are coequalizers (of their kernel pair) *) *)

(*   Definition kp_coeq_mono {B C :Type} (f : C -> B) (P := pullback f f) (Q := coequalizer (λ x:P, x.1) (λ x:P, x.2.1)) (q := coeq (f:=(λ x:P, x.1)) (g:=(λ x:P, x.2.1))) *)
(*   : Q -> B *)
(*     := @coequalizer_rectnd P C (λ x:P, x.1) (λ x:P, x.2.1) B f (λ a, a.2.2). *)

(*   Lemma kp_coeq_is_mono_transport_lemma *)
(*         {B : Type} *)
(*         {C : Type} *)
(*         (f : C → B) *)
(*         (P := pullback f f : Type) *)
(*         (Q := coequalizer (λ x : P, x.1) (λ x : P, (x.2).1) : Type) *)
(*         (e := coeq (f:=(λ x : P, x.1)) (g:=(λ x : P, (x.2).1)) *)
(*               : C → coequalizer (λ x : P, x.1) (λ x : P, (x.2).1)) *)
(*         (p := kp_coeq_mono f *)
(*               : let P0 := pullback f f in *)
(*                 let Q0 := coequalizer (λ x : P0, x.1) (λ x : P0, (x.2).1) in *)
(*                 let q := coeq (f:=(λ x : P0, x.1)) (g:=(λ x : P0, (x.2).1)) in Q0 → B) *)
(*         (b : B) *)
(*         (c : C) *)
(*         (c' : C) *)
(*         (pcc : e c = e c') *)
(*   : transport (λ x : Q, p x = b) pcc = concat (ap p pcc)^. *)
(*   destruct pcc; simpl. *)
(*   apply path_forall; intro x. *)
(*   rewrite transport_1. *)
(*   rewrite concat_1p. *)
(*   exact 1. *)
(*   Defined. *)

(*   Definition kp_coeq_is_mono_ap_lemma *)
(*              (B : Type) *)
(*              (C : Type) *)
(*              (f : C → B) *)
(*              (P := pullback f f : Type) *)
(*              (Q := coequalizer (λ x : P, x.1) (λ x : P, (x.2).1) : Type) *)
(*              (e := coeq (f:=(λ x : P, x.1)) (g:=(λ x : P, (x.2).1)) *)
(*                    : C → coequalizer (λ x : P, x.1) (λ x : P, (x.2).1)) *)
(*              (p := kp_coeq_mono f *)
(*                    : let P0 := pullback f f in *)
(*                      let Q0 := coequalizer (λ x : P0, x.1) (λ x : P0, (x.2).1) in *)
(*                      let q := coeq (f:=(λ x : P0, x.1)) (g:=(λ x : P0, (x.2).1)) in Q0 → B) *)
(*              (b : B) *)
(*              (c : C) *)
(*              (c' : C) *)
(*              (fcc : f c = f c') *)
(*   : (ap p (path_coeq (c; (c'; fcc)))) = fcc *)
(*     := coequalizer_rectnd_beta_pp B f (λ a : pullback f f, (a.2).2) (c;(c';fcc)). *)

(*   Lemma foo (A B: Type) (x y : A) (f g : A -> A) (P:= λ a, f a= f x)  (p : x = y) *)
(*   : transport P p 1 = ap f p^. *)
(*   destruct p. *)
(*   reflexivity. *)
(*   Qed. *)
  
(*   Lemma kp_coeq_is_mono (B C :Type) (f : C -> B) (P := pullback f f) (Q := coequalizer (λ x:P, x.1) (λ x:P, x.2.1)) (e := coeq (f:=(λ x:P, x.1)) (g:=(λ x:P, x.2.1))) (p := @kp_coeq_mono B C f)  *)
(*   : is_mono p. *)
(*     intros b.  *)
(*     apply hprop_allpath. *)
(*     intros [q π] [q' π']. *)
(*     revert π'. revert π. *)
(*     revert q'. revert q. *)

(*     refine (coequalizer_rect2 (λ x : pullback f f, x.1) *)
(*                               (λ x : pullback f f, (x.2).1) _ _ _ _). *)
(*     { intros b' c' π π'. *)
(*       apply @path_sigma' with (p:= (@path_coeq P C (λ x : P, x.1) (λ x : P, (x.2).1) (b';(c';π @ π'^)))). *)
(*       simpl. *)
(*       pose (p1 := kp_coeq_is_mono_transport_lemma (C:=C) f b _ _ (@path_coeq P C (λ x : P, x.1) (λ x : P, (x.2).1) (b';(c';π @ π'^)))). *)
(*       apply (transport (λ U, U π = π') p1^); clear p1. *)
(*       pose (p1 := kp_coeq_is_mono_ap_lemma _ _ f b b' c' (π @ π'^)). *)
(*       apply (transport (λ U, U^ @ π = π') p1^). *)
(*       apply (transport (λ U, U @ π = _) (inv_pV _ _)^). *)
(*       apply (transport (λ U, U = _) (concat_pp_p _ _ _)^). *)
(*       apply (transport (λ U, π' @ U = π') (concat_Vp _)^). *)
(*       apply (transport (λ U, U = _) (concat_p1 _)^). *)
(*       reflexivity. } *)
    
(*     { intros w [x [y q]]. simpl in *. *)
(*       apply path_forall; intros π. *)
(*       apply path_forall; intros π'. *)
(*       rewrite transport_forall_constant. simpl. *)
(*       rewrite transport_forall. simpl. *)
(*       destruct π'. *)
(*       hott_simpl. *)
(*       repeat rewrite (transport_paths_l _ 1). *)
(*       hott_simpl. *)

(*       unfold path_sigma'. simpl. *)
(*       Search path_sigma. *)
 
      
(*     generalize dependent q'. generalize dependent q. *)

(*     refine (coequalizer_rect (λ x : pullback f f, x.1) (λ x : pullback f f, (x.2).1) _ _ _). *)
(*     { intros b0 π. *)
(*       refine (coequalizer_rect (λ x : pullback f f, x.1) (λ x : pullback f f, (x.2).1) _ _ _). *)
(*       { intros b1 π'. *)
(*         apply @path_sigma' with (p:= (@path_coeq P C (λ x : P, x.1) (λ x : P, (x.2).1) (b0;(b1;π @ π'^)))). *)
(*         simpl. *)

(*         pose (p1 := kp_coeq_is_mono_transport_lemma (C:=C) f b _ _ (@path_coeq P C (λ x : P, x.1) (λ x : P, (x.2).1) (b0;(b1;π @ π'^)))). *)
(*         apply (transport (λ U, U π = π') p1^); clear p1. *)
(*         pose (p1 := kp_coeq_is_mono_ap_lemma _ _ f b b0 b1 (π @ π'^)). *)
(*         apply (transport (λ U, U^ @ π = π') p1^). *)
(*         apply (transport (λ U, U @ π = _) (inv_pV _ _)^). *)
(*         apply (transport (λ U, U = _) (concat_pp_p _ _ _)^). *)
(*         apply (transport (λ U, π' @ U = π') (concat_Vp _)^). *)
(*         apply (transport (λ U, U = _) (concat_p1 _)^). *)
(*         reflexivity. *)
(*       } *)
      
(*       { intros [x [y q]]; simpl in *. *)
(*         (* apply path_forall; intro π'. destruct π'. simpl. *) *)

(*         pose (@dpath_forall _ _ (coequalizer _ _) (λ w, p w = f y) (λ w, λ π', (coeq b0; π) = (w; π'))). _ _ (path_coeq (x; (y; q)))). *)
(*         Search transport. *)


(*         pose (@transport_forall (coequalizer _ _) (λ w, p w = f y) (λ w, λ π', (coeq b0; π) = (w; π')) _ _ (path_coeq (x; (y; q)))). *)
(*         simpl in p0. *)
(*         apply (transport (λ U, U = _) (p0 _ 1)^). *)

        


(*     destruct q as [c], q' as [c'].  *)

(*     apply @path_sigma' with (p:= (@path_coeq P C (λ x : P, x.1) (λ x : P, (x.2).1) (c;(c';π @ π'^)))). *)

(*     pose (p1 := kp_coeq_is_mono_transport_lemma (C:=C) (f:=f) b (@path_coeq P C (λ x : P, x.1) (λ x : P, (x.2).1) (c;(c';π @ π'^)))). *)
(*     apply (transport (λ U, U π = π') p1^); clear p1. *)

(*     pose (p1 := kp_coeq_is_mono_ap_lemma f b c c' (π @ π'^)). *)
(*     apply (transport (λ U, U^ @ π = π') p1^). *)
(*     rewrite inv_pV. hott_simpl. *)
(*   Qed. *)

(*   Lemma coeq_is_equiv (B C :Type) (f : C -> B) (P := pullback f f) (Q := coequalizer (λ x:P, x.1) (λ x:P, x.2.1)) (e := coeq (λ x:P, x.1) (λ x:P, x.2.1)) (p := @kp_coeq_mono B C f) (f_epi : is_epi f) *)
(*   : IsEquiv p. *)
(*     apply epi_mono_equiv. *)
(*     -  assert (forall c, p (e c) = f c). *)
(*        intro c; exact 1. *)
(*        apply (epi_two_out_of_three_2 p (λ c, 1) (@coeq_is_epi P C (λ x:P, x.1) (λ x:P, x.2.1)) f_epi). *)
(*     - apply kp_coeq_is_mono.  *)
(*   Qed. *)

(*   Definition kernel_pair A B (f : A -> B) := pullback f f. *)
  
(*   Definition inj1 A B (f : A -> B) : kernel_pair f -> A := pr1. *)
(*   Definition inj2 A B (f : A -> B) : kernel_pair f -> A := fun x => pr1 (pr2 x). *)

(*   Definition epi_coeq_kernel_pair_comm (C B:Type) (f:C -> B)  *)
(*   : f o (@inj1 C B f) = f o (@inj2 C B f). *)
(*     apply path_forall; intro x. exact x.2.2. *)
(*   Defined. *)
    
(*   Theorem epi_coeq_kernel_pair_eq (C B:Type) (f:C -> B) (f_epi : is_epi f) *)
(*   : coequalizer (@inj1 C B f) (@inj2 C B f) <~> B. *)
(*   Proof. *)
(*     (* apply path_universe_uncurried. *) *)
(*     exists (@kp_coeq_mono B C f). *)
(*     apply coeq_is_equiv. *)
(*     exact f_epi. *)
(*   Defined. *)

(*   Theorem epi_coeq_kernel_pair (C B:Type) (f:C -> B) (f_epi : is_epi f) *)
(*   : is_coequalizer (f ; epi_coeq_kernel_pair_comm f). *)
(*     pose (pp := epi_coeq_kernel_pair_eq f_epi). *)
(*     pose (foo := @coequalizer_transport_end (kernel_pair f) C B (coequalizer (λ x:(kernel_pair f), x.1) (λ x:(kernel_pair f), x.2.1)) (λ x:(kernel_pair f), x.1) (λ x:(kernel_pair f), x.2.1) (path_universe pp)). *)
(*     specialize (foo (coeq (λ x:(kernel_pair f), x.1) (λ x:(kernel_pair f), x.2.1); *)
(*                      path_forall _ _ (@path_coeq _ _ (λ x:(kernel_pair f), x.1) (λ x:(kernel_pair f), x.2.1)))). *)
(*     specialize (foo (coequalizer_is_coequalizer (λ x:(kernel_pair f), x.1) (λ x:(kernel_pair f), x.2.1))). *)
(*     specialize (foo (f; epi_coeq_kernel_pair_comm f)). *)
(*     unfold path_universe in foo. unfold path_universe_uncurried in foo. *)
(*     rewrite eisretr in foo. *)
(*     simpl in foo. *)
(*     specialize (foo 1). *)
(*     apply foo. *)

(*     simpl. *)
(*     unfold epi_coeq_kernel_pair_comm; simpl. *)
(*     apply (@equiv_inj _ _ _ (isequiv_ap10 _ _)). *)
(*     unfold ap10 at 1, path_forall at 1; rewrite eisretr. *)
(*     apply path_forall; intro x. *)
(*     rewrite (ap10_ap_postcompose (kp_coeq_mono (f:=f)) (path_forall coeql coeqr path_coeq) x). *)
(*     unfold ap10, path_forall; rewrite eisretr. *)
(*     simpl. *)
(*     unfold kp_coeq_mono. *)
(*     exact (coequalizer_rectnd_beta_pp f (λ a : pullback f f, (a.2).2) x)^. *)
(*   Qed. *)
(* End CoequalizersEpimorphisms.  *)