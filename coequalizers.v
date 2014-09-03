Require Export Utf8_core.
Require Import HoTT TruncType.
Require Import hit.Connectedness hit.minus1Trunc.
Require Import univalence lemmas epi_mono.

Set Universe Polymorphism.
Set Implicit Arguments.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

Section Coequalizers_HIT.
  
  Private Inductive coequalizer {A B:Type} (f g : A -> B) : Type :=
    | coeq : B -> coequalizer f g.

  Arguments coeq {A B f g} b.
  
  Definition coeql {A B:Type} {f g:A -> B} (a:A) : coequalizer f g
    := coeq (f a).

  Definition coeqr {A B:Type} {f g:A -> B} (a:A) : coequalizer f g
    := coeq (g a).

  Axiom pp_coeq : forall {A B:Type} {f g: A -> B} (a:A), @coeql A B f g a = coeqr a.

  Definition coequalizer_rect {A B} (f g: A -> B) (P : coequalizer f g -> Type)
   (coeq' : forall b : B, P (coeq b))
   (pp_coeq' : forall a : A, (@pp_coeq A B f g a) # (coeq' ((f a))) = coeq' ((g a)))
   : forall w, P w
   := fun w => match w with coeq a => fun _ => coeq' a end pp_coeq'.

  Definition coequalizer_rect_compute {A B} (f g: A -> B) (P : coequalizer f g -> Type)
   (coeq' : forall b : B, P (coeq b))
   (pp_coeq' : forall a : A, (@pp_coeq A B f g a) # (coeq' ((f a))) = coeq' ((g a)))
   x
  : coequalizer_rect P coeq' pp_coeq' (coeq x) = coeq' x.
  Proof.
    reflexivity.
  Defined.

  Axiom coequalizer_rect_beta_pp
   : forall {A B f g} (P : @coequalizer A B f g -> Type)
   (coeq' : forall b : B, P (coeq b))
   (pp_coeq' : forall a : A, (@pp_coeq A B f g a) # (coeq' ((f a))) = coeq' ((g a)))
   (a : A),
   apD (@coequalizer_rect _ _ f g P coeq' pp_coeq') (pp_coeq a) = pp_coeq' a.

  Definition coequalizer_rectnd {A B:Type} {f g:A -> B} (P:Type) (coeq' : B -> P) (pp' : forall a:A, coeq' (f a) = coeq' (g a))
  : @coequalizer A B f g -> P
    := coequalizer_rect (λ _, P) coeq' (λ a, (transport_const (pp_coeq a) (coeq' (f a))) @ (pp' a)).

  Definition coequalizer_rectnd_beta_pp {A B:Type} {f g:A -> B} (P:Type) (coeq' : B -> P) (pp' : forall a:A, coeq' (f a) = coeq' (g a)) (a:A)
  : ap (coequalizer_rectnd coeq' pp') (pp_coeq a) = pp' a.
    unfold coequalizer_rectnd.
    eapply (cancelL (transport_const (pp_coeq a) _)).
    refine ((apD_const (@coequalizer_rect A B f g (fun _ => P) coeq' _) (pp_coeq a))^ @ _).
    refine (coequalizer_rect_beta_pp (λ _, P) coeq' (λ a, (transport_const (pp_coeq a) (coeq' (f a))) @ (pp' a)) a).
  Defined.
  
End Coequalizers_HIT.

Section Coequalizer_universal_property.

  Definition is_coequalizer A B (f g : A -> B) X (coequalizer : {m : B -> X & m o f =  m o g}) :=
    forall Y, IsEquiv (fun x : X -> Y => 
                         existT (fun m => m o f =  m o g) (x o pr1 coequalizer) (ap (fun u => x o u) (pr2 coequalizer))).

  Theorem coequalizer_is_coequalizer A B (f g : A -> B)
  : @is_coequalizer A B f g (coequalizer f g) ((coeq f g); path_forall _ _ (@pp_coeq A B f g)).
    intro Y. simpl.
    apply @isequiv_adjointify with (g := λ m, (@coequalizer_rectnd A B f g Y m.1 (ap10 m.2))).
    - intros [m p]. simpl.
      apply @path_sigma' with (p := path_forall _ _ (coequalizer_rect_compute (λ _ : coequalizer f g, Y) m (λ a : A, transport_const (pp_coeq a) (m (f a)) @ ap10 p a))).

      simpl.
      unfold coequalizer_rect_compute.
      rewrite path_forall_1. simpl. 
      apply (@equiv_inj _ _ _ (isequiv_ap10 _ _)).
      apply path_forall; intro x.
      rewrite (ap10_ap_postcompose (coequalizer_rectnd m (ap10 p)) (path_forall coeql coeqr pp_coeq)).
      unfold ap10, path_forall; rewrite eisretr.
      apply coequalizer_rectnd_beta_pp.

    - intro φ. simpl.

      assert ((ap10
                 (ap (λ u : A → coequalizer f g, φ o u)
                     (path_forall coeql coeqr pp_coeq))) = λ x, ap φ (pp_coeq x)).

      apply path_forall; intro x. rewrite ap10_ap_postcompose. unfold ap10, path_forall; rewrite eisretr. exact 1.

      apply (transport (λ U, coequalizer_rectnd (φ o coeq f g) U = φ) X^).
      unfold coequalizer_rectnd.

      apply path_forall; intro c; destruct c.
      apply (coequalizer_rect_compute (λ _ : coequalizer f g, Y) (φ o coeq f g) (λ a : A,
                                                                                       transport_const (pp_coeq a) ((φ o coeq f g) (f a)) @ ap φ (pp_coeq a))).
  Qed.
  
End Coequalizer_universal_property.

Lemma coeq_is_epi (A B:Type) (f g:A -> B) (q := @coeq A B f g)
: is_epi q.
  intros x; destruct x.
  apply min1. exists b. exact 1.
Defined.

Definition coeq_mono (B C :Type) (f : C -> B) (P := pullback f f) (Q := coequalizer (λ x:P, x.1) (λ x:P, x.2.1)) (q := coeq (λ x:P, x.1) (λ x:P, x.2.1))
: Q -> B
  := @coequalizer_rectnd P C (λ x:P, x.1) (λ x:P, x.2.1) B f (λ a, a.2.2).

Lemma coeq_is_mono_transport_lemma
      (B : Type)
      (C : Type)
      (f : C → B)
      (P := pullback f f : Type)
      (Q := coequalizer (λ x : P, x.1) (λ x : P, (x.2).1) : Type)
      (e := coeq (λ x : P, x.1) (λ x : P, (x.2).1)
            : C → coequalizer (λ x : P, x.1) (λ x : P, (x.2).1))
      (p := coeq_mono (f:=f)
            : let P0 := pullback f f in
              let Q0 := coequalizer (λ x : P0, x.1) (λ x : P0, (x.2).1) in
              let q := coeq (λ x : P0, x.1) (λ x : P0, (x.2).1) in Q0 → B)
      (b : B)
      (c : C)
      (c' : C)
      (pcc : e c = e c')
: transport (λ x : Q, p x = b) pcc = concat (ap p pcc)^.
destruct pcc; simpl.
apply path_forall; intro x.
rewrite transport_1.
rewrite concat_1p.
exact 1.
Defined.

Definition coeq_is_mono_ap_lemma
      (B : Type)
      (C : Type)
      (f : C → B)
      (P := pullback f f : Type)
      (Q := coequalizer (λ x : P, x.1) (λ x : P, (x.2).1) : Type)
      (e := coeq (λ x : P, x.1) (λ x : P, (x.2).1)
            : C → coequalizer (λ x : P, x.1) (λ x : P, (x.2).1))
      (p := coeq_mono (f:=f)
            : let P0 := pullback f f in
              let Q0 := coequalizer (λ x : P0, x.1) (λ x : P0, (x.2).1) in
              let q := coeq (λ x : P0, x.1) (λ x : P0, (x.2).1) in Q0 → B)
      (b : B)
      (c : C)
      (c' : C)
      (fcc : f c = f c')
: (ap p (pp_coeq (c; (c'; fcc)))) = fcc
  := coequalizer_rectnd_beta_pp f (λ a : pullback f f, (a.2).2) (c;(c';fcc)).
  
Lemma coeq_is_mono (B C :Type) (f : C -> B) (P := pullback f f) (Q := coequalizer (λ x:P, x.1) (λ x:P, x.2.1)) (e := coeq (λ x:P, x.1) (λ x:P, x.2.1)) (p := @coeq_mono B C f) 
: is_mono p.
  intros b. unfold hfiber.
  apply hprop_allpath.
  intros [q π] [q' π'].

  destruct q. destruct q'. rename c0 into c'.

  apply @path_sigma' with (p:= (@pp_coeq P C (λ x : P, x.1) (λ x : P, (x.2).1) (c;(c';π @ π'^)))).
  simpl. fold P; fold Q.  unfold p, coeq_mono in π, π'. simpl in π, π'.

  pose (bla := @pp_coeq _ _ (λ x : P, x.1) (λ x : P, (x.2).1) (c; (c'; π @ π'^))).
  simpl in bla. unfold coeql, coeqr in bla. simpl in bla.

  pose (p1 := coeq_is_mono_transport_lemma (C:=C) (f:=f) b (@pp_coeq P C (λ x : P, x.1) (λ x : P, (x.2).1) (c;(c';π @ π'^)))).
  simpl in p1.

  apply (transport (λ U, U π = π') p1^); clear p1.

  pose (p1 := coeq_is_mono_ap_lemma f b c c' (π @ π'^)).
  simpl in p1.

  apply (transport (λ U, U^ @ π = π') p1^).
  rewrite inv_pV. hott_simpl.
Qed.

Lemma coeq_is_equiv (B C :Type) (f : C -> B) (P := pullback f f) (Q := coequalizer (λ x:P, x.1) (λ x:P, x.2.1)) (e := coeq (λ x:P, x.1) (λ x:P, x.2.1)) (p := @coeq_mono B C f) (f_epi : is_epi f)
: IsEquiv p.
  apply epi_mono_equiv.
  -  assert (forall c, p (e c) = f c).
       intro c; exact 1.
       
    apply (epi_two_out_of_three_2 p (λ c, 1) (@coeq_is_epi P C (λ x:P, x.1) (λ x:P, x.2.1)) f_epi).
  - apply coeq_is_mono. 
Qed.


Definition kernel_pair A B (f : A -> B) := pullback f f.

Definition inj1 A B (f : A -> B) : kernel_pair f -> A := pr1 (P:=_).
Definition inj2 A B (f : A -> B) : kernel_pair f -> A := fun x => pr1 (P:=_) (pr2 (P:=_) x).

Theorem epi_coeq_kernel_pair (C B:Type) (f:C -> B) (f_epi : is_epi f)
: coequalizer (@inj1 C B f) (@inj2 C B f) = B.
Proof.
  apply path_universe_uncurried.
  exists (@coeq_mono B C f).
  apply coeq_is_equiv.
  exact f_epi.
Qed.

Theorem coequalizer_transport (A B X Q:Type) (f g:A -> B) (p : X = Q)  (n : (∃ n : B → Q, n o f = n o g)) (Q_coeq : is_coequalizer n)  (cm : (equiv_path _ _ p^) o n.1 o f = (equiv_path _ _ p^) o n.1 o g) (ccm : cm = ap (λ u, (equiv_path _ _ p^) o u) n.2)
: @is_coequalizer A B f g X (((equiv_path _ _ p^) o n.1); cm).
  
  destruct p; simpl in *.
  destruct n as [n cn]. simpl in *.

  unfold compose in *. simpl in *.
  rewrite ap_idmap in ccm. destruct ccm.
  exact Q_coeq.
Qed.