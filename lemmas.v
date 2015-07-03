Require Export Utf8_core.
Require Import HoTT.
Require Import hit.Connectedness hit.Truncations Types.Paths.
Require Import univalence.

Set Universe Polymorphism.
Set Implicit Arguments.

Local Open Scope path_scope.
(* Local Open Scope equiv_scope. *)

Section Lemmas.

Context `{ua: Univalence}.
Context `{fs: Funext}.

Lemma path_sigma_1 (A : Type) (P : A → Type) (u : ∃ x, P x)
: path_sigma P u u 1 1 = idpath.
  destruct u. reflexivity.
Defined.

Lemma L425 A B (f:A -> B) (y:B) (x x': hfiber f y)
: (x=x') <~> {Ɣ:x.1=x'.1 & (ap f Ɣ) @ x'.2 = x.2}.
  refine (equiv_adjointify _ _ _ _).
  - intro p. destruct p.
    exists idpath. apply concat_1p.
  - intros [r q]. destruct x as [x p], x' as [x' p']; simpl in *.
    destruct r. apply @path_sigma' with (p:=1). hott_simpl. 
  - intros [Ɣ q].
    destruct x as [x p], x' as [x' p']; simpl in *.
    destruct Ɣ. hott_simpl. destruct q. hott_simpl.
    destruct p'. reflexivity. 
  - intro p; destruct p; hott_simpl.
    destruct x as [x p]. simpl. destruct p. simpl. apply path_sigma_1.
Qed.

Lemma concat_ap (A B:Type) (f : A -> B) (x y: A) (equiv_inv : B -> A) (eisretr : Sect equiv_inv f) (eissect : Sect f equiv_inv) :
  forall (eq : f x = f y), eisretr (f x) @ eq @ (eisretr (f y))^ = ap f (ap equiv_inv eq).
Proof.
  intro.
  destruct eq. simpl. 
  rewrite concat_p1.
  hott_simpl.
Defined.

Lemma concat_ap2 (A B:Type) (f : A -> B) (x y: A) (equiv_inv : B -> A) (eisretr : Sect equiv_inv f) (eissect : Sect f equiv_inv) :
  forall eq, ap equiv_inv (ap f eq) = (eissect x) @ eq @ (eissect y)^.
Proof.
  intro.
  destruct eq.
  simpl. rewrite concat_p1.
  hott_simpl.
Qed.

Lemma isequiv_ap10 : forall (A B: Type) f g, IsEquiv (@ap10 A B f g).
  intros A B f g.
  apply isequiv_apD10.
Defined.

Lemma eta'_path_sigma:
  ∀ (A : Type) (P : A → Type) (u v : ∃ x, P x) (p : u = v) q (pp : p..2 = q),
    path_sigma P u v p ..1 q = p.
  intros A P u bu p q pp.
  destruct pp.
  apply eta_path_sigma.
Qed.


Lemma square_fiber_map {A B C D:Type} (f:A -> B) (g:C -> D) (h:A -> C) (k:B -> D) (s : forall a, k (f a) = g (h a)) (b:B)
: hfiber f b -> hfiber g (k b).
Proof.
  intros X.
  exists (h X.1).
  path_via (k (f X.1)).
  exact (ap k X.2).
Defined.

Section Inverse2.
  
Definition uninverse2 {A} {x y : A} (p q : x = y) : (p^ = q^) -> (p = q).
Proof.
  intros r.
  path_via (p^^).
  apply @concat with (q^^).
  apply inverse2; assumption.
  auto with path_hints.
Defined.

Lemma inverse2_functor {A} (x y : A) (p q r : x = y) (s : p = q) (t : q = r) :
  inverse2 (s @ t) = inverse2 s @ inverse2 t.
Proof.
  path_induction. auto with path_hints.
Defined.

Lemma inverse2_inverse {A} (x y : A) (p q : x = y) (s : p = q) :
  inverse2 (s^) = (inverse2 s)^.
Proof.
  path_induction. auto with path_hints.
Defined.

Lemma inverse_inverse_inverse {A} (x y : A) (p : x = y) :
  inverse2 (inv_V p) =
  inv_V (p^).
Proof.
  path_induction. auto with path_hints.
Defined.

Lemma inverse_inverse_natural {A} (x y : A) (p q : x = y) (r : p = q) :
  inverse2 (inverse2 r) @ inv_V q =
  inv_V p @ r.
Proof.
  path_induction. auto with path_hints.
Defined.

Definition inverse2_equiv {A} (x y : A) (p q : x = y) : (p = q) <~> (p^ = q^).
Proof.
  refine (equiv_adjointify _ _ _ _).
  - apply inverse2.
  - apply uninverse2.
  - intros r.
    unfold uninverse2.
    path_via (inverse2 (inv_V p)^ @ inverse2 (inverse2 r @ inv_V q)).
    apply inverse2_functor.
    path_via ((inverse2 (inv_V p))^ @ inverse2 (inverse2 r @ inv_V q)).
    apply whiskerR.
    apply inverse2_inverse.
    path_via ((inv_V (p^))^ @ inverse2 (inverse2 r @ inv_V q)).
    apply whiskerR.
    apply ap.
    apply inverse_inverse_inverse.
    apply moveR_Mp.
    path_via (inverse2 (inverse2 r) @ inverse2 (inv_V q)).
    apply inverse2_functor.
    path_via (inverse2 (inverse2 r) @ inv_V (q^)).
    apply whiskerL.
    apply inverse_inverse_inverse.
    eapply (concat (inverse_inverse_natural r)).
    apply whiskerR. auto with path_hints.
  - intros r.
    unfold uninverse2.
    apply moveR_Mp.
    rewrite inverse_inverse_natural.
    apply whiskerR. auto with path_hints.
Defined.

End Inverse2.
    
Section Three_by_three.

  Hypotheses A B C D : Type.
  Hypotheses (f : A -> B) (g : C -> D) (h : A -> C) (k : B -> D).
  Hypothesis s : forall a, k (f a) = g (h a).

  Variables (b : B) (c : C).
  Variable (d : k b = g c).

  Let fibf := hfiber f b.
  Let fibg := hfiber g (k b).

  Let fibf_to_fibg := square_fiber_map g h k s (b:=b) :
    fibf -> fibg.

  Let fibh_to_fibk := square_fiber_map k f g (fun a => (s a)^) (b:=c)
    : hfiber h c -> hfiber k (g c).
  
  Let fibfg := hfiber fibf_to_fibg (c; d^). (* {z : fibf & fibf_to_fibg z = (c ; !d)} *)
  Let fibhk := hfiber fibh_to_fibk (b; d).  (* {z : hfiber h c & fibh_to_fibk z = (b ; d)} *)

  Lemma sect_path_sigma (X : Type) (P : X → Type) (u v : ∃ x, P x) (p : u.1 = v.1)
        (q : transport P p u.2 = v.2)
  : ((path_sigma P u v p q) ..1; (path_sigma P u v p q)..2) = (existT (λ p, transport P p u.2 = v.2) p q) .
    refine (path_sigma'  _ _ _).
    exact (pr1_path_sigma p q).
    rewrite transport_paths_Fl.
    rewrite (pr2_path_sigma p q).
    apply moveR_Vp. reflexivity.
  Qed.


    
  Let fibfibmapf (x : A) (p : f x = b) :
    ((h x ; (s x)^ @ ap k p) = (existT (fun c' => g c' = k b) c (d^)))
    <~>
    {q : h x = c & transport (fun c' => g c' = k b) q ((s x)^ @ ap k p) = d^}.
    refine (equiv_adjointify _ _ _ _).
    - intro q.
      exists q..1. exact q..2.
    - intros [q qq].
      apply path_sigma' with q. exact qq.
    - intros [q qq].
      unfold path_sigma'. simpl.
      apply (sect_path_sigma (λ c' : C, g c' = k b) (h x; (s x)^ @ ap k p) (c; d^) q qq).
    - intro q. unfold path_sigma'.
      apply eta_path_sigma.
  Defined.

  Let fibfibmaph (x : A) (q : h x = c) :
    ((f x ; (s x)^^ @ ap g q) = (existT (fun b' => k b' = g c) b d))
    <~> {p : f x = b &
             transport (fun b' => k b' = g c) p ((s x)^^ @ ap g q) = d}.
    refine (equiv_adjointify _ _ _ _).
    - intro p.
      exists p..1. exact p..2.
    - intros [p pp].
      apply path_sigma' with p. exact pp.
    - intros [p pp].
      unfold path_sigma'. simpl.
      apply (sect_path_sigma (λ b' : B, k b' = g c) (f x; ((s x)^)^ @ ap g q) (b; d) p pp).
    - intro p. unfold path_sigma'.
      apply eta_path_sigma.
  Defined.

  Let fibfibfibmap (x : A) (p : f x = b) (q : h x = c) :
    (transport (fun c' => g c' = k b) q ((s x)^ @ ap k p) = d^)
    <~>
    (transport (fun b' => k b' = g c) p ((s x)^^ @ ap g q) = d).
    apply equiv_inverse.
    equiv_via
      ((transport (fun b' => k b' = g c) p ((s x)^^ @ ap g q))^ = d^).
    apply inverse2_equiv.
    assert ((transport (λ b' : B, k b' = g c) p (((s x)^)^ @ ap g q))^
            = transport (λ c' : C, g c' = k b) q ((s x)^ @ ap k p)).
    { repeat rewrite transport_paths_FlFr.
      repeat rewrite ap_const.
      hott_simpl.
      repeat rewrite ap_V.
      repeat rewrite inv_pp.  repeat rewrite inv_V. rewrite concat_pp_p. reflexivity. }
    rewrite X. apply equiv_idmap.
  Defined.

  Let fibfibmap (x : A) (p : f x = b) :
    {q : h x = c &
      (transport (fun c' => g c' = k b) q ((s x)^ @ ap k p) = d^)}
    <~>
    {q : h x = c &
      (transport ( fun b' => k b' = g c) p ((s x)^^ @ ap g q) = d)}.
  Proof.
    apply equiv_functor_sigma_id. intro a.
    apply fibfibfibmap.
  Defined.

   Let fibmap (x:A) :
    {p : f x = b & fibf_to_fibg (x ; p) = (c ; d^)} <~>
    {q : h x = c & fibh_to_fibk (x ; q) = (b ; d)}.
  Proof.
    equiv_via
      ({p : f x = b & {q : h x = c &
                           transport (fun c' => g c' = k b) q ((s x)^ @ ap k p) = d^ } }).
    apply equiv_functor_sigma_id.
    intros; apply fibfibmapf.
    equiv_via
      ({q : h x = c & {p : f x = b &
        transport (fun b' => k b' = g c) p ((s x)^^ @ ap g q) = d } }).
    equiv_via
      ({p : f x = b & {q : h x = c&
                           transport (fun b' => k b' = g c) p ((s x)^^ @ ap g q) = d } }).
    apply equiv_functor_sigma_id. intros.
    apply fibfibmap.
    apply equiv_sigma_symm.
    apply equiv_functor_sigma_id. intros.
    apply equiv_inverse.
    apply fibfibmaph.
  Defined.

  Definition three_by_three' : fibfg <~> fibhk.
  Proof.
    equiv_via
      ({x : A & {p : f x = b & fibf_to_fibg (x;p) = (c;d^) } } ).
    apply equiv_inverse.
    unfold fibfg, fibf_to_fibg, square_fiber_map, hfiber, fibf, hfiber. simpl.
    exact (@equiv_sigma_assoc A (λ x, f x = b) (λ X, (h X.1; (s X.1)^ @ ap k X.2) = (existT (λ c, g c = k b) c (d^)))).
    unfold fibhk, fibh_to_fibk, fibf_to_fibg, square_fiber_map, hfiber. simpl.
    equiv_via
      ({x : A & {p : h x = c & fibh_to_fibk (x;p) = (b;d) } }).
    apply equiv_functor_sigma_id. intros.
    apply fibmap.
    exact (@equiv_sigma_assoc A (λ x, h x = c) (λ X, fibh_to_fibk X = (b; d))).
  Defined.
  
End Three_by_three.

Lemma three_by_three {A B C D:Type} (f:A -> B) (g:C -> D) (h:A -> C) (k:B -> D) (s : forall a, k (f a) = g (h a)) (b:B) (c:C) (p:k b = g c)
      (fibf_to_fibg := square_fiber_map g h k s (b:=b))
      (fibh_to_fibk := square_fiber_map k f g (λ a, (s a)^) (b:=c))
: hfiber fibf_to_fibg (c;p^) = hfiber fibh_to_fibk (b;p).
  apply path_universe_uncurried.
  apply three_by_three'.
Defined.

Lemma VpV (X:Type) (x y:X) (p q:x=y): p=q -> p^= q^.
intro H. destruct H. auto.
Defined.

Lemma ap_path_forall (A B C:Type) (f:A -> B) (g h:B -> C) (eq:forall x, g x = h x)              
: ap (λ u, u o f) (path_forall g h eq) = path_forall (g o f) (h o f) (λ x, (eq (f x))).
  apply (@equiv_inj _ _ _ (isequiv_ap10 _ _)).
  unfold ap10 at 2, path_forall at 2; rewrite eisretr.
  apply path_forall; intro a.
  rewrite ap10_ap_precompose.
  unfold ap10, path_forall; rewrite eisretr. reflexivity.
Qed.
    
Lemma path_sigma_eta (A : Type) (P : A → Type) (u : ∃ x, P x)
: path_sigma P u (u.1;u.2) 1 1 = (eta_sigma u)^.
destruct u. simpl. reflexivity.
Defined.

Lemma moveR_E_compose (A B C:Type) (f:B -> C) (g : A -> B) (h : A -> C) (IsEq_g : IsEquiv g)
: (f = h o g^-1) -> (f o g = h).
  intro H.
  symmetry in H.
  destruct H. apply path_forall; intro x. rewrite eissect. reflexivity.
Qed.

Lemma ap_ap_path_forall (X:Type) (Y:X -> Type) (g h:forall x:X, Y x) eq x
: ap (λ f:forall x:X, Y x, f x)
     (path_forall g h eq)
  = eq x.
  apply (apD10 (f := ((ap (x:=g) (y:=h) (λ f : ∀ x0 : X, Y x0, f x)) o apD10^-1)) (g:= λ eq, eq x)).
  refine (moveR_E_compose _ _).
  simpl. apply path_forall; intro u.
  destruct u; reflexivity.
Qed.

Lemma ap_ap2_path_forall (X:Type) (Y : X -> Type) (Z:forall x:X, Y x -> Type) (g h : forall x:X, forall y:Y x, Z x y) eq x y
: ap (λ f:forall x:X, forall y:Y x, Z x y, f x y) (path_forall g h (λ x, path_forall (g x) (h x) (eq x)))
  = eq x y.
  rewrite (ap_compose (λ f : ∀ (x0 : X) (y0 : Y x0), Z x0 y0, f x) (λ f, f y) (path_forall g h (λ x0 : X, path_forall (g x0) (h x0) (eq x0)))).
  pose (rew := ap_ap_path_forall (λ x0 : X, path_forall (g x0) (h x0) (eq x0)));
    simpl in rew; rewrite rew; clear rew.
  apply ap_ap_path_forall.
Qed.

Lemma ap_transport_Vp {X} (Y:X -> Type) {x1 x2:X} (p:x1 = x2) {y1 y2 : Y x1} (q:y1 = y2)
: ap (transport Y p^) (ap (transport Y p) q) = transport_Vp Y p y1 @ q @ (transport_Vp Y p y2)^.
destruct p, q; reflexivity.
Qed.

Lemma transport_VpV {A} (P : A -> Type) {x y:A} (p:x=y) (z:P y)
: transport_Vp P p (transport P p^ z)
  = ap (transport P p^) (transport_pV P p z).
  destruct p; reflexivity.
Qed.

Lemma trunc_unit (n:trunc_index) : IsTrunc n Unit.
Proof.
  induction n.
  exact contr_unit.
  apply (trunc_succ).
Defined.  
  
  

End Lemmas.