Require Export Utf8_core.
Require Import HoTT.
Require Import hit.Connectedness hit.Truncations Types.Paths.
Require Import univalence.

Set Universe Polymorphism.
Set Implicit Arguments.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

Section Lemmas.

Context `{ua: Univalence}.
Context `{fs: Funext}.

Lemma path_sigma_1 (A : Type) (P : A → Type) (u : ∃ x, P x)
: path_sigma P u u 1 1 = 1.
  destruct u. reflexivity.
Defined.

Lemma L425 A B (f:A -> B) (y:B) (x x': hfiber f y)
: (x=x') = {Ɣ:x.1=x'.1 & (ap f Ɣ) @ x'.2 = x.2}.
  apply path_universe_uncurried.
  refine (equiv_adjointify _ _ _ _).
  - intro p. destruct p.
    exists 1. apply concat_1p.
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
  
End Lemmas.