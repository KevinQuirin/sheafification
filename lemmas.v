Require Export Utf8_core.
Require Import HoTT.
Require Import hit.Connectedness hit.minus1Trunc types.Paths.
Require Import univalence.

Set Universe Polymorphism.
Set Implicit Arguments.

Local Open Scope path_scope.
Local Open Scope equiv_scope.


Lemma path_sigma_1 (A : Type) (P : A → Type) (u : ∃ x, P x)
: path_sigma P u u 1 1 = 1.
  destruct u. exact 1.
Defined.

Lemma L425_inv A B (f:A -> B) (y:B) (x x': hfiber f y)
: ((∃ Ɣ : x .1 = x' .1, ap f Ɣ @ x' .2 = x .2) -> (x=x')).
  intros [r q]. destruct x as [x p], x' as [x' p']; simpl in *.
    destruct r. apply @path_sigma' with (p:=1). hott_simpl.
Defined.

Lemma L425 A B (f:A -> B) (y:B) (x x': hfiber f y)
: (x=x') = {Ɣ:x.1=x'.1 & (ap f Ɣ) @ x'.2 = x.2}.
  apply univalence_axiom.
  exists ((λ p, match p with 1 => (1;concat_1p x.2) end) : x = x' -> (∃ Ɣ : x .1 = x' .1, ap f Ɣ @ x' .2 = x .2)).
  apply isequiv_adjointify with (g := L425_inv x x').
  - intros [Ɣ q].
    destruct x as [x p], x' as [x' p']; simpl in *.
    destruct Ɣ. hott_simpl. destruct q. hott_simpl.
    destruct p'. exact 1. 
  -  intro p; destruct p; hott_simpl.
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

Lemma moveL_pV_moveR_pM (A:Type) (x y z:A) (p : x = z) (q : y = z) (r : y = x)
: forall Ɣ, (moveL_pV p r q (moveR_pM p q r Ɣ)) = Ɣ.
  intro Ɣ. 
  unfold moveR_pM, moveL_pV. destruct p. hott_simpl.
Qed.


Lemma isequiv_ap10 : forall (A B: Type) f g, IsEquiv (@ap10 A B f g).
  intros A B f g.
  apply isequiv_apD10.
Defined.

Lemma ap_conjug_ap10 (A B:Type) (f g : A -> B) φ (r : f = g) (p : forall x, φ x = x) x
: (ap f (p x))^ @ (ap10 r (φ x)) @ (ap g (p x)) = ap10 r x.
  destruct r. simpl. rewrite concat_p1. apply concat_Vp.
Qed.