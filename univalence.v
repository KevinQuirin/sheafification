Require Export Utf8_core.
Require Import HoTT.
Require Import Coq.Program.Tactics.

Set Universe Polymorphism.
Global Set Primitive Projections.
Set Implicit Arguments.

Local Open Scope path_scope.
Local Open Scope equiv_scope.
Local Open Scope type_scope.

Context `{ua: Univalence}.
Context `{fs: Funext}.

(* we assume functional extensionality and univalence *)

(* Instance univalence_equiv : Univalence.  *)

(* Definition univalence_axiom T T' : (T <~> T') -> T = T' :=  *)
(*   @equiv_inv _ _ _ (isequiv_equiv_path T T'). *)

(* Definition univalence_transport : forall (T T' : Type) (f : T -> T') *)
(*   (G:IsEquiv f) (x:T), transport idmap (univalence_axiom (BuildEquiv _ _ f G)) x = f x. *)
(* Admitted. *)

(* Instance equal_f_equiv : Funext. *)
(* Admitted. *)

(* Definition functional_extensionality_dep {A} {B : A -> Type} (f g : forall x : A, B x) : *)
(*   (forall x, f x = g x) -> f = g := @equiv_inv _ _ _ (isequiv_apD10 _ _ f g). *)

Theorem log_equiv_is_equiv (A B:Type) {H : IsHProp A} {H' : IsHProp B} (f : A -> B) (g : B -> A) : 
  IsEquiv f.
  assert (Sect f g). intro x. apply allpath_hprop; assumption.
  assert (Sect g f). intro x. apply allpath_hprop; assumption.
  apply BuildIsEquiv with (eisretr := X0) (eissect := X).
  intro. destruct (H' (f (g (f x))) (f x)). rewrite <- contr. symmetry. apply contr.
Defined.

Theorem univalence_hprop (A B:Type) {H : IsHProp A} {H' : IsHProp B} : (A <-> B) -> A = B.
Proof.
  destruct 1 as [f g]. apply path_universe_uncurried.
  exists f. exact (log_equiv_is_equiv (H:=H) (H':=H') f g).
Defined.

Lemma eq_dep_subset' : forall A (B:A -> Type) (_:forall a, IsHProp (B a)) 
                             (a a':A) (H: B a) (H': B a'),
                        a = a' -> existT _ a H = existT _ a' H'.
  intros. apply (path_sigma' _ X0). destruct X0. apply (X a).
Defined.

Lemma eq_dep_subset : forall A (B:A -> Type) (_:forall a, IsHProp (B a)) 
                             (u v : sigT B),
                        u.1 = v.1 -> u = v.
  intros. apply (path_sigma _ _ _ X0). destruct u; destruct v; simpl in X0; destruct X0. apply allpath_hprop. 
Defined.

Lemma isequiv_eq_dep_subset {A:Type} {B:A -> Type} (X : ∀ a : A, IsHProp (B a)) (u v : {a:A & B a})
: IsEquiv (eq_dep_subset X u v).
  apply @isequiv_adjointify with (g := λ p, ap pr1 p).
  - intro p. destruct p. simpl. unfold eq_dep_subset.
    destruct u as [a H]; simpl in *.
    assert (center (H=H) = 1).
    apply contr.
    apply (transport (λ u, path_sigma B (a;H) (a;H) 1 u = 1) X0^).
    exact 1.
  - intro p.
    destruct u as [u G], v as [v H].
    simpl in p; destruct p. unfold eq_dep_subset.
    pose (foo := @ap_existT). unfold path_sigma' in foo.
    rewrite <- foo.
    simpl. unfold allpath_hprop.
    destruct (center (G=H)). reflexivity.
Defined.

