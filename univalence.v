Require Export Utf8_core.
Require Import HoTT.
Require Import Coq.Program.Tactics.

Set Universe Polymorphism.
Global Set Primitive Projections.
Set Implicit Arguments.

(* we assume functional extensionality and univalence *)

Instance univalence_equiv : Univalence. 
Admitted.

Definition univalence_axiom T T' : (T <~> T')%equiv -> T = T' := 
  @equiv_inv _ _ _ (isequiv_equiv_path T T').

Definition univalence_transport : forall (T T' : Type) (f : T -> T')
  (G:IsEquiv f) (x:T), transport idmap (univalence_axiom (BuildEquiv _ _ f G)) x = f x.
Admitted.

Instance equal_f_equiv : Funext.
Admitted.

Definition functional_extensionality_dep {A} {B : A -> Type} (f g : forall x : A, B x) :
  (forall x, f x = g x) -> f = g := @equiv_inv _ _ _ (isequiv_apD10 _ _ f g).

Theorem log_equiv_is_equiv (A B:Type) {H : IsHProp A} {H' : IsHProp B} (f : A -> B) (g : B -> A) : 
  IsEquiv f.
  assert (Sect f g). intro x. apply allpath_hprop; assumption.
  assert (Sect g f). intro x. apply allpath_hprop; assumption.
  apply BuildIsEquiv with (eisretr := X0) (eissect := X).
  intro. destruct (H' (f (g (f x))) (f x)). rewrite <- contr. symmetry. apply contr.
Defined.

Theorem univalence_hprop (A B:Type) {H : IsHProp A} {H' : IsHProp B} : (A <-> B) -> A = B.
Proof.
  destruct 1 as [f g]. apply univalence_axiom.
  exists f. exact (log_equiv_is_equiv (H:=H) (H':=H') f g).
Defined.

Lemma eq_dep_subset : forall A (B:A -> Type) (_:forall a, IsHProp (B a)) 
                             (a a':A) (H: B a) (H': B a'),
                        a = a' -> existT _ a H = existT _ a' H'.
  intros. apply (path_sigma' _ X0). destruct X0. apply (X a).
Defined.
