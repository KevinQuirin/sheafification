Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.

Require Import equiv truncation univalence sub_object_classifier.

Set Universe Polymorphism.
Global Set Primitive Projections.
Set Implicit Arguments.

Definition pullback (A B C : Type) (f : A -> C) (g : B -> C) := {a:A & {b: B & f a = g b}}.

Section Pullback.

  Variable A B C : Type.
  Variable f : A -> C.
  Variable g : B -> C.

  Variable S : Type.

  Definition pullback_inj : (S -> pullback f g) -> 
                            pullback (fun m : S -> A => f o m) (fun n : S -> B => g o n) :=
    fun h => (pr1 o h; ((fun x => pr1 (pr2 x)) o h ; 
                              path_forall _ _ (fun s => pr2 (pr2 (h s))))).


  Instance pullback_equiv : IsEquiv pullback_inj.
  apply (isequiv_adjointify pullback_inj (λ X s, (pr1 X s ;(pr1 (pr2 X) s ; ap10 (pr2 (pr2 X)) s)))).
  - intro P; destruct P as [m [n P]]. simpl. unfold pullback_inj, compose; simpl.
    apply path_sigma' with (p := idpath).
    simpl.
    apply path_sigma' with (p := idpath). 
    simpl. apply eissect.
  - intro P. apply path_forall. intro s. 
    rewrite <- eta_sigma.
    apply path_sigma' with (p := idpath); simpl.
    rewrite <- eta_sigma.
    apply path_sigma' with (p := idpath); simpl.
    unfold ap10, path_forall. rewrite eisretr.
    exact idpath.
  Defined.
  
  Definition pullback_proj : pullback f g -> {_:A & B} := 
    fun X => existT (fun _ => B) (pr1 X) (pr1 (pr2 X)).

End Pullback.

Section Images.
  
  Definition Im {A B} (f : A -> B) := {b : B & squash (hfiber f b)}.

  Definition toIm {A B} (f : A -> B) : A -> Im f := fun a => (f a; truncation_incl (a;idpath)).

  Definition fromIm {A B} (f : A -> B) : Im f -> B := fun im => pr1 im.
  
End Images.
