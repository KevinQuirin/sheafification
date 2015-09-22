(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.

Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
Local Open Scope type_scope.

Module Export T.

  Private Inductive T {A B:Type} (f: A -> B) : Type :=
    | t : A -> (T f).

  Arguments t {A B f} a.

  Axiom tp : forall {A B f} (a b:A), f a = f b -> @t A B f a = @t A B f b.

  Axiom tp_1 : forall {A B f} (a:A), @tp A B f a a 1 = 1.

  Definition T_ind {A B:Type} {f:A -> B} (P : T f -> Type)
             (t' : forall a, P (t a))
             (tp' : forall a b p, transport P (tp a b p) (t' a) = t' b)
             (tp_1' : forall a, (transport2 P (tp_1 a) (t' a))^ @ tp' a a 1 = 1)
    : forall w, P w
    := fun w => match w with
                |t a => fun _ => t' a
                end tp_1'.

  Axiom T_ind_beta_tp : forall {A B:Type} {f:A -> B} (P : T f -> Type)
             (t' : forall a, P (t a))
             (tp' : forall a b p, transport P (tp a b p) (t' a) = t' b)
             (tp_1' : forall a, (transport2 P (tp_1 a) (t' a))^ @ tp' a a 1 = 1)
             a b p,
     apD (T_ind P t' tp' tp_1') (tp a b p) = tp' a b p.
        
End T.

Definition T_rec {A B:Type} {f:A -> B} (P:Type)
           (t': A -> P)
           (tp' : forall (a b:A) (p:f a = f b), t' a = t' b)
           (tp_1' : forall a, tp' a a 1 = 1)
  : T f -> P.
Proof.
  refine (T_ind _ t' (fun a b p => transport_const _ _ @ tp' a b p)  _).
  intro a.
  exact ((concat_p_pp ((transport2 (λ _ : T f, P) (tp_1 a) (t' a))^)  (transport_const (tp a a 1) (t' a)) (tp' a a 1))                                                                                                 @ whiskerR (moveR_Vp _ _ _ (transport2_const (A:=T f) (B:= P) (tp_1 a) (t' a))) (tp' a a 1)                                                                                                         @ concat_1p _                                                                                     @ (tp_1' a)).
Defined.

Definition T_rec_beta_tp {A B:Type} {f:A -> B} (P:Type)
           (t': A -> P)
           (tp' : forall (a b:A) (p:f a = f b), t' a = t' b)
           (tp_1' : forall a, tp' a a 1 = 1)
           a b p
  : ap (T_rec P t' tp' tp_1') (tp a b p) = tp' a b p.
Proof.
Admitted.