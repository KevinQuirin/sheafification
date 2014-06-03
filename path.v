Require Export Utf8_core.
Require Import HoTT.
Set Implicit Arguments.
Set Universe Polymorphism.
Global Set Primitive Projections.

(* Inductive paths {A : Type} (a : A) : A -> Type := *)
(*   idpath : paths a a. *)

(* Arguments idpath {A a} , [A] a. *)

(* Arguments paths_ind [A] a P f y p. *)
(* Arguments paths_rec [A] a P f y p. *)
(* Arguments paths_rect [A] a P f y p. *)

(* Notation "x = y :> A" := (@paths A x y) : type_scope. *)
(* Notation "x = y" := (x = y :>_) : type_scope. *)

Notation " ( x ; p ) " := (existT _ x p).
(* Notation Π1 := projT1. *)
(* Notation Π2 := projT2. *)
Notation "T ** U" := (prod T U) (at level 50) : type_scope.

(* Definition idmap {A} := fun (x:A) => x. *)

(* Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y. *)
(*   destruct p. exact u. Defined. *)

(* Definition transportage {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y. *)
(*   destruct p. exact u. Defined. *)

(* Arguments transport {A} P {x y} p u : simpl nomatch. *)

(* Lemma transport_const : ∀ (A B : Type) (x y: A) (p:x = y) (y : B), *)
(*  transport (fun _ => B) p y = y. intros. destruct p. exact (idpath _).  *)
(* Defined. *)

Notation "p # u" := (transport _ p u) (right associativity, at level 65, only parsing).

(* Definition inverse {A : Type} {x y : A} (p : x = y) : y = x *)
(*   := match p with idpath => idpath end. *)

(* Arguments inverse {A x y} p : simpl nomatch. *)

(* Notation "p ^" := (inverse p) (at level 3). *)

(* Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y *)
(*   := match p with idpath => idpath end. *)

(* Definition apD {A:Type} {B:A->Type} (f:∀ a:A, B a) {x y:A} (p:x=y): *)
(*   p # (f x) = f y *)
(*   := *)
(*   match p with idpath => idpath end. *)

Definition composition T U V (f : T -> U) (g : U -> V) := fun t => g (f t).

Notation  "g ° f" := (composition f g) (at level 50).

Definition comp_assoc A B C D (f: A -> B) (g:B -> C) (h : C -> D) :
  h ° (g ° f) = (h ° g) ° f := idpath.

Definition apf (A B X : Type) (f : A -> B) (x y : X -> A) : x = y -> f ° x = f ° y.
  intro. destruct X0. reflexivity. Defined.

(** See above for the meaning of [simpl nomatch]. *)
(* Arguments ap {A B} f {x y} p : simpl nomatch. *)
(* Arguments apD {A B} f {x y} p : simpl nomatch. *)

(* Lemma transport_compose {A B} {x y : A} (P : B -> Type) (f : A -> B) *)
(*   (p : x = y) (z : P (f x)) *)
(*   : transport (fun x => P (f x)) p z  =  transport P (ap f p) z. *)
(* Proof. *)
(*   destruct p; reflexivity. *)
(* Defined. *)

(* Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z. *)
(*   destruct q. exact p. Defined. *)

Notation "p @ q" := (concat p q) (at level 20) : type_scope.

(* Lemma apD_const {A B} {x y : A} (f : A -> B) (p: x = y) : *)
(*   apD f p = transport_const p (f x) @ ap f p. *)
(* Proof. *)
(*   destruct p. reflexivity. *)
(* Defined. *)

(* Definition transport_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1) *)
(*   : transport (fun y => x = y) p q = q @ p. *)
(* Proof. *)
(*   destruct p, q; reflexivity. *)
(* Defined. *)

(* Lemma concat_R {A : Type} {x y z : A} (p p': x = y) (q : y = z) : p = p' -> p @ q = p' @ q. *)
(* destruct 1. reflexivity. Defined.  *)

(* Lemma concat_L {A : Type} {x y z : A} (p : x = y) (q q': y = z) : q = q' -> p @ q = p @ q'. *)
(* destruct 1. reflexivity. Defined.  *)

(* Definition concat_assoc {A : Type} {x y z w : A} (p : x = y) (q : y = z) (r : z = w) :  *)
(*   (p @ q) @ r = p @ (q @ r). *)
(* destruct p,q,r. reflexivity. Defined. *)

(* Lemma ap_concat A B (f:A -> B) (a b c : A) (p : a = b) (q : b = c) :  *)
(*   ap f (p @ q) = ap f p @ ap f q. *)
(*   destruct p, q. reflexivity. *)
(* Defined. *)

Lemma inverse_inv_L A (x y : A) (p : x = y) : inverse p @ p = idpath _.
  destruct p. reflexivity.
Defined.

Lemma inverse_inv_R A (x y : A) (p : x = y) : p @ inverse p = idpath _.
  destruct p. reflexivity.
Defined.

Lemma idpath_L {A : Type} {x y: A} (p : x = y) : (idpath _) @ p = p.
destruct p. reflexivity. Defined.

Lemma idpath_R {A : Type} {x y: A} (p : x = y) : p @ (idpath _) = p.
destruct p. reflexivity. Defined.

Definition id_sym (A : Type) (x y : A) : x = y -> y = x.
  intro e. destruct e. reflexivity. Defined.

(* Lemma cancelL {A} {x y z : A} (p : x = y) (q r : y = z) *)
(*   : (p @ q = p @ r) -> (q = r). *)
(* Proof. *)
(*   destruct p, r. *)
(*   intro a. exact (id_sym (idpath_L q) @ a). *)
(* Defined. *)

(* Lemma cancelR {A} {x y z : A} (p q : x = y) (r : y = z) *)
(*   : (p @ r = q @ r) -> (p = q). *)
(* Proof. *)
(*   destruct r, p. *)
(*   intro a. *)
(*   exact (a @ idpath_R q). *)
(* Defined. *)

(* Definition transport_pp {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) : *)
(*   p @ q # u = q # p # u := *)
(*   match q with idpath => *)
(*     match p with idpath => idpath end *)
(*   end. *)

(* Definition transport_arrow {A : Type} {B C : A -> Type} *)
(*   {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C x1) (y : B x2) *)
(*   : (transport (fun x => B x -> C x) p f) y  =  p # (f (id_sym p # y)). *)
(* Proof. *)
(*   destruct p; simpl. reflexivity. *)
(* Defined. *)

(* Definition ap_sym {A B:Type} (f:A -> B) {x y:A} (p:x = y) : ap f (id_sym p) = id_sym (ap f p) := *)
(*   match p with idpath => idpath end. *)


(* Definition transportD {A : Type} (B : A -> Type) (C : forall a:A, B a -> Type) *)
(*   {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1 y) *)
(*   : C x2 (p # y) *)
(*   := *)
(*   match p with idpath => z end. *)

(* Definition transport_pV {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P y) *)
(*   : p # id_sym p # z = z *)
(*   := id_sym (transport_pp P (id_sym p) p z) *)
(*   @ ap (fun r => transport P r z) (inverse_inv_L p). *)

(* Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x) : Type *)
(*   := forall x:A, f x = g x. *)

(* Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope. *)

(* Definition transport_forall *)
(*   {A : Type} {P : A -> Type} {C : forall x, P x -> Type} *)
(*   {x1 x2 : A} (p : x1 = x2) (f : forall y : P x1, C x1 y) *)
(*   : (transport (fun x => forall y : P x, C x y) p f) *)
(*     == (fun y => *)
(*        transport (C x2) (transport_pV _ _ _) (transportD _ _ p _ (f (id_sym p # y)))) *)
(*   := match p with idpath => fun _ => idpath _ end. *)


(* Definition transport_paths_lr {A : Type} {x1 x2 : A} (p : x1 = x2) (q : x1 = x1) *)
(*   : transport (fun x => x = x) p q = id_sym p @ q @ p. *)
(* Proof. *)
(*   destruct p; simpl. *)
(*   rewrite <- ((id_sym (idpath_L q))).  *)
(*   apply (id_sym (idpath_R q)).  *)
(* Defined. *)

(* Definition moveR_transport_p {A : Type} (P : A -> Type) {x y : A} *)
(*   (p : x = y) (u : P x) (v : P y) *)
(*   : u = inverse p # v -> p # u = v. *)
(* Proof. *)
(*   destruct p. *)
(*   exact idmap. *)
(* Defined. *)

(* Definition moveR_transport_V {A : Type} (P : A -> Type) {x y : A} *)
(*   (p : y = x) (u : P x) (v : P y) *)
(*   : u = p # v -> inverse p # u = v. *)
(* Proof. *)
(*   destruct p. *)
(*   exact idmap. *)
(* Defined. *)

Definition equal_f (A : Type) (P : A -> Type) (f g : forall x, P x) (p : f = g) :
forall x, f x = g x.
intro x. destruct p. reflexivity.
Defined.

Definition equal_f_eq (A : Type) (P : A -> Type) (f g : forall x, P x) (p : f = g) x y (q : y = x) : equal_f P p x = transport (fun x => f x = g x) q (equal_f P p y).
  destruct p, q. reflexivity.
Defined.

(* Definition transport2 {A : Type} (P : A -> Type) {x y : A} {p q : x = y} *)
(*   (r : p = q) (z : P x) *)
(*   : p # z = q # z *)
(*   := ap (fun p' => p' # z) r. *)

Definition eq_transport {A : Type} (B : A -> Type) (g : forall a:A, B a -> B a)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (q : y = g x1 y) : p # y = transport (λ a : A, B a → B a) p (g x1) (p # y).
  destruct p. exact q. Defined.

Definition transportD_eq {A : Type} (B : A -> Type) (g : forall a:A, B a -> B a)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (q : y = g x1 y)
  : transportD B (fun a b => b = g a b) p y q =
    (eq_transport _ _ p q) @ equal_f _ (apD g p) (p # y).
  destruct p. apply (id_sym (idpath_R _)).
Defined.


(* Definition transport_paths_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B} *)
(*   (p : x1 = x2) (q : f x1 = y) *)
(*   : transport (fun x => f x = y) p q = inverse (ap f p) @ q. *)
(* Proof. *)
(*   destruct p, q; reflexivity. *)
(* Defined. *)

(* Definition transport_paths_FFlr {A B : Type} {f : A -> B} {g : B -> A} {x1 x2 : A} *)
(*   (p : x1 = x2) (q : g (f x1) = x1) *)
(*   : transport (fun x => g (f x) = x) p q = inverse (ap g (ap f p)) @ q @ p. *)
(* Proof. *)
(*   destruct p; simpl. *)
(*   exact (inverse (idpath_L q) @ inverse (idpath_R ((idpath _) @ q))). *)
(* Defined. *)

(* Definition transport_sigma {A : Type} {B : A -> Type} {C : forall a:A, B a -> Type} *)
(*   {x1 x2 : A} (p : x1 = x2) (yz : { y : B x1 & C x1 y }) *)
(*   : transport (fun x => { y : B x & C x y }) p yz *)
(*     = (p # yz.1 ; transportD _ _ p (yz.1) (yz.2)). *)
(* Proof. *)
(*   destruct p.  destruct yz as [y z]. reflexivity. *)
(* Defined. *)


Definition id_sym_invol (A : Type) (x y : A) (e : x = y) : id_sym (id_sym e) = e.
  destruct e. reflexivity. Defined.

Definition id_sym_invol2 (A : Type) (x y : A) (e : x = y) : (e ^%path) ^%path = e.
  destruct e. reflexivity. Defined.

Lemma eq_dep_sumT : forall A (B:A->Type) (P P':A) (H:B P) (H':B P')  (prf: P = P'), H = prf ^# H'  -> existT _ P H = existT _ P' H'.
intros A B P P' H H' prf X; destruct prf. rewrite X. reflexivity.
 Qed.

(* Definition projT1_path {A} {P : A -> Type} {u v : sigT P} (p : u = v) *)
(* : u.1 = v.1 := ap (@projT1 _ _) p. *)

(* Notation "p ..1" := (projT1_path p) (at level 3). *)

(* Definition projT2_path {A} {P : A -> Type} {u v : sigT P} (p : u = v) *)
(*   : p..1 # u.1 = v.2 *)
(*   := inverse (transport_compose P (@projT1 _ _) p (u.2)) *)
(*      @ (@apD {x:A & P x} _ (@projT2 _ _) _ _ p). *)

(* Notation "p ..2" := (projT2_path p) (at level 3). *)

Ltac equalT_pi1 := match goal with | [ |- existT _ ?x _ = existT _ ?y _] => assert
  (x = y) end. 

Ltac equalT_pi1L x := match goal with | [ |- _ = existT _ ?y _] => assert
  (x = y) end. 

Ltac equalT_pi1R y := match goal with | [ |- existT _ ?x _ = _] => assert
  (x = y) end. 


Lemma existT_eta : ∀ A (P : A -> Type) (t : sigT P), t = existT _
  (t.1) (t.2).
   destruct t. reflexivity. 
Qed.
