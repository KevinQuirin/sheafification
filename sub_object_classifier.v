Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations.

(* Require Import univalence. *)
Require Import equivalence.
Require Import epi_mono.

Set Universe Polymorphism.
Global Set Primitive Projections.
Set Implicit Arguments.

Section SubObject_CLassifier.

Context `{ua: Univalence}.
Context `{fs: Funext}.

Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.

Definition hfiber_eqL A B (f : A -> B) : {b : B & {a : A & f a = b}} -> A.
  intro b. destruct b as [b [a eq]]. exact a. Defined.

Definition hfiber_eqR A B (f : A -> B) : A -> {b : B & {a : A & f a = b}}.
  intro a. exists (f a). exists a. reflexivity. Defined.

Definition hfiber_eq_eissect A B (f : A -> B) : Sect (hfiber_eqL f) (hfiber_eqR f).
intro. destruct x as [b [a x]]. destruct x. reflexivity. Defined.

Definition hfiber_eq_eisretr A B (f : A -> B) : Sect (hfiber_eqR f) (hfiber_eqL f).
intro. reflexivity. Defined.

Instance hfiber_eq_eq A B (f: A -> B) : IsEquiv (hfiber_eqL f).
eapply (BuildIsEquiv _ _ _ (hfiber_eqR f) (hfiber_eq_eisretr f) (hfiber_eq_eissect f)). 
intros. destruct x as [b [a x]]. destruct x. reflexivity. Defined.

Definition hfiber_eq A B (f : A -> B) : {b : B & hfiber f b} = A.
  apply path_universe_uncurried. 
  exists (hfiber_eqL f).
  exact (hfiber_eq_eq _).
Defined.

Definition hfiber_pi1L B (P : B -> Type) (b : B) : 
  hfiber (@pr1 B (λ b0 : B, P b0)) b -> P b.
  intro. destruct X as [[a e] eq]. exact (eq # e). Defined.

Definition hfiber_pi1R B (P : B -> Type) (b : B) : 
  P b -> hfiber (@pr1 B (λ b0 : B, P b0)) b.
  intro e. exists (b;e). reflexivity. Defined.

Definition hfiber_pi1_eissect B (P : B -> Type) (b : B) : Sect (hfiber_pi1L P (b:=b)) (hfiber_pi1R P b).
intro t; destruct t as [[b' e] eq]. induction eq. reflexivity. Defined.

Definition hfiber_pi1_eisretr B (P : B -> Type) (b : B) : Sect (hfiber_pi1R P b) (hfiber_pi1L P (b:=b)).
intro x; reflexivity. Defined.

Instance hfiber_pi1_eq B (P : B -> Type) (b:B) : IsEquiv (hfiber_pi1L P (b:=b)).
apply (BuildIsEquiv _ _ _ (hfiber_pi1R P b) (hfiber_pi1_eisretr P b) (hfiber_pi1_eissect P (b:=b))).
destruct x as [[? ?] eq]; induction eq; simpl. reflexivity. Defined.
  
Definition hfiber_pi1 B (P : B -> Type) (b : B) : 
  hfiber (@pr1 B (λ b0 : B, P b0)) b = P b.
  apply path_universe_uncurried. 
  exists (hfiber_pi1L P (b:=b)).
  exact (hfiber_pi1_eq _ _).
Defined.

Definition sub_to_char B : {A : Type & A -> B} -> B -> Type :=
  λ f b, hfiber (f.2) b.

Definition char_to_sub B : (B -> Type) -> {A : Type & A -> B} :=
  λ P, ({b : B & P b} ; @pr1 _ (P)).

Definition sub_eq_char_retr B : Sect (char_to_sub (B:=B)) (sub_to_char (B:=B)).
intro P. apply path_forall; intro b. apply hfiber_pi1. Defined.

Definition sub_eq_char_sect B : Sect (sub_to_char (B:=B)) (char_to_sub (B:=B)).
  intro t; destruct t as [A f]; simpl. 
  apply (path_sigma' (λ T, T -> B) (hfiber_eq f)). 
  apply path_forall; intro t.
  rewrite transport_arrow. rewrite transport_const. unfold hfiber_eq.
  erewrite moveR_transport_V. assert ((existT (fun b => {a : A | f a = b}) (f t) (t; idpath)).1 = f t).
  reflexivity. exact X.
  pose (p := transport_path_universe {| equiv_fun := hfiber_eqL f; equiv_isequiv := hfiber_eq_eq f |}). unfold path_universe in p. simpl in p.
  rewrite p. reflexivity.
Defined.
  
Instance sub_eq_char_eq B : IsEquiv (sub_to_char (B:=B)).
apply (isequiv_adjointify _ (char_to_sub (B:=B)) (sub_eq_char_retr (B:=B)) (sub_eq_char_sect (B:=B))). 
Defined.

(* Definition sub_eq_char B : {A : Type & A -> B} = (B -> Type). *)
(*   apply path_universe_uncurried.  *)
(*   exists (sub_to_char (B := B)). *)
(*   exact (sub_eq_char_eq B). *)
(* Defined. *)

Definition terminal A B (f : A -> B) : A -> {A' : Type & A'} :=
  λ a, (hfiber f (f a); (a; idpath)).

Definition subobject_diagram A B (f : A -> B) : 
  @pr1 _ (idmap) o terminal f = sub_to_char (A;f) o f.
  apply path_forall; intro a. unfold sub_to_char; simpl. reflexivity.
Defined.

Definition nsub_to_char n B : {A : Type & {f : A -> B & forall b, IsTrunc n (hfiber f b)}} -> B -> Trunk n :=
  λ f b, (hfiber (f.2.1) b; (f.2.2) b).
 
Instance projContr B (P : B -> {T : Type & Contr_internal T}) (b:B) : Contr_internal ((P b).1)
 := (P b).2.

Instance nhfiber_pi1_eq n B (P : B -> Trunk n) (b:B) : IsEquiv (hfiber_pi1L (fun b => (P b).1) (b:=b)).
apply (hfiber_pi1_eq (fun b => (P b).1)).
Defined.

Definition nhfiber_pi1 n B (P : B -> Trunk n) (b : B) : 
  hfiber (@pr1 _ (λ b0 : B, (P b0).1)) b = (P b).1 :=
  hfiber_pi1 (fun b => (P b).1) b.

Instance nchar_to_sub_eq n B (P : B -> Trunk n) (b:B) : IsEquiv (λ x:(P b).1, 
(existT (λ x, x.1 = b) (existT (λ b, (P b).1) b x) idpath)).
apply (isequiv_adjointify  (λ x : (P b) .1, (existT (λ x, x.1 = b) (existT (λ b, (P b).1) b x) idpath)) (fun X => transport (λ b, (P b).1) (X.2) (X.1.2))).
- intro x; destruct x as [[b' P'] eqb']. simpl in *.
  destruct eqb'. simpl.
  apply path_sigma' with (p := idpath); simpl.
  reflexivity.
- intro x. reflexivity. Defined. 

Definition nchar_to_sub_compat n B (P : B -> Trunk n) : 
  forall b, IsTrunc n (hfiber (A:={b : B & (P b).1}) (B:=B) (@pr1 _ (fun b => (P b).1)) b).
  intro. unfold hfiber. unfold Trunk in *.
  eapply (@trunc_equiv ((P b).1) ({x : {b0 : B & (P b0).1} & x.1 = b})
                       (λ x:((P b).1), (existT (λ x, x.1 = b) (existT (λ b, (P b).1) b x) idpath))).
  exact ((P b).2).
  exact (nchar_to_sub_eq _ _).
Defined.

Definition nchar_to_sub n B : (B -> Trunk n) -> {A : Type & {f : A -> B & forall b, IsTrunc n (hfiber f b)}} :=
  λ P, ({b : B & (P b).1} ; (@pr1 _ _; nchar_to_sub_compat _)).

Definition ntransport_arrow n {A : Type} {B C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C x1) (y : B x2) (Tr_f : ∀ b : C x1 , IsTrunc n (hfiber f b))
  : pr1 (transport (fun x => {f0 : B x -> C x & forall (b:C x), IsTrunc n {x : B x & f0 x = b}}) p (f; Tr_f)) y  =  p # (f (p^ # y)).
Proof.
  destruct p; simpl. reflexivity.
Defined.

Definition nsub_eq_char_retr n B : Sect (nchar_to_sub (n:=n) (B:=B)) (nsub_to_char n (B:=B)).
  intro P. apply path_forall; intro b.
  unfold nsub_to_char, nchar_to_sub, hfiber; simpl.
  apply truncn_unique. simpl.
  apply nhfiber_pi1.
Defined.

(* Lemma eq_dep_sumT : forall A (B:A->Type) (P P':A) (H:B P) (H':B P')  (prf: P = P'),  H = prf^ # H'  -> existT _ P H = existT _ P' H'. *)
(* intros A B P P' H H' prf X; destruct prf. rewrite X. reflexivity. *)
(*  Qed. *)

Definition nsub_eq_char_sect n B : Sect (nsub_to_char n (B:=B))(nchar_to_sub (n:=n) (B:=B)).
  intro t; destruct t as [A f]; simpl.
  apply (path_sigma) with (p := (hfiber_eq (f.1))).
  (* apply (eq_dep_sumT (λ T, ∃ f : T → B, ∀ b : B, IsTrunc n (hfiber f b)) _ (hfiber_eq (f.1))). *)
  simpl.
  apply (moveR_transport_p (λ A0 : Type, ∃ f0 : A0 → B, ∀ b : B, IsTrunc n (hfiber f0 b)) (hfiber_eq f .1) (pr1; nchar_to_sub_compat (nsub_to_char n (A; f))) f).
  rewrite <- (eta_sigma).

  assert (pr1 = (transport (λ A0 : Type, ∃ f0 : A0 → B, ∀ b : B, IsTrunc n (hfiber f0 b))
     (hfiber_eq f .1) ^ f).1).
  (* equalT_pi1. *)
  apply path_forall; intro t.
  destruct t as [b [a eq]]; simpl.
  destruct f as [f Tr_f]. simpl in *.
  pose (trans := (@ntransport_arrow n _ (λ x, x) (λ x, B) _ _ (hfiber_eq f)^ f (f a; (a; idpath)) Tr_f)).
  transitivity (transport (λ _ : Type, B) (hfiber_eq f)^
          (f
             (transport (λ x : Type, x) (((hfiber_eq f)^^))
                (f a; (a; idpath))))).
  hott_simpl.
  (* rewrite (id_sym_invol). *)
  unfold hfiber_eq. rewrite transport_path_universe_uncurried, transport_const.
  simpl. exact (eq^).
  symmetry. simpl in *.
  destruct eq; exact trans.

  apply path_sigma with (p := X).
  apply path_ishprop.
Defined. 

Instance nsub_eq_char_eq n B : IsEquiv (nsub_to_char n (B:=B)) := 
  isequiv_adjointify _ (nchar_to_sub (B:=B)) (nsub_eq_char_retr (n:=n) (B:=B)) (nsub_eq_char_sect n (B:=B)).

Definition nsub_eq_char n B : {A : Type & {f : A -> B & forall b, IsTrunc n (hfiber f b)}} = (B -> Trunk n).
  apply path_universe_uncurried.
  exists (nsub_to_char n (B:=B)).
  exact (nsub_eq_char_eq _ _).
Defined.

Definition nterminal n A B (f : {f : A -> B & forall b, IsTrunc n (hfiber f b)}) : A -> {A' : Trunk n & (A'.1)} :=
  λ a, (((hfiber (f.1) ((f.1) a)) ; (f.2) ((f.1) a)); (a; idpath)).

Definition nsubobject_diagram n A B (f : {f : A -> B & forall b, IsTrunc n (hfiber f b)}) : 
  @pr1 _ _ o nterminal n f = nsub_to_char n (A;f) o (f.1).
  apply path_forall; intro a. unfold nsub_to_char; simpl. reflexivity.
Defined.

Definition fibers_composition_f A B C (f : A -> B) (g : B -> C) (c : C) : hfiber (g o f) c -> {w : hfiber g c & hfiber f (w.1)} := λ a, ( (f (a.1) ; a.2) ; (a.1 ; idpath )).

Arguments fibers_composition_f {A B C} f g {c} _.

Definition fibers_composition_g A B C (f : A -> B) (g : B -> C) (c : C) : {w : hfiber g c & hfiber f (w.1)} -> hfiber (g o f) c.
  destruct 1 as [X X0]. destruct X as [xg pxg]. destruct X0 as [xf pxf]; simpl in *.
  exists xf; destruct pxf. exact pxg.
Defined.

Definition fibers_composition_retr A B C (f : A -> B) (g : B -> C) (c : C) : 
  Sect (fibers_composition_g (f:=f) (g:=g) (c:=c)) (fibers_composition_f (f) (g) (c:=c)). 
  intro x; destruct x as [[x px] [y py]].
  unfold fibers_composition_f; simpl in *.
  destruct px; destruct py. reflexivity.
Defined.

Definition fibers_composition_sect A B C (f : A -> B) (g : B -> C) (c : C) : 
  Sect (fibers_composition_f (f) (g) (c:=c)) (fibers_composition_g (f:=f) (g:=g) (c:=c)). 
  intro x. destruct x as [x p]. 
  reflexivity.
Defined.
Arguments fibers_composition_sect {A B C} f g {c} _.

Instance fibers_composition_eq A B C (f : A -> B) (g : B -> C) (c : C) : IsEquiv (@fibers_composition_f A B C f g c).
apply (BuildIsEquiv _ _ _ (fibers_composition_g (f:=f) (g:=g) (c:=c)) (fibers_composition_retr (f:=f) (g:=g) (c:=c)) (fibers_composition_sect (f) (g) (c:=c))).
  destruct x as [x p]; simpl.
  destruct p.
  reflexivity.
Defined.
  
Lemma fibers_composition A B C (f : A -> B) (g : B -> C) (c : C):
  (hfiber (g o f) c) = { w : (hfiber g c) & hfiber f (w.1) }.
Proof.
  apply path_universe_uncurried.
  exists (@fibers_composition_f _ _ _ _ _ _).
  exact (@fibers_composition_eq _ _ _ _ _ _).
Qed.

Lemma function_trunc_compo n A B C : forall (f : A -> B) (g : B -> C), (forall (b:B), IsTrunc n (hfiber f b)) -> (forall (c:C), IsTrunc n (hfiber g c)) -> (forall (c:C), IsTrunc n (hfiber (g o f) c)).
Proof.
  intros f g Hf Hg c.
  rewrite (fibers_composition f g). refine trunc_sigma.
Defined.

Definition hfiber_eq_L A B C (f : A -> B) (g : B -> C) b : hfiber f b -> hfiber (g o f) (g b).
  intro e. destruct e as [x p]. exists x. exact (ap g p). Defined.

Definition hfiber_eq_R A B C (f : A -> B) (g : B -> C) (H :IsMono g) b : hfiber (g o f) (g b) -> hfiber f b.
  destruct 1 as [x p]. exists x. exact (@equiv_inv _ _ _ (H (f x) b) p).  Defined.

Instance hfiber_mono_equiv A B C (f : A -> B) (g : B -> C) (H :IsMono g) b : IsEquiv (hfiber_eq_L (f:=f) g (b:=b)). 
apply (isequiv_adjointify _ (hfiber_eq_R H b)).
- intro e. destruct e. simpl. apply @path_sigma' with (p:=idpath).
  apply eisretr.
- intro e. destruct e. simpl. apply @path_sigma' with (p :=idpath).
  apply eissect. 
Defined.

Definition hfiber_mono A B C (f : A -> B) (g : B -> C) (X :IsMono g) b : hfiber f b = hfiber (g o f) (g b).
  apply path_universe_uncurried. exists (hfiber_eq_L (f:=f) g (b:=b)). apply hfiber_mono_equiv. exact X.
Defined.


Definition inter_symm_f E (χ φ : E -> Type) x :
  hfiber (λ t : {b : {b : E & χ b} & φ (pr1 b)}, pr1 (pr1 t)) x ->
  hfiber (λ t : {b : {b : E & φ b} & χ (pr1 b)}, pr1 (pr1 t)) x := 
  fun X => ((existT (fun b => _ b .1) (X.1.1.1;X.1.2) X.1.1.2);X.2).

Instance inter_symm_equiv E (χ φ : E -> Type) x : IsEquiv (inter_symm_f χ φ (x:=x)). 
apply (isequiv_adjointify _ (inter_symm_f φ χ (x:=x))).
- intro X; destruct X as [[[a b] c] d]. reflexivity.
- intro X; destruct X as [[[a b] c] d]. reflexivity.
Defined.

Definition inter_symm E (χ φ : E -> Type) x :
  hfiber (λ t : {b : {b : E & χ b} & φ (pr1 b)}, pr1 (pr1 t)) x = 
  hfiber (λ t : {b : {b : E & φ b} & χ (pr1 b)}, pr1 (pr1 t)) x.
  apply path_universe_uncurried. exact (BuildEquiv _ _ _ (inter_symm_equiv _ _ x)).
Defined.

End SubObject_CLassifier.



