Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import path equiv truncation univalence sub_object_classifier limit_colimit.

Set Universe Polymorphism.
Global Set Primitive Projections.
Set Implicit Arguments.

(* Needed lemmas *)

  Definition apD10_fed (A : Type) (B : A -> Type) (f g : ∀ x : A, B x) (H : forall x, f x = g x)  :
    apD10 (path_forall f g H) = H .
    unfold path_forall. unfold equiv_inv.
    destruct (@isequiv_apD10 equal_f_equiv A B f g).
    exact (eisretr H).
  Defined.

  Definition apf_L  (A B X : Type) (f : X -> A) (x y : A -> B) : x = y -> x ° f = y ° f.
    intro H. destruct H. exact idpath.
  Defined.

  Lemma apf_L_concat A B X (f:X -> A) (a b c : A -> B) (p : a = b) (q : b = c) :
    apf_L f (p @ q) = apf_L f p @ apf_L f q.
    destruct p, q. reflexivity.
  Defined.

  Lemma apf_L_inv A B X (f:X -> A) (a b : A -> B) (p:a=b) : inverse (apf_L f p) = apf_L f (inverse p).
    destruct p. exact idpath.
  Defined.

  Lemma ap_ap10_ {oA A B} (g h : oA -> B) (η : A -> oA) (p : g = h) (a : A) : apD10 (ap (fun f => f°η) p) a = ap10 p (η a).
    destruct p. exact idpath.
  Defined.

(* Definition 7.7.1 *)
Record subuniverse_struct n := Build_subuniverse_struct { 
  
  subuniverse_HProp : forall (T:Trunc n), HProp  ;
    
  O : Trunc n -> {T : Trunc n & (subuniverse_HProp T).1} ;

  O_unit : forall T, T.1 -> (O T).1.1;

  O_equiv : forall (P : Trunc n) (Q :{T : Trunc n & (subuniverse_HProp T).1}),
              IsEquiv (fun f : (O P).1.1 -> Q.1.1 => f ° (O_unit P)) 
}.

Section Reflective_Subuniverse.

  Variable n:trunc_index.

  Variable subU : subuniverse_struct n.
  
  Definition subuniverse_Type := 
  {T : Trunc n & pr1 (subU.(subuniverse_HProp) T)}.
  
  Definition subuniverse_Type_is_TruncSn : IsTrunc (trunc_S n) subuniverse_Type.
    unfold subuniverse_Type.
    apply (@trunc_sigma _ (fun T => (subuniverse_HProp subU T) .1) _ (Tn_is_TSn (n:=n))).
    intro T. apply IsHProp_IsTrunc. apply (pr2 (subU.(subuniverse_HProp) T)).
  Defined.

  Definition O_rec (P : Trunc n) (Q : subuniverse_Type) :
    (P.1 -> Q.1.1) -> (subU.(O) P).1.1 -> Q.1.1 := 
    (@equiv_inv _ _ _ (subU.(O_equiv) _ _)).

  Definition O_rec_retr (P : Trunc n) (Q : subuniverse_Type) f
  : O_rec _ _ f ° subU.(O_unit) _ = f :=
    @eisretr _ _ _ (subU.(O_equiv) P Q) f.

  Definition O_rec_sect (P : Trunc n) (Q : subuniverse_Type) f :=
    @eissect _ _ _ (subU.(O_equiv) P Q) f.

  
  Definition O_rec_const (P:Trunc n) (Q:subuniverse_Type) y : O_rec P Q (λ _, y) = (λ _, y)
    := eissect _ (IsEquiv := O_equiv subU P Q) (λ x, y).

  Lemma transport_O_rec (P:Trunc n) (Q R:subuniverse_Type) (B:= λ S:subuniverse_Type, S.1.1) (eq : Q = R) f r:
    transport B eq (O_rec P Q f r) = O_rec P R (λ v, transport B eq (f v)) r.
    destruct eq. simpl. exact idpath.
  Defined.
  
  Definition O_unit_retract_equiv (T:Trunc n) (μ : (subU.(O) T).1.1 -> T.1) (η := subU.(O_unit) T) : Sect η μ -> IsEquiv η.
    unfold Sect; intros H. apply isequiv_adjointify with (g:=μ).
    - assert (η ° μ ° η = idmap ° η).
      rewrite <- comp_assoc. unfold composition at 3. apply apf.
      apply path_forall; intro y.
      exact (H y).
      exact (apD10 (elim_E (subU.(O_equiv) T (subU.(O) T)) (η ° μ) idmap X)).
    - exact H.
  Defined.
    
  Instance O_modal_equiv (P : subuniverse_Type) : IsEquiv (subU.(O_unit) P.1).
  apply O_unit_retract_equiv with (μ := (O_rec P.1 P idmap)).
  pose (f := O_rec_retr P.1 P idmap). 
  intro. eapply apD10 in f. exact (f x).
  Defined.

  Definition unique_subuniverse : forall (T T' : subuniverse_Type), pr1 T = pr1 T' -> T = T'. 
    intros. destruct T, T'. eapply (eq_dep_subset (λ x, let (a, _) := subuniverse_HProp subU x in a) _ _ _ X). 
    Grab Existential Variables. intro. simpl. exact ((subuniverse_HProp subU a) .2).
  Defined.

  Definition O_modal (T:subuniverse_Type) : T = subU.(O) T.1.
    apply unique_subuniverse. apply truncn_unique.
    apply univalence_axiom.
    exact (BuildEquiv _ _ (subU.(O_unit) (pr1 T)) (O_modal_equiv _)).
  Defined.

  Definition O_invol : forall T, (O subU) ( pr1 ((O subU) T)) = O subU T.
    intro T; symmetry; apply O_modal.
  Defined.

  Definition subuniverse_struct_transport T U (f : (T.1 <~> U.1)%equiv) :
    (subU.(subuniverse_HProp) T).1 -> (subU.(subuniverse_HProp) U).1.
    apply univalence_axiom in f. apply truncn_unique in f. rewrite f.
    intro x; exact x.
  Defined.
  
  Definition subuniverse_iff_O (T:Trunc n) : 
    IsEquiv (subU.(O_unit) T) = pr1 (subU.(subuniverse_HProp) T).
    apply univalence_hprop. apply hprop_isequiv. apply (pr2 (subU.(subuniverse_HProp) T)).
    split.
    - exact (fun X => subuniverse_struct_transport _ _ (BuildEquiv _ _ _ (isequiv_inverse (H:=X))) (pr2 (subU.(O) T))). 
    - exact (fun X => O_modal_equiv (T;X)).
  Defined.


(* ○-lift of functions *)
  
  Definition function_lift (A B : Trunc n) (f : A.1 -> B.1) : (subU.(O) A).1.1 -> (subU.(O) B).1.1.
    apply O_rec; intro x; apply subU.(O_unit); apply f; exact x.
  Defined.

  Definition function_lift_modal (A:Trunc n) (B:subuniverse_Type) (f : A.1 -> B.1.1) : (O subU A).1.1 -> B.1.1.
    apply O_rec. exact f.
  Defined.

  Notation "'○' f" := (function_lift _ _ f) (at level 0).
  Notation "'○' f" := (function_lift_modal _ _ f) (at level 0).

  Lemma O_rec_O_unit (A : subuniverse_Type) (B : Trunc n) (f : B.1 -> A.1.1) (x : (O subU B).1.1) :
    O_unit subU A.1 (O_rec B A f x) = O_rec B (O subU A.1) ((O_unit subU A.1)°f) x.
    assert (O_rec B (O subU A .1) (O_unit subU A .1 ° f) x = O_rec B (O subU A .1) ((O_unit subU A .1) ° (O_rec B A f) ° (O_unit subU B)) x).
      pose (foo := O_rec_retr B A f).
      rewrite (inverse (comp_assoc _ _ _)).
      rewrite foo. exact idpath.
    rewrite X; clear X.
    assert (forall U, O_rec B (O subU A .1) (U ° O_unit subU B) x = U x).
      intro U.
      exact (apD10 (O_rec_sect B (O subU A.1) U) x).
    exact (inverse (X (O_unit subU A .1 ° O_rec B A f))).
  Defined.

  Definition function_lift_modal_square (A : Trunc n) (B : subuniverse_Type) (f : A.1 -> B.1.1) : (@equiv_inv _ _ (subU.(O_unit) B.1) (O_modal_equiv B)) ° (function_lift A B.1 f) ° (subU.(O_unit) A) =  f.
    apply path_forall; intro x; unfold composition, function_lift; simpl.
    exact (transport (λ U, O_rec B .1 B (λ x : (B .1) .1, x) U = f x) (inverse (apD10 ((O_rec_retr A (subU.(O) B.1)) ((O_unit subU B.1)°f)) x)) (apD10 (O_rec_retr B.1 B idmap) (f x))).
  Defined.

  Definition function_lift_compose (A B C : Trunc n) ( f : A.1 -> B.1) (g : B.1 -> C.1) :
    (function_lift A C (g°f)) = (function_lift B C g)°(function_lift A B f).
    apply path_forall; intro x; simpl.
    unfold function_lift.
    fold ( (O_unit subU C) ° g).
    fold ( (O_unit subU B) ° f).
    assert ((λ x : A .1, O_unit subU C ((g ° f) x)) = ((((O_unit subU C) ° g) ° f))).
      exact idpath.
    rewrite X; clear X.
    
    assert (O_rec A (O subU C) (((O_unit subU C ° g) ° f)) = O_rec A (O subU C) (((O_rec B (O subU C) (O_unit subU C ° g) ° O_unit subU B) ° f))).
      pose (foo := O_rec_retr B (O subU C) (O_unit subU C ° g)).
      rewrite foo. exact idpath.

    rewrite X; clear X.

    rewrite (inverse (comp_assoc _ _ _)).

    assert (O_rec A (O subU C)
     (O_rec B (O subU C) (O_unit subU C ° g) ° (O_unit subU B ° f)) =
            O_rec A (O subU C)
     (O_rec B (O subU C) (O_unit subU C ° g) ° (O_rec A (O subU B) (O_unit subU B ° f) ° O_unit subU A))).
      pose (foo := O_rec_retr A (O subU B) (O_unit subU B ° f)).
      rewrite foo. exact idpath.
    rewrite X; clear X.

    pose (foo := apD10 (O_rec_sect A (O subU C) (O_rec B (O subU C) (O_unit subU C ° g)
       ° O_rec A (O subU B) (O_unit subU B ° f))) x).

    rewrite comp_assoc.
    unfold O_rec, equiv_inv, composition in *; simpl in *.
    rewrite foo. exact idpath.
  Defined.

  Definition function_lift_square (A B C X : Trunc n) (π1 : X.1 -> A.1) (π2 : X.1 -> B.1) (f : A.1 -> C.1) (g : B.1 -> C.1) (comm : (f°π1) = (g°π2)) : ( (function_lift A C f) ° (function_lift X A π1) ) = ( (function_lift B C g) ° (function_lift X B π2) ).
    unfold function_lift, composition in *; simpl in *.
    apply path_forall; intro x; simpl.

    pose (foo1 := apD10 (function_lift_compose X A C π1 f) x). unfold function_lift, composition in foo1; simpl in foo1.
    pose (foo2 := apD10 (function_lift_compose X B C π2 g) x). unfold function_lift, composition in foo2; simpl in foo2.
    pose (foo3 := ap (λ u, O_rec X (O subU C) (λ x0, O_unit subU C (u x0)) x) (x:=f°π1) (y:=g°π2) comm). simpl in foo3.

    exact ((inverse foo1) @ foo3 @ foo2).
  Defined.

(* The universal property commute with η *)

    Definition equal_fun_modal (A:Trunc n) (B:subuniverse_Type) (f g:(O subU A).1.1 -> B.1.1) (η := O_unit subU A) : ((f°η = g°η) -> (f=g))
    := λ H, ((inverse (eissect _ (IsEquiv := (O_equiv subU A B)) f) @ (ap equiv_inv H) @ (eissect _ (IsEquiv := (O_equiv subU A B)) g))).
    
  Lemma universality_unit_lemma (oA A B: Type) (η : A -> oA) (f g : oA -> B) (inv : (A -> B) -> oA -> B) (π : f°η = g°η) (eisretr : forall x:A -> B, (inv x)°η = x) (eissect : forall x : oA -> B, inv (x ° η) = x) a : apD10 (ap inv π) (η a) = ((apD10 (eisretr (f ° η)) a @ apD10 π a) @ (apD10 (eisretr (g ° η)) a) ^)%path.
    destruct π. simpl. rewrite concat_p1. rewrite concat_pV. exact idpath.
  Defined.
      
  Definition universality_unit (A:Trunc n) (B:subuniverse_Type) (f g:(O subU A).1.1 -> B.1.1) (η := O_unit subU A) (π : (f°η = g°η)) : forall a, apD10 (equal_fun_modal A B π) (η a) = apD10 π a.
    intro a. unfold equal_fun_modal. destruct (O_equiv subU A B). simpl.
    repeat rewrite apD10_pp. rewrite apD10_V. rewrite concat_pp_p.
    apply moveR_Mp. apply moveR_pM. rewrite inv_V.
    assert (apD10 (eisretr (g°η)) a = apD10 (eissect g) (η a)).
    fold η in eisadj; rewrite (eisadj g). apply ap_ap10_.
    rewrite <- X; clear X.
    assert (apD10 (eisretr (f°η)) a =
            apD10 (eissect f) (η a)).
    fold η in eisadj; rewrite (eisadj f). apply ap_ap10_.
    rewrite <- X. clear X.
    apply (universality_unit_lemma equiv_inv π eisretr eissect a).
  Defined.                                                                                                         

(* Dependent product and arrows *)
  Definition subuniverse_forall (A:Type) (B:A -> Trunc n) : (* Theorem 7.7.2 *)
    (forall x, (subU.(subuniverse_HProp) (B x)).1) -> ((subU.(subuniverse_HProp)) (forall x:A, (B x).1 ; trunc_forall (H0 := λ x, (B x).2))).1.
    intro H.
    pose (ev := λ x, (λ (f:(forall x, (B x).1)), f x)).
    pose (ζ := λ x:A, O_rec (∀ x0 : A, (B x0) .1; trunc_forall (H0 := λ x, (B x).2)) (B x; H x) (ev x)).
    pose (h := λ z, λ x, ζ x z).
    simpl in *.
    rewrite <- (subuniverse_iff_O).
    set (η := (O_unit subU (∀ x : A, (B x) .1; trunc_forall))).
    apply O_unit_retract_equiv with (μ := h).
    intro φ.
    unfold h, ζ, ev; clear h; clear ζ; clear ev.
    apply path_forall; intro x.
    pose (foo := @O_rec_retr (∀ x0 : A, (B x0) .1; trunc_forall (H0 := λ x, (B x).2)) (B x; H x) (λ f : ∀ x0 : A, (B x0) .1, f x)).
    exact (apD10 foo φ).
  Defined.

  Definition subuniverse_arrow (A : Type) (B : subuniverse_Type) :
    (subuniverse_HProp subU (A -> B.1.1 ; trunc_arrow (H0 := B.1.2))).1.
    apply subuniverse_forall.
    intro a. exact B.2.
  Defined.

(* Product *)
  Definition subuniverse_product (A B : subuniverse_Type) :
    (subuniverse_HProp subU (A.1.1*B.1.1 ; trunc_prod (H:=A.1.2) (H0 := B.1.2))).1.
    rewrite <- subuniverse_iff_O.

    pose (μ := λ (X : ((O subU (A.1.1 ** B.1.1; trunc_prod (H:=A.1.2) (H0 := B.1.2))) .1) .1),
               (O_rec (A.1.1 ** B.1.1; trunc_prod (H:=A.1.2) (H0 := B.1.2)) (A)
                      (λ x : (A.1.1 ** B.1.1; trunc_prod (H:=A.1.2) (H0 := B.1.2)) .1, (fst x)) X,
                O_rec (A.1.1 ** B.1.1; trunc_prod (H:=A.1.2) (H0 := B.1.2)) (B)
                      (λ x : (A.1.1 ** B.1.1; trunc_prod (H:=A.1.2) (H0 := B.1.2)) .1, (snd x)) X)).
    apply O_unit_retract_equiv with (μ := μ).
    intro x; destruct x as [a b].
    unfold μ; apply path_prod.
    - simpl.
     exact (apD10 (O_rec_retr (A.1.1 ** B.1.1; trunc_prod (H:=A.1.2) (H0 := B.1.2)) A (λ x : (A .1) .1 ** (B .1) .1, fst x)) (a,b)). 
    - simpl.
      exact (apD10 (O_rec_retr (A.1.1 ** B.1.1; trunc_prod (H:=A.1.2) (H0 := B.1.2)) B (λ x : (A .1) .1 ** (B .1) .1, snd x)) (a,b)). 
  Defined.
  
  Definition subuniverse_product_fun (A B : Trunc n) : (O subU (A.1*B.1; trunc_prod (H:=A.2) (H0:=B.2))).1.1 -> (O subU A).1.1*(O subU B).1.1
    := function_lift_modal
         (A.1*B.1; trunc_prod (H:=A.2) (H0:=B.2))
         (((O subU A).1.1*(O subU B).1.1 ; trunc_prod (H := (O subU A).1.2) (H0 := (O subU B).1.2)) ; subuniverse_product (O subU A) (O subU B))
         (λ x, (O_unit subU A (fst x), O_unit subU B (snd x))).

  Definition subuniverse_product_inv (A B : Trunc n) : (O subU A).1.1*(O subU B).1.1 -> (O subU (A.1*B.1 ; trunc_prod (H:=A.2) (H0:=B.2))).1.1.
    intro x. destruct x.
    generalize dependent p; apply O_rec; intro p.
    generalize dependent p0; apply O_rec; intro p0.
    apply (O_unit subU).
    exact (p,p0).
  Defined.

  (* Definition product_universal (A B : Trunc n) (C : subuniverse_Type) : *)
  (*   Equiv ((O subU (A.1 * B.1 ; trunc_prod (H:=A.2) (H0:=B.2))).1.1 -> C.1.1) ((O subU A).1.1*(O subU B).1.1 -> C.1.1). *)
  (*   apply (@equiv_compose' _ (A.1*B.1 -> C.1.1) _). *)
  (*   Focus 2. *)
  (*   exists ((λ f : ((O subU (A .1 ** B .1; trunc_prod)) .1) .1 -> (C .1) .1, f ° O_unit subU (A .1 ** B .1; trunc_prod))). *)
  (*   exact (O_equiv _ _ _). *)

  (*   apply (@equiv_compose' _ (A.1 -> B.1 -> C.1.1) _). *)
  (*   Focus 2. *)
  (*   exists (λ f, λ u v, f (u,v)). *)
  (*   apply isequiv_adjointify with (g := λ u, λ x, u (fst x) (snd x)). *)
  (*   intro x. apply path_forall; intro u; apply path_forall; intro v. exact idpath. *)
  (*   intro x. apply path_forall; intro u. rewrite eta_prod. exact idpath. *)

  (*   apply (@equiv_compose' _ ((O subU A).1.1 -> B.1 -> C.1.1) _). *)
  (*   Focus 2. apply equiv_inverse. *)
  (*   exists (λ f : (((O subU A) .1) .1 -> (existT (λ S, (subuniverse_HProp subU S).1) (existT (λ T, IsTrunc n T) (B .1 -> (C .1) .1) (trunc_arrow (H0 := C.1.2))) (subuniverse_arrow B .1 C)).1.1),  *)
  (*                 f ° O_unit subU A). *)
  (*   exact (O_equiv subU A (( B.1 -> C.1.1 ; trunc_arrow (H0 := C.1.2)) ; subuniverse_arrow B.1 C)). *)
    
  (*   apply (@equiv_compose' _ ((O subU A).1.1 -> (O subU B).1.1 -> C.1.1) _). *)
  (*   exists (λ f, λ u, f (fst u) (snd u)). *)
  (*   apply isequiv_adjointify with (g := λ f, λ u v, f (u,v)). *)
  (*   intro x. apply path_forall; intro u. rewrite eta_prod. exact idpath. *)
  (*   intro x. apply path_forall; intro u. apply path_forall; intro v. exact idpath. *)

  (*   apply equiv_postcompose'. *)
  (*   apply equiv_inverse. *)
  (*   exists (λ f : ((O subU B) .1) .1 -> (C .1) .1, f ° O_unit subU B). *)
  (*   exact (O_equiv subU B C). *)
  (* Defined. *)

  Definition product_universal (A B : Trunc n) (C : subuniverse_Type) :
    Equiv (A.1 * B.1 -> C.1.1) ((O subU A).1.1*(O subU B).1.1 -> C.1.1).
    (* apply (@equiv_compose' _ (A.1*B.1 -> C.1.1) _). *)
    (* Focus 2. *)
    (* exists ((λ f : ((O subU (A .1 ** B .1; trunc_prod)) .1) .1 -> (C .1) .1, f ° O_unit subU (A .1 ** B .1; trunc_prod))). *)
    (* exact (O_equiv _ _ _). *)

    apply (@equiv_compose' _ (A.1 -> B.1 -> C.1.1) _).
    Focus 2.
    exists (λ f, λ u v, f (u,v)).
    apply isequiv_adjointify with (g := λ u, λ x, u (fst x) (snd x)).
    intro x. apply path_forall; intro u; apply path_forall; intro v. exact idpath.
    intro x. apply path_forall; intro u. rewrite eta_prod. exact idpath.

    apply (@equiv_compose' _ ((O subU A).1.1 -> B.1 -> C.1.1) _).
    Focus 2. apply equiv_inverse.
    exists (λ f : (((O subU A) .1) .1 -> (existT (λ S, (subuniverse_HProp subU S).1) (existT (λ T, IsTrunc n T) (B .1 -> (C .1) .1) (trunc_arrow (H0 := C.1.2))) (subuniverse_arrow B .1 C)).1.1), 
                  f ° O_unit subU A).
    exact (O_equiv subU A (( B.1 -> C.1.1 ; trunc_arrow (H0 := C.1.2)) ; subuniverse_arrow B.1 C)).
    
    apply (@equiv_compose' _ ((O subU A).1.1 -> (O subU B).1.1 -> C.1.1) _).
    exists (λ f, λ u, f (fst u) (snd u)).
    apply isequiv_adjointify with (g := λ f, λ u v, f (u,v)).
    intro x. apply path_forall; intro u. rewrite eta_prod. exact idpath.
    intro x. apply path_forall; intro u. apply path_forall; intro v. exact idpath.

    apply equiv_postcompose'.
    apply equiv_inverse.
    exists (λ f : ((O subU B) .1) .1 -> (C .1) .1, f ° O_unit subU B).
    exact (O_equiv subU B C).
  Defined.

  Definition product_universal' (A B : Trunc n) (C : subuniverse_Type) :
    (A.1 * B.1 -> C.1.1) = ((O subU A).1.1*(O subU B).1.1 -> C.1.1).
    apply univalence_axiom; exact (product_universal A B C).
  Defined.
  
  (* Definition subuniverse_product' (A B : Trunc n) : Equiv  (O subU (A.1*B.1 ; trunc_prod (H:=A.2) (H0 := B.2))).1.1 ((O subU A).1.1*(O subU B).1.1). *)

  (*   pose (eta := λ u:A.1*B.1, (O_unit subU A (fst u), O_unit subU B (snd u))). *)
    
  (*   pose (foo := product_universal' A B (((O subU A).1.1*(O subU B).1.1 ; trunc_prod (H := (O subU A).1.2) (H0 := (O subU B).1.2)) ; subuniverse_product (O subU A) (O subU B))); simpl in foo. *)

  (*   (* rewrite foo in eta. *) *)
  (*   exists (subuniverse_product_fun A B). *)
  (*   apply isequiv_adjointify with (g:= equiv_fun _ _ foo idmap). *)
  (*   - intro x. unfold subuniverse_product_fun, foo; simpl. unfold function_lift_modal; simpl. unfold compose in *; simpl in *. *)
      


  (* Theorem 7.7.4 *)
  Definition subuniverse_sigma :
    (forall (A:subuniverse_Type) (B:A.1.1 -> subuniverse_Type), (subuniverse_HProp subU ({x:A.1.1 & (B x).1.1} ; trunc_sigma (H:=A.1.2) (H0 := λ x, (B x).1.2))).1) <->
    (forall (A:Trunc n) (B: (O subU A).1.1 -> subuniverse_Type) (g : forall (a:A.1), (B (O_unit subU A a)).1.1), {f : forall (z:(O subU A).1.1), (B z).1.1 & forall a:A.1, f (O_unit subU A a) = g a}).
    split.
    - intro H. intros A B g.
      pose (Z := existT (λ T, (subuniverse_HProp subU T).1) ({z:(O subU A).1.1 & (B z).1.1} ; trunc_sigma (H:=(O subU A).1.2) (H0:=λ z, (B z).1.2)) (H (O subU A) B)).
      pose (g' :=( λ a:A.1, (O_unit subU A a ; g a)) : A.1 -> Z.1.1).
      pose (f' := O_rec _ _ g').
      pose (eqf :=λ a:A.1, (apD10 (O_rec_retr _ _ g') a)). unfold composition in eqf. fold f' in eqf.
      pose (g'' := λ x, (f' x).1).
      pose (f'' := λ x:(O subU A).1.1, x).
      pose (eq'' := path_forall _ _ (λ x, @ap _ _ pr1 _ _ (eqf x))).
      assert (g'' ° (O_unit subU A) = f'' ° (O_unit subU A)).
        exact eq''.
      pose (eq''' := apD10 (equal_fun_modal A (O subU A) (g:=f'') (f:=g'') (eq''))). unfold f'', g'' in eq'''; simpl in eq'''.
      pose (f := λ z, (f' z).2). simpl in f.
      set (η := O_unit subU A) in *.

      exists (λ z, transport (λ u, (B u).1.1) (eq''' z) (f z)).
      intro a.

      unfold f. unfold g' in eqf; simpl in eqf.
      pose (p := projT1_path (eqf a)). simpl in p.
      pose (q := projT2_path (eqf a)). simpl in q.

      rewrite <- q. 
      assert ( (eq''' (η a)) =  (eqf a) ..1).
        unfold eq''', projT1_path, eqf, q, p, f, eq''', eq'', f'', g'', eqf, f', g', Z, η in *; simpl in *.
        rewrite universality_unit. rewrite apD10_fed. exact idpath.
      exact (ap (λ v, transport (λ u, ((B u) .1) .1) v (f' (η a)) .2) X0).
    - intros H A B.
      pose (h := λ x, O_rec ({x:A.1.1 & (B x).1.1};trunc_sigma (H := A.1.2) (H0 := λ u, (B u).1.2)) A pr1 x).
      pose (p := λ z, apD10 (O_rec_retr ({x : (A .1) .1 | ((B x) .1) .1}; trunc_sigma (H := A.1.2) (H0 := λ u, (B u).1.2)) A pr1) z).
      pose (C := λ w, B(h w)).
      pose (g := λ z, (transport (λ u, (B u).1.1) (inverse (p z)) z.2)).
      simpl in *.
      specialize (H ({x:A.1.1 & (B x).1.1};trunc_sigma (H := A.1.2) (H0 := λ u, (B u).1.2)) C g).
      destruct H as [f q]. simpl in q.
      pose (k := (λ w, (h w; f w)) : (O subU ({x:A.1.1 & (B x).1.1};trunc_sigma (H := A.1.2) (H0 := λ u, (B u).1.2))).1.1 -> ({x:A.1.1 & (B x).1.1};trunc_sigma (H := A.1.2) (H0 := λ u, (B u).1.2)).1); simpl in k.

      rewrite <- subuniverse_iff_O.
      apply O_unit_retract_equiv with (μ := k).

      intro x; destruct x as [x1 x2]. unfold k.
      apply eq_dep_sumT with (prf := (p (x1;x2))).
      rewrite (q (x1;x2)).
      exact idpath.
  Defined.
      
  Lemma is_trunc_eq (S S':subuniverse_Type) : IsTrunc n (S=S').
    apply istrunc_paths.
    apply (subuniverse_Type_is_TruncSn).
  Defined.


  Lemma istrunc_pullback (A B C : Trunc n) (f : A.1 -> C.1) (g : B.1 -> C.1) : IsTrunc n (pullback f g).
    unfold pullback.
    apply (@trunc_sigma _ _ _ A.2).
    intro a.
    apply (@trunc_sigma _ _ _ B.2).
    intro b.
    apply istrunc_paths.
    apply (trunc_succ (H:= C.2)).
  Defined.

(*   Definition pullback_μ_fun (A B C : subuniverse_Type) (f : A.1.1 -> C.1.1) (g : B.1.1 -> C.1.1) :  (O subU (pullback f g; istrunc_pullback A .1 B .1 C .1 f g)).1.1 -> {a:A.1.1 | B.1.1}. *)
(*     intro x. *)
(*     exists (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) A *)
(*   (λ x0 : (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) .1, x0 .1) x). *)
(*     exact (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) B *)
(*   (λ x0 : (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) .1, (x0 .2) .1) *)
(*   x). *)
(*   Defined. *)

(*   Definition pullback_μ_eq (A B C : subuniverse_Type) (f : A.1.1 -> C.1.1) (g : B.1.1 -> C.1.1) (x : (O subU (pullback f g; istrunc_pullback A .1 B .1 C .1 f g)).1.1) : (f (pullback_μ_fun A B C f g x).1 = g (pullback_μ_fun A B C f g x).2). *)
    
(*     assert (foo := apD10 (@function_lift_square A.1 B.1 C.1 ((pullback f g; istrunc_pullback A .1 B .1 C .1 f g)) pr1 (λ x, x.2.1) f g (path_forall _ _ (λ u, u.2.2))) x). *)
    
(*     assert (p := apD10 (function_lift_modal_square A.1 C f) (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) A (λ x0 : (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) .1, x0 .1) x)). *)

(*     assert (q := apD10 (function_lift_modal_square B.1 C g) (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) B (λ x0 : (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) .1, x0.2.1) x)). *)
    
(*     assert ( *)
(*         O_rec C .1 C (λ x : (C .1) .1, x) *)
(*               (function_lift A .1 C .1 f *)
(*                              (O_unit subU A .1 *)
(*                                      (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) A *)
(*                                             (λ x0 : pullback f g, x0 .1) x))) *)
(*         = *)
(*         O_rec C .1 C (λ x : (C .1) .1, x) *)
(*               (function_lift B .1 C .1 g *)
(*                              (O_unit subU B .1 *)
(*                                      (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) B *)
(*                                             (λ x0 : pullback f g, (x0 .2) .1) x)))). *)
(*     apply ap. unfold function_lift. simpl. *)

(*     assert ( AA : *)
(*                O_rec A .1 (O subU C .1) (λ x0 : (A .1) .1, O_unit subU C .1 (f x0)) *)
(*                      (O_unit subU A .1 *)
(*                              (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) A *)
(*                                     (λ x0 : pullback f g, x0 .1) x)) *)
(*                = *)
(*                O_rec A .1 (O subU C .1) (λ x0 : (A .1) .1, O_unit subU C .1 (f x0)) *)
(*                      ( *)
(*                        (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) (O subU A.1) *)
(*                               (λ x0 : pullback f g, O_unit subU A.1 x0 .1) x))). *)
(*     apply ap. apply O_rec_O_unit. *)

(*     assert (BB : *)
(*               O_rec B .1 (O subU C .1) (λ x0 : (B .1) .1, O_unit subU C .1 (g x0)) *)
(*                     (O_unit subU B .1 *)
(*                             (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) B *)
(*                                    (λ x0 : pullback f g, (x0 .2) .1) x)) *)
(*               = *)
(*               O_rec B .1 (O subU C .1) (λ x0 : (B .1) .1, O_unit subU C .1 (g x0)) *)
(*                     ( *)
(*                       (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) (O subU B.1) *)
(*                              (λ x0 : pullback f g, O_unit subU B.1 (x0 .2) .1) x))). *)
(*     apply ap; apply O_rec_O_unit. *)

(*     apply (transport (λ u, u = O_rec B .1 (O subU C .1) (λ x0 : (B .1) .1, O_unit subU C .1 (g x0)) *)
(*                                      (O_unit subU B .1 *)
(*                                              (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) B *)
(*                                                     (λ x0 : pullback f g, (x0 .2) .1) x))) (inverse AA)). *)
(*     apply (transport (λ u, O_rec A .1 (O subU C .1) (λ x0 : (A .1) .1, O_unit subU C .1 (f x0)) *)
(*                                  (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) *)
(*                                         (O subU A .1) (λ x0 : pullback f g, O_unit subU A .1 x0 .1) x)  = u) (inverse BB)). *)

(*     clear AA; clear BB. *)
(*     exact foo. *)
(*     exact ((inverse p) @ X @ q). *)
(*   Defined. *)

(*   Lemma pullback_μ (A B C : subuniverse_Type) (f : A.1.1 -> C.1.1) (g : B.1.1 -> C.1.1) (x : (O subU (pullback f g; istrunc_pullback A .1 B .1 C .1 f g)).1.1) : pullback f g. *)
(*     exists (pullback_μ_fun A B C f g x).1. *)
(*     exists (pullback_μ_fun A B C f g x).2. *)
(*     exact (pullback_μ_eq A B C f g x). *)
(*   Defined. *)
  
  Lemma pullback_sheaves (A B C : subuniverse_Type) (f : A.1.1 -> C.1.1) (g : B.1.1 -> C.1.1) : (subU.(subuniverse_HProp) (pullback f g ; istrunc_pullback A.1 B.1 C.1 f g)).1.
(*     rewrite <- subuniverse_iff_O. *)
(*     apply O_unit_retract_equiv with (μ := pullback_μ A B C f g). *)
(*     intro x; destruct x as [F [G prf]]; simpl in *. *)
(*     unfold pullback_μ; simpl. *)
    
(*     pose (foo := apD10 (O_rec_retr (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) A (λ x : pullback f g, x .1)) (F;(G;prf))); unfold composition in foo; simpl in foo. *)
(*     pose (bar := apD10 (O_rec_retr (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) B (λ x : pullback f g, x .2.1)) (F;(G;prf))); unfold composition in bar; simpl in bar. *)

(*     assert ( *)
(*         (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) A *)
(*                (λ x0 : pullback f g, x0 .1) *)
(*                (O_unit subU (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) *)
(*                        (F; (G; prf))); *)
(*          (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) B *)
(*                 (λ x0 : pullback f g, (x0 .2) .1) *)
(*                 (O_unit subU (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) *)
(*                         (F; (G; prf))); *)
(*           pullback_μ_eq A B C f g *)
(*                         (O_unit subU (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) *)
(*                                 (F; (G; prf))))) *)
(*         = *)
(*         existT (λ U, {b:B.1.1 | f U = g b}) F *)
(*          (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) B *)
(*                 (λ x0 : pullback f g, (x0 .2) .1) *)
(*                 (O_unit subU (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) *)
(*                         (F; (G; prf))); *)
(*           transport *)
(*             (λ U, f U = g (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) B *)
(*                                  (λ x0 : pullback f g, (x0 .2) .1) *)
(*                                  (O_unit subU (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) *)
(*                                          (F; (G; prf))))) *)
(*             foo *)
(*             (pullback_μ_eq A B C f g *)
(*                            (O_unit subU (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) *)
(*                                    (F; (G; prf))))) *)
(*       ). *)

(*     rewrite <- foo. *)
(*     apply eq_dep_sumT with (prf := idpath). simpl. exact idpath. *)
(*     rewrite X; clear X. *)
    
(*     assert ( *)
(*         (F; *)
(*          (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) B *)
(*                 (λ x0 : pullback f g, (x0 .2) .1) *)
(*                 (O_unit subU (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) *)
(*                         (F; (G; prf))); *)
(*           transport *)
(*             (λ U : (A .1) .1, *)
(*                    f U = *)
(*                    g *)
(*                      (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) B *)
(*                             (λ x0 : pullback f g, (x0 .2) .1) *)
(*                             (O_unit subU (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) *)
(*                                     (F; (G; prf))))) foo *)
(*             (pullback_μ_eq A B C f g *)
(*                            (O_unit subU (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) *)
(*                                    (F; (G; prf)))))) *)
(*         = *)
(*         existT (λ U, {b:B.1.1 | f U = g b}) F *)
(*          (existT (λ U:B.1.1, f F = g U) G *)
(*           (transport *)
(*             (λ U : B.1.1, f F = g U) *)
(*             bar *)
(*             (transport *)
(*             (λ U : (A .1) .1, *)
(*                    f U = *)
(*                    g *)
(*                      (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) B *)
(*                             (λ x0 : pullback f g, (x0 .2) .1) *)
(*                             (O_unit subU (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) *)
(*                                     (F; (G; prf))))) foo *)
(*             (pullback_μ_eq A B C f g *)
(*                            (O_unit subU (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) *)
(*                                    (F; (G; prf))))))) *)
(*       ). *)
(*     rewrite <- bar. apply eq_dep_sumT with (prf := idpath). simpl. *)
(*     apply eq_dep_sumT with (prf := idpath). simpl. exact idpath. *)
(*     rewrite X; clear X. *)
     
(*     repeat apply eq_dep_sumT with (prf := idpath); simpl. *)

(*     apply (moveR_transport_p (λ U : (B .1) .1, f F = g U) bar) . *)
(*     apply (moveR_transport_p (λ U : (A .1) .1, *)
(*       f U = *)
(*       g *)
(*         (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) B *)
(*            (λ x0 : pullback f g, (x0 .2) .1) *)
(*            (O_unit subU (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) *)
(*               (F; (G; prf))))) foo). *)
(*     unfold foo, bar, pullback_μ_eq. simpl. clear foo; clear bar. *)
(*     set (AA := (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) A *)
(*            (λ x0 : pullback f g, x0 .1) *)
(*            (O_unit subU (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) *)
(*               (F; (G; prf))))). *)
(*     set (BB := (O_rec (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) B *)
(*                    (λ x0 : pullback f g, (x0 .2) .1) *)
(*                    (O_unit subU *)
(*                       (pullback f g; istrunc_pullback A .1 B .1 C .1 f g) *)
(*                       (F; (G; prf))))). *)

(*     repeat rewrite (transport_paths_Fl). repeat rewrite (transport_paths_Fr). *)
(*     hott_simpl. *)
(*     unfold function_lift_modal, function_lift_square, function_lift_compose, function_lift_modal_square, path_forall, composition. simpl. *)
(*     repeat rewrite (eisretr apD10). hott_simpl. *)
(*     (* rewrite equalf_fed. rewrite equalf_fed. *) *)
(*     repeat rewrite (transport_paths_Fl). repeat rewrite inverse_ap. *)
(*     repeat rewrite inv_V. *)
(*     hott_simpl. *)
    

(* (* We know that AA=F and BB=G, but can't rewrite now *) *)

(*     unfold path_forall. *)

(*     (*          admit. *) *)
  Admitted.

  Lemma istrunc_unit (m:trunc_index) : IsTrunc m Unit.
    induction m.
    - exact contr_unit.
    - apply trunc_succ.
  Defined.
  
  (* Lemma unit_modal : (subU.(subuniverse_HProp) (existT (λ T, IsTrunc n T) (Unit) (istrunc_unit n))).1. *)
  (*   rewrite <- subuniverse_iff_O. *)
  (*   apply O_unit_retract_equiv with (μ := λ x:(subU.(O) (Unit;istrunc_unit n)).1.1, tt). *)
  (*   intro u. *)
  (*   destruct u; exact idpath. *)
  (* Defined. *)

  Lemma paths_are_sheaves (S:subuniverse_Type) (x y:S.1.1) : (subuniverse_HProp subU (x=y ; istrunc_paths S.1.1 n x y (H:= @trunc_succ _ _ S.1.2))).1.
    (* assert ((x=y) = (@pullback Unit Unit S.1.1 (λ u, x) (λ u, y))). *)
    (*   apply univalence_axiom. *)
    (*   unfold pullback. *)
    (*   exists (λ X, existT (λ _, {_ : Unit | x=y}) tt (existT (λ _, x=y) tt X)). *)
    (*   apply isequiv_adjointify with (g := λ X : {_ : Unit | {_ : Unit | x=y}}, X.2.2). *)
    (*   - intro u. destruct u as [tt1 [tt2 u]]. simpl. *)
    (*     destruct tt1; destruct tt2. exact idpath. *)
    (*   - intro u. destruct u. exact idpath. *)
    (* - assert ((x = y; istrunc_paths (H := @trunc_succ _ _ S.1.2) (S .1).1 n x y) = (@pullback Unit Unit S.1.1 (λ u, x) (λ u, y) ; istrunc_pullback (Unit;istrunc_unit n) (Unit;istrunc_unit n) S.1 (λ u, x) (λ u, y))). *)
    (*   apply eq_dep_sumT with (prf := X). *)
    (*   apply allpath_hprop. *)
    (*   rewrite X0. simpl. *)
    (*   apply (pullback_sheaves ((Unit;istrunc_unit n);unit_modal) ((Unit;istrunc_unit n);unit_modal) S). *)
  Admitted.
 
End Reflective_Subuniverse.