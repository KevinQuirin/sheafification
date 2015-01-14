Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import univalence lemmas epi_mono equivalence sub_object_classifier colimit nat_lemmas cech_nerve.

Set Universe Polymorphism.
Global Set Primitive Projections.
Set Implicit Arguments.

Section Preliminary .

Context `{ua: Univalence}.
Context `{fs: Funext}.

(* Definition 7.7.1 *)
Record subuniverse_struct n := Build_subuniverse_struct { 
  
  subuniverse_HProp : forall (T:Trunk n), HProp  ;
    
  O : Trunk n -> {T : Trunk n & (subuniverse_HProp T).1} ;

  O_unit : forall T, T.1 -> (O T).1.1;

  O_equiv : forall (P : Trunk n) (Q :{T : Trunk n & (subuniverse_HProp T).1}),
              IsEquiv (fun f : (O P).1.1 -> Q.1.1 => f o (O_unit P)) 
}.

End Preliminary.

Section Reflective_Subuniverse.

  Variable n:trunc_index.

  Variable subU : subuniverse_struct n.

  Context `{ua: Univalence}.
  Context `{fs: Funext}.
  
  Definition subuniverse_Type := 
  {T : Trunk n & pr1 (subU.(subuniverse_HProp) T)}.
  
  Definition subuniverse_Type_is_TrunkSn : IsTrunc (trunc_S n) subuniverse_Type.
    unfold subuniverse_Type.
    apply (@trunc_sigma _ (fun T => (subuniverse_HProp subU T) .1) _ (Tn_is_TSn (n:=n))).
    intro T. apply IsHProp_IsTrunc. apply (pr2 (subU.(subuniverse_HProp) T)).
  Defined.

  Definition O_rec (P : Trunk n) (Q : subuniverse_Type) :
    (P.1 -> Q.1.1) -> (subU.(O) P).1.1 -> Q.1.1 := 
    (@equiv_inv _ _ _ (subU.(O_equiv) _ _)).

  Definition O_rec_retr (P : Trunk n) (Q : subuniverse_Type) f
  : O_rec _ _ f o subU.(O_unit) _ = f :=
    @eisretr _ _ _ (subU.(O_equiv) P Q) f.

  Definition O_rec_sect (P : Trunk n) (Q : subuniverse_Type) f :=
    @eissect _ _ _ (subU.(O_equiv) P Q) f.
  
  Definition O_rec_const (P:Trunk n) (Q:subuniverse_Type) y : O_rec P Q (λ _, y) = (λ _, y)
    := eissect _ (IsEquiv := O_equiv subU P Q) (λ x, y).

  Lemma transport_O_rec (P:Trunk n) (Q R:subuniverse_Type) (B:= λ S:subuniverse_Type, S.1.1) (eq : Q = R) f r:
    transport B eq (O_rec P Q f r) = O_rec P R (λ v, transport B eq (f v)) r.
    destruct eq. simpl. reflexivity.
  Defined.
  
  Definition O_unit_retract_equiv (T:Trunk n) (μ : (subU.(O) T).1.1 -> T.1) (η := subU.(O_unit) T) : Sect η μ -> IsEquiv η.
    unfold Sect; intros H. apply isequiv_adjointify with (g:=μ).
    - assert (η o μ o η = idmap o η).
      apply (ap (fun x => η o x)).
      apply path_forall; intro y.
      exact (H y).
      exact (apD10 (@equiv_inj _ _ _ (subU.(O_equiv) T (subU.(O) T)) (η o μ) idmap X)).
    - exact H.
  Defined.
    
  Instance O_modal_equiv (P : subuniverse_Type) : IsEquiv (subU.(O_unit) P.1).
  apply O_unit_retract_equiv with (μ := (O_rec P.1 P idmap)).
  pose (f := O_rec_retr P.1 P idmap). 
  intro. eapply apD10 in f. exact (f x).
  Defined.

  Definition unique_subuniverse : forall (T T' : subuniverse_Type), pr1 T = pr1 T' -> T = T'. 
    intros. destruct T, T'. eapply (eq_dep_subset' (λ x, let (a, _) := subuniverse_HProp subU x in a) _ _ _ X). 
    Grab Existential Variables. intro. simpl. exact ((subuniverse_HProp subU a) .2).
  Defined.

  Definition isequiv_unique_subuniverse (T T':subuniverse_Type)
  : IsEquiv (unique_subuniverse T T').
    apply isequiv_adjointify with (g := λ p, p..1).
     - intro p; destruct p.
      unfold unique_subuniverse; simpl.
      destruct T as [[T TrT] ShT]. simpl.
      unfold eq_dep_subset. simpl.
      apply (transport (λ U, path_sigma' (λ x : Trunk n, let (a, _) := subuniverse_HProp subU x in a) 1 U = 1) (@contr (ShT = ShT) ((subuniverse_HProp subU (T;TrT)).2 ShT ShT) 1)^).
      reflexivity.
    - intro p. unfold unique_subuniverse, eq_dep_subset. 
      destruct T as [T ShT], T' as [T' ShT']; simpl in *. destruct p.
      assert (ShT = ShT').
      apply @path_ishprop.
      exact (subuniverse_HProp subU T).2.
      destruct X.
      apply (transport (λ U, ap pr1
                                (path_sigma'
                                   (λ x : Trunk n, let (a, _) := subuniverse_HProp subU x in a) 1
                                   U) = 1) (@contr (ShT = ShT) ((subuniverse_HProp subU T).2 ShT ShT) 1)^).
      reflexivity.
  Defined.
      
  Definition O_modal (T:subuniverse_Type) : T = subU.(O) T.1.
    apply unique_subuniverse. apply truncn_unique.
    apply path_universe_uncurried.
    exact (BuildEquiv _ _ (subU.(O_unit) (pr1 T)) (O_modal_equiv _)).
  Defined.

  Definition O_invol : forall T, (O subU) ( pr1 ((O subU) T)) = O subU T.
    intro T; symmetry; apply O_modal.
  Defined.

  Definition subuniverse_struct_transport T U (f : (T.1 <~> U.1)%equiv) :
    (subU.(subuniverse_HProp) T).1 -> (subU.(subuniverse_HProp) U).1.
    apply path_universe_uncurried in f. apply truncn_unique in f. rewrite f.
    intro x; exact x.
  Defined.
  
  Definition subuniverse_iff_O (T:Trunk n) : 
    IsEquiv (subU.(O_unit) T) = pr1 (subU.(subuniverse_HProp) T).
    apply univalence_hprop. apply hprop_isequiv. apply (pr2 (subU.(subuniverse_HProp) T)).
    split.
    - exact (fun X => subuniverse_struct_transport _ _ (BuildEquiv _ _ _ (isequiv_inverse _ (feq:=X))) (pr2 (subU.(O) T))). 
    - exact (fun X => O_modal_equiv (T;X)).
  Defined.


(* ○-lift of functions *)
  
  Definition function_lift (A B : Trunk n) (f : A.1 -> B.1) : (subU.(O) A).1.1 -> (subU.(O) B).1.1.
    apply O_rec; intro x; apply subU.(O_unit); apply f; exact x.
  Defined.

  Definition function_lift_modal (A:Trunk n) (B:subuniverse_Type) (f : A.1 -> B.1.1) : (O subU A).1.1 -> B.1.1.
    apply O_rec. exact f.
  Defined.

  Notation "'○' f" := (function_lift _ _ f) (at level 0).
  Notation "'○' f" := (function_lift_modal _ _ f) (at level 0).
  
  Lemma reflect_factoriality_pre
        (X:Trunk n)
        (Y Z:subuniverse_Type)
        (g : Y.1.1 -> Z.1.1)
        (f : X.1 -> Y.1.1)
  : g o (O_rec X Y f) = O_rec X Z (g o f).
  Proof.
    apply (@equiv_inj _ _ _ (O_equiv subU X Z) (g o (O_rec X Y f)) (O_rec X Z (g o f))).
    transitivity (g o f).
    - apply (ap (λ f, g o f)).
      exact (O_rec_retr X Y f).
    - exact (O_rec_retr X Z (g o f))^.
  Defined.

  Lemma reflect_factoriality_post
        (X Y:Trunk n)
        (Z:subuniverse_Type)
        (g:Y.1 -> Z.1.1)
        (f:X.1 -> Y.1)
  : (O_rec Y Z g) o (function_lift X Y f) = O_rec X Z (g o f).
  Proof.
    transitivity (O_rec X Z ((O_rec Y Z g) o (O_unit subU Y o f))).
    - apply reflect_factoriality_pre.
    - apply ap.
      transitivity (((O_rec Y Z g) o O_unit subU Y) o f).
      reflexivity.
      exact (ap (λ u, u o f) (O_rec_retr Y Z g)).
  Defined.

  Lemma reflect_functoriality
        (X Y Z:Trunk n)
        (g:Y.1 -> Z.1)
        (f:X.1 -> Y.1)
  : (function_lift Y Z g) o (function_lift X Y f) = function_lift X Z (g o f).
    apply reflect_factoriality_post.
  Defined.

  Lemma O_rec_O_unit (A : subuniverse_Type) (B : Trunk n) (f : B.1 -> A.1.1) (x : (O subU B).1.1) :
    O_unit subU A.1 (O_rec B A f x) = O_rec B (O subU A.1) ((O_unit subU A.1) o f) x.
    assert (O_rec B (O subU A .1) (O_unit subU A .1 o f) x = O_rec B (O subU A .1) ((O_unit subU A .1) o (O_rec B A f) o (O_unit subU B)) x).
      pose (foo := O_rec_retr B A f).
      apply (ap (fun u => O_rec B (O subU A.1) u x)).
      apply (ap (fun u => O_unit subU A.1 o u)).
      exact foo^.
    rewrite X; clear X.
    assert (forall U, O_rec B (O subU A .1) (U o O_unit subU B) x = U x).
      intro U.
      exact (apD10 (O_rec_sect B (O subU A.1) U) x).
    exact (inverse (X (O_unit subU A .1 o O_rec B A f))).
  Defined.

  Definition function_lift_modal_square (A : Trunk n) (B : subuniverse_Type) (f : A.1 -> B.1.1) : (@equiv_inv _ _ (subU.(O_unit) B.1) (O_modal_equiv B)) o (function_lift A B.1 f) o (subU.(O_unit) A) =  f.
    apply path_forall; intro x; unfold function_lift; simpl.
    exact (transport (λ U, O_rec B .1 B (λ x : (B .1) .1, x) U = f x) (inverse (apD10 ((O_rec_retr A (subU.(O) B.1)) ((O_unit subU B.1) o f)) x)) (apD10 (O_rec_retr B.1 B idmap) (f x))).
  Defined.

  Definition function_lift_compose (A B C : Trunk n) ( f : A.1 -> B.1) (g : B.1 -> C.1) :
    (function_lift A C (g o f)) = (function_lift B C g) o (function_lift A B f).
    apply path_forall; intro x; simpl.
    unfold function_lift.
    (* fold ( (O_unit subU C) o g). *)
    (* fold ( (O_unit subU B) o f). *)
    (* assert ((λ x : A .1, O_unit subU C ((g o f) x)) = ((((O_unit subU C) o g) o f))). *)
      (* reflexivity. *)
    (* rewrite X; clear X. *)
    
    assert (O_rec A (O subU C) (((O_unit subU C o g) o f)) = O_rec A (O subU C) (((O_rec B (O subU C) (O_unit subU C o g) o O_unit subU B) o f))).
      pose (foo := O_rec_retr B (O subU C) (O_unit subU C o g)).
      apply (transport (λ U, _ = O_rec _ _ (λ x0, U (f x0))) foo^). reflexivity.
    rewrite X; clear X.

    assert (O_rec A (O subU C)
     (O_rec B (O subU C) (O_unit subU C o g) o (O_unit subU B o f)) =
            O_rec A (O subU C)
     (O_rec B (O subU C) (O_unit subU C o g) o (O_rec A (O subU B) (O_unit subU B o f) o O_unit subU A))).
      pose (foo := O_rec_retr A (O subU B) (O_unit subU B o f)).
      apply (transport (λ U, _ = O_rec _ _ (λ x0, O_rec _ _ _ (U x0))) foo^). reflexivity.
    etransitivity. exact (ap10 X x).

    pose (foo := apD10 (O_rec_sect A (O subU C) (O_rec B (O subU C) (O_unit subU C o g)
       o O_rec A (O subU B) (O_unit subU B o f))) x).

    unfold O_rec, equiv_inv in *; simpl in *.
    rewrite foo. reflexivity.
  Defined.

  Definition function_lift_square (A B C X : Trunk n) (π1 : X.1 -> A.1) (π2 : X.1 -> B.1) (f : A.1 -> C.1) (g : B.1 -> C.1) (comm : (f o π1) = (g o π2)) : ( (function_lift A C f) o (function_lift X A π1) ) = ( (function_lift B C g) o (function_lift X B π2) ).
    unfold function_lift in *; simpl in *.
    apply path_forall; intro x; simpl.

    pose (foo1 := apD10 (function_lift_compose X A C π1 f) x). unfold function_lift in foo1; simpl in foo1.
    pose (foo2 := apD10 (function_lift_compose X B C π2 g) x). unfold function_lift in foo2; simpl in foo2.
    pose (foo3 := ap (λ u, O_rec X (O subU C) (λ x0, O_unit subU C (u x0)) x) (x:=f o π1) (y:=g o π2) comm). simpl in foo3.

    exact ((inverse foo1) @ foo3 @ foo2).
  Defined.

  Definition function_lift_idmap A : function_lift A A idmap = idmap
    := O_rec_sect A (O subU A) idmap.

  Lemma function_lift_equiv A B f 
  : IsEquiv f -> IsEquiv (function_lift A B f).
    intro H.
    eapply (isequiv_adjointify (function_lift A B f) (function_lift B A (@equiv_inv A.1 B.1 f H))).
    - intro x.
      etransitivity; try exact (ap10 (reflect_functoriality B A B f equiv_inv) x).
      etransitivity; try exact (ap10 (function_lift_idmap B) x).
      apply (ap (λ u, function_lift B B u x)).
      apply path_forall; intro.
      apply eisretr.
    - intro y.
      etransitivity; try exact (ap10 (reflect_functoriality A B A equiv_inv f) y).
      etransitivity; try exact (ap10 (function_lift_idmap A) y).
      apply (ap (λ u, function_lift A A u y)).
      apply path_forall; intro.
      apply eissect.
  Defined.

  Lemma function_lift_transport A B (p:A=B)
  : ((ap (O subU) p)..1..1) = (@path_universe _ (O subU A).1.1 (O subU B).1.1 (function_lift A B (transport idmap p..1)) (function_lift_equiv A B (f := (equiv_path A.1 B.1 p..1)) _)) .
    destruct p. simpl.
    unfold path_universe, path_universe_uncurried.
    apply (@equiv_inj _ _ _ (isequiv_equiv_path _ _)).
    rewrite eisretr. apply equal_equiv. simpl.
    apply path_forall; intro a. simpl.
    unfold function_lift. simpl.
    exact ((ap10 (O_rec_sect A (O subU A) idmap) a)^).
  Qed.

(* The universal property commute with η *)

  Definition equal_fun_modal (A:Trunk n) (B:subuniverse_Type) (f g:(O subU A).1.1 -> B.1.1) (η := O_unit subU A) : ((f o η = g o η) -> (f=g))
    := λ H, ((inverse (eissect _ (IsEquiv := (O_equiv subU A B)) f) @ (ap equiv_inv H) @ (eissect _ (IsEquiv := (O_equiv subU A B)) g))).
    
  Lemma universality_unit_lemma_lemma (oA A B: Type) (η : A -> oA) (f g : A -> B) (inv : (A -> B) -> oA -> B) (π : f = g) (eisretr : forall x:A -> B, (inv x) o η = x) (eissect : forall x : oA -> B, inv (x o η) = x) a
  : apD10 (ap inv π) (η a) = ((apD10 (eisretr f) a @ apD10 π a) @ (apD10 (eisretr g) a) ^)%path.
    destruct π.
    hott_simpl.
  Qed.
    
  Lemma universality_unit_lemma  (oA A: Type) (B:Type) (η : A -> oA) (f g : oA -> B) (inv : (A -> B) -> oA -> B) (π : f o η = g o η) (eisretr : forall x:A -> B, (inv x) o η = x) (eissect : forall x : oA -> B, inv (x o η) = x) a
  : apD10 (ap inv π) (η a) = ((apD10 (eisretr (f o η)) a @ apD10 π a) @ (apD10 (eisretr (g o η)) a) ^)%path.
    apply universality_unit_lemma_lemma.
    exact eissect.
  Defined.
      
  Definition universality_unit (A:Trunk n) (B:subuniverse_Type) (f g:(O subU A).1.1 -> B.1.1)
             (η := O_unit subU A) (π : (f o η = g o η))
  : forall a, apD10 (equal_fun_modal A B f g π) (η a) = apD10 π a.
    intro a. unfold equal_fun_modal. destruct (O_equiv subU A B). simpl.
    repeat rewrite apD10_pp. rewrite apD10_V. rewrite concat_pp_p.
    apply moveR_Mp. apply moveR_pM. rewrite inv_V.
    assert (apD10 (eisretr (g o η)) a = apD10 (eissect g) (η a)).
    fold η in eisadj; rewrite (eisadj g).
    apply (apD10_ap_precompose η (eissect g)).
    rewrite <- X; clear X.
    assert (apD10 (eisretr (f o η)) a =
            apD10 (eissect f) (η a)).
    fold η in eisadj; rewrite (eisadj f).
    apply (apD10_ap_precompose η (eissect f)).
    rewrite <- X. clear X.
    apply (universality_unit_lemma η f g equiv_inv π eisretr eissect a).
  Defined.

(* Things *)

  Lemma O_rec_O_rec_dep_retr
        (A: Trunk n)
        (B: A.1 -> Trunk n)
        f g
        (H : forall a, f a (g a) = a)
  : O_rec A (O subU A) (λ x:A.1, O_rec (B x) (O subU A) (λ y, O_unit subU A (f x y)) (O_unit subU (B x) (g x))) = idmap.
    simpl.
    assert (X:forall x0 : A .1, (function_lift (B x0) A (f x0) (O_unit subU (B x0) (g x0)))  = (O_unit subU A x0)).
    intro a.
    etransitivity. exact (ap10 (O_rec_retr (B a) (O subU A) (λ x : (B a) .1, O_unit subU A (f a x))) (g a)).
    apply ap; apply H.
    transitivity (
        O_rec A (O subU A)
              (λ x0 : A .1,
                      (function_lift (B x0) A (f x0))
                        (O_unit subU (B x0) (g x0)))
      ).

    transitivity (O_rec A (O subU A)  (λ x0 : A .1, O_unit subU A x0)).
    apply ap. apply path_forall; intro a; exact (X a).
    rewrite (path_forall _ _ X).
    reflexivity.
    rewrite (path_forall _ _ X).
    apply (O_rec_sect A (O subU A) idmap).
  Qed.

  Lemma O_rec_O_rec_dep_sect
        (A: Trunk n)
        (B: A.1 -> Trunk n)
        f g
        (H : forall a, f a (g a) = a)
  : O_rec A (O subU A) (λ x:A.1, O_rec (B x) (O subU A) (λ y, O_unit subU A (f x (O_unit subU (B x) y))) (g x)) = idmap.
    simpl.
    transitivity (O_rec A (O subU A) (λ x : A .1, O_unit subU A x)).
    apply ap. apply path_forall; intro a.
    etransitivity; try exact (ap10 (O_rec_sect (B a) (O subU A) (λ u, O_unit subU A (f a u))) (g a)).
    apply ap. apply H.
    exact (O_rec_sect A (O subU A) idmap).
  Qed.

  
  Lemma O_rec_O_rec (A B C : Trunk n) f g x (H : forall b c, (f (g b c) c) = b)
  : O_rec A
          (O subU B)
          (λ u:A.1, O_rec C
                          (O subU B)
                          (λ v:C.1, O_unit subU B (f u v))
                          x)
          o (O_rec B
                 (O subU A)
                 (λ u:B.1, O_rec C
                                 (O subU A)
                                 (λ v:C.1, O_unit subU A (g u v))
                                 x)
                 ) = idmap.

    apply (equal_fun_modal B (O subU B)).
    apply path_forall; intro b.

    pose (eq := ap10 (O_rec_retr B (O subU A) (λ u : B .1, O_rec C (O subU A) (λ v : C .1, O_unit subU A (g u v)) x)) b); simpl in eq.
    rewrite eq; clear eq.

    pose (eq := ap10 (reflect_factoriality_post C A (O subU B) (λ u : A .1, O_rec C (O subU B) (λ v : C .1, O_unit subU B (f u v)) x) (g b)) x); unfold function_lift in eq; simpl in eq.
    rewrite eq; clear eq.

    assert ((λ x, 
            O_rec C (O subU B)
                  (λ x0 : C .1,
                          O_rec C (O subU B) (λ v : C .1, O_unit subU B (f (g b x0) v)) x) x) = (λ _, O_unit subU B b)).

    apply (@equiv_inj _ _ _ (O_equiv subU C (O subU B))).
    apply path_forall; intro c.
    pose (foo := ap10 (O_rec_retr C (O subU B) (λ x1 : C .1,
       O_rec C (O subU B) (λ v : C .1, O_unit subU B (f (g b x1) v))
         (O_unit subU C c))) c).
    rewrite foo; clear foo.
    pose (foo := ap10 (O_rec_retr C (O subU B) (λ v : C .1, O_unit subU B (f (g b c) v))) c).
    rewrite foo; clear foo.
    apply ap. exact (H b c).
    
    exact (ap10 X x).
  Qed.

  Lemma equiv_nj_inverse A a b
  : (O subU (a=b ; istrunc_paths (H:=A.2) A.1 n a b)).1.1 = (O subU (b=a ; istrunc_paths (H:=A.2) A.1 n b a)).1.1.
    repeat apply (ap pr1). apply ap.
    apply truncn_unique.
    exact (equal_inverse a b).
  Defined.

(* Dependent product and arrows *)
  Definition subuniverse_forall (A:Type) (B:A -> Trunk n) : (* Theorem 7.7.2 *)
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

    pose (μ := λ (X : ((O subU (A.1.1 * B.1.1; trunc_prod (H:=A.1.2) (H0 := B.1.2))) .1) .1),
               (O_rec (A.1.1 * B.1.1; trunc_prod (H:=A.1.2) (H0 := B.1.2)) (A)
                      (λ x : (A.1.1 * B.1.1; trunc_prod (H:=A.1.2) (H0 := B.1.2)) .1, (fst x)) X,
                O_rec (A.1.1 * B.1.1; trunc_prod (H:=A.1.2) (H0 := B.1.2)) (B)
                      (λ x : (A.1.1 * B.1.1; trunc_prod (H:=A.1.2) (H0 := B.1.2)) .1, (snd x)) X)).
    apply O_unit_retract_equiv with (μ := μ).
    intro x; destruct x as [a b].
    unfold μ; apply path_prod.
    - simpl.
     exact (apD10 (O_rec_retr (A.1.1 * B.1.1; trunc_prod (H:=A.1.2) (H0 := B.1.2)) A (λ x : (A .1) .1 * (B .1) .1, fst x)) (a,b)). 
    - simpl.
      exact (apD10 (O_rec_retr (A.1.1 * B.1.1; trunc_prod (H:=A.1.2) (H0 := B.1.2)) B (λ x : (A .1) .1 * (B .1) .1, snd x)) (a,b)). 
  Defined.
  
  Definition subuniverse_product_fun (A B : Trunk n) : (O subU (A.1*B.1; trunc_prod (H:=A.2) (H0:=B.2))).1.1 -> (O subU A).1.1*(O subU B).1.1
    := function_lift_modal
         (A.1*B.1; trunc_prod (H:=A.2) (H0:=B.2))
         (((O subU A).1.1*(O subU B).1.1 ; trunc_prod (H := (O subU A).1.2) (H0 := (O subU B).1.2)) ; subuniverse_product (O subU A) (O subU B))
         (λ x, (O_unit subU A (fst x), O_unit subU B (snd x))).

  Definition subuniverse_product_inv (A B : Trunk n) : (O subU A).1.1*(O subU B).1.1 -> (O subU (A.1*B.1 ; trunc_prod (H:=A.2) (H0:=B.2))).1.1.
    intro x. destruct x as [p p0].
    generalize dependent p; apply O_rec; intro p.
    generalize dependent p0; apply O_rec; intro p0.
    apply (O_unit subU).
    exact (p,p0).
  Defined.

  Definition product_universal (A B : Trunk n) (C : subuniverse_Type) :
    Equiv (A.1 * B.1 -> C.1.1) ((O subU A).1.1*(O subU B).1.1 -> C.1.1).
    apply (@equiv_compose' _ (A.1 -> B.1 -> C.1.1) _).
    Focus 2.
    exists (λ f, λ u v, f (u,v)).
    refine (@isequiv_adjointify _ _ _ (λ u, λ x, u (fst x) (snd x)) _ _).
    intro x. apply path_forall; intro u; apply path_forall; intro v. reflexivity.
    intro x. apply path_forall; intro u. apply (transport (λ U, x U = x u) (eta_prod u)). reflexivity.

    apply (@equiv_compose' _ ((O subU A).1.1 -> B.1 -> C.1.1) _).
    Focus 2. apply equiv_inverse.
    exists (λ f : (((O subU A) .1) .1 -> (existT (λ S, (subuniverse_HProp subU S).1) (existT (λ T, IsTrunc n T) (B .1 -> (C .1) .1) (trunc_arrow (H0 := C.1.2))) (subuniverse_arrow B .1 C)).1.1), 
                  f o O_unit subU A).
    exact (O_equiv subU A (( B.1 -> C.1.1 ; trunc_arrow (H0 := C.1.2)) ; subuniverse_arrow B.1 C)).
    
    apply (@equiv_compose' _ ((O subU A).1.1 -> (O subU B).1.1 -> C.1.1) _).
    exists (λ f:(((O subU A).1).1 → ((O subU B).1).1 → (C.1).1), λ u, f (fst u) (snd u)).
    apply isequiv_adjointify with (g := λ f, λ u v, f (u,v)).
    intro x. apply path_forall; intro u. rewrite (eta_prod u). reflexivity.
    intro x. apply path_forall; intro u. apply path_forall; intro v. reflexivity.

    apply equiv_postcompose'.
    apply equiv_inverse.
    exists (λ f : ((O subU B) .1) .1 -> (C .1) .1, f o O_unit subU B).
    exact (O_equiv subU B C).
  Defined.

  Definition product_universal' (A B : Trunk n) (C : subuniverse_Type) :
    (A.1 * B.1 -> C.1.1) = ((O subU A).1.1*(O subU B).1.1 -> C.1.1).
    apply path_universe_uncurried; exact (product_universal A B C).
  Defined.

  Definition subuniverse_product' (A B : Trunk n) (TrP : IsTrunc n (A.1*B.1)) : (O subU (A.1*B.1 ; TrP)).1.1 = ((O subU A).1.1*(O subU B).1.1).
    apply path_universe_uncurried.
    refine (equiv_adjointify _ _ _ _).
    - intros x.
      econstructor.
      revert x; apply O_rec; intro x; apply O_unit; exact (fst x).
      revert x; apply O_rec; intro x; apply O_unit; exact (snd x).
    - intros [x y].
      revert x; apply O_rec; intro x.
      revert y; apply O_rec; intro y.
      apply O_unit; exact (x,y).
    - intros [oa ob]. simpl.
      pose (s0 := ((((O subU A).1).1 ∧ ((O subU B).1).1); trunc_prod (H :=(O subU A).1.2) (H0 := (O subU B).1.2) )).
      pose (s := (s0 ; subuniverse_product (O subU A) (O subU B)) : subuniverse_Type).

      pose (p := λ (A:Trunk n) (f g : (O subU A).1.1 -> s.1.1) pp, ap10 (@equal_fun_modal A s f g pp)).
      revert oa; refine (p _ _ _ _); apply path_forall; intro a.
      revert ob; refine (p _ _ _ _); apply path_forall; intro b.


      assert (rew := λ P Q f, ap10 (O_rec_retr P Q f)).

      repeat rewrite rew. reflexivity.
    - simpl.
      pose (p := λ (X:Trunk n) (f g : (O subU X).1.1 -> (O subU (existT (IsTrunc n) (A.1 ∧ B.1) TrP)).1.1) pp, ap10 (@equal_fun_modal X (O subU (A.1 ∧ B.1; TrP)) f g pp)).
      refine (p _ _ _ _). apply path_forall.
      intros [a b]. simpl.
      assert (rew := λ P Q f, ap10 (O_rec_retr P Q f)).

      repeat rewrite rew. reflexivity.
  Defined.
  
  Lemma subuniverse_product_unit (A B : Trunk n) (TrP : IsTrunc n (A.1*B.1))
  : forall x, ((equiv_path _ _ (subuniverse_product' A B TrP)) o (O_unit subU (A.1*B.1 ; TrP))) x =  (O_unit subU A (fst x), O_unit subU B (snd x)).
    intro x.
    simpl. unfold subuniverse_product'. unfold equiv_adjointify.
    rewrite transport_path_universe_uncurried.
    (* unfold compose; simpl. *)
    refine (path_prod _ _ _ _).
    - simpl.
      (* rewrite O_rec_retr. *)
      refine (@apD10 _ _ ( O_rec (A.1 ∧ B.1; TrP) (O subU A)
                                 (λ x0 : A.1 ∧ B.1, O_unit subU A (fst x0)) o (O_unit subU (A.1 ∧ B.1; TrP))) ((O_unit subU A) o fst) _ x).
      simpl.
      apply (O_rec_retr (A.1 ∧ B.1; TrP) (O subU A) (λ x0 : A.1 ∧ B.1, O_unit subU A (fst x0))).
    - simpl.
      refine (@apD10 _ _ ( O_rec (A.1 ∧ B.1; TrP) (O subU B)
                                 (λ x0 : A.1 ∧ B.1, O_unit subU B (snd x0)) o (O_unit subU (A.1 ∧ B.1; TrP))) ((O_unit subU B) o snd) _ x).
      apply O_rec_retr.
  Defined.
  
  (* Theorem 7.7.4 *)
  Definition subuniverse_sigma :
    (forall (A:subuniverse_Type) (B:A.1.1 -> subuniverse_Type), (subuniverse_HProp subU ({x:A.1.1 & (B x).1.1} ; trunc_sigma (H:=A.1.2) (H0 := λ x, (B x).1.2))).1) <->
    (forall (A:Trunk n) (B: (O subU A).1.1 -> subuniverse_Type) (g : forall (a:A.1), (B (O_unit subU A a)).1.1), {f : forall (z:(O subU A).1.1), (B z).1.1 & forall a:A.1, f (O_unit subU A a) = g a}).
    split.
    - intro H. intros A B g.
      pose (Z := existT (λ T, (subuniverse_HProp subU T).1) ({z:(O subU A).1.1 & (B z).1.1} ; trunc_sigma (H:=(O subU A).1.2) (H0:=λ z, (B z).1.2)) (H ((O subU A)) B)).
      pose (g' :=( λ a:A.1, (O_unit subU A a ; g a)) : A.1 -> Z.1.1).
      pose (f' := O_rec  _ Z g'). unfold O_rec in f'.
      pose (eqf :=λ a:A.1, (apD10 (O_rec_retr _ Z g') a)). fold f' in eqf.
      pose (g'' := λ x, (f' x).1).
      pose (f'' := λ x:(O subU A).1.1, x).
      pose (eq'' := path_forall _ _ (λ x, @ap _ _ pr1 _ _ (eqf x))).
      (* assert (g'' o (O_unit sf A) = f'' o (O_unit sf A)). *)
        (* exact eq''. *)
      pose (eq''' := apD10 (equal_fun_modal A (O subU A) (f'') (g'') eq''^)). unfold f'', g'' in eq'''; simpl in eq'''.
      pose (f := λ z, (f' z).2). simpl in f.
      set (η := O_unit subU A) in *.

      exists (λ z, transport (λ u, (B u).1.1) (eq''' z)^ (f z)).
      intro a.

      unfold f. unfold g' in eqf; simpl in eqf.
      pose (p := pr1_path (eqf a)^). simpl in p.
      pose (q := pr2_path (eqf a)^). simpl in q.

      rewrite <- q. 
      assert ( (eq''' (η a)) =  (eqf a)^ ..1).
        unfold eq''', pr1_path, eqf, q, p, f, eq''', eq'', f'', g'', eqf, f', g', Z, η in *; simpl in *.
        rewrite universality_unit. unfold path_forall.
        repeat rewrite apD10_V.
        rewrite (eisretr apD10).
        rewrite ap_V.
        reflexivity.
      rewrite X.
      rewrite transport_Vp. reflexivity.
    - intros H A B.
      pose (h := λ x, O_rec  ({x:A.1.1 & (B x).1.1};trunc_sigma (H := A.1.2) (H0 := λ u, (B u).1.2)) A pr1 x).
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
      rewrite (q (x1;x2)).
      apply @path_sigma'  with (p := (p (x1;x2))).
      unfold g; simpl.
      rewrite transport_pV.
      reflexivity.
  Defined.
      
  Lemma subuniverse_unit : (subU.(subuniverse_HProp) (existT (λ T, IsTrunc n T) (Unit) (trunc_unit n))).1.
    rewrite <- subuniverse_iff_O.
    apply O_unit_retract_equiv with (μ := λ x:(subU.(O) (Unit;trunc_unit n)).1.1, tt).
    intro u.
    destruct u; reflexivity.
  Defined.

  Definition OUnit_is_Unit : (((O subU (Unit; trunc_unit n)).1).1 = Unit)
    := ((O_modal ((((Unit; trunc_unit n) : Trunk n); subuniverse_unit) : subuniverse_Type))..1..1)^.

  (** Paths *)
  Definition subuniverse_paths (A : subuniverse_Type)
  : forall x y:A.1.1, (subuniverse_HProp subU (x = y ; istrunc_paths _ n (H:= (trunc_succ (H := A.1.2))) _ _)).1.
    intros x y.
    rewrite <- subuniverse_iff_O.
    refine (O_unit_retract_equiv _ _).
    - intros u.
      assert (p : (fun _:(O subU (x = y; istrunc_paths (A.1).1 n (H:= (trunc_succ (H := A.1.2))) x y)).1.1 => x) = (fun _=> y)).
      { apply (equiv_inv (IsEquiv := isequiv_ap
                                         (H:= O_equiv subU (x = y; istrunc_paths (A.1).1 n (H:= (trunc_succ (H := A.1.2))) x y) A)
                                         (fun _ : (O subU (x = y; istrunc_paths (A.1).1 n (H:= (trunc_succ (H := A.1.2))) x y)).1.1  => x)
                                         (fun _ : (O subU (x = y; istrunc_paths (A.1).1 n (H:= (trunc_succ (H := A.1.2))) x y)).1.1  => y))).
        apply path_forall; intro v. exact v. }
      exact (ap10 p u).
    - intro u.
      etransitivity;
      [exact ((@ap10_ap_precompose _ _ _
                (O_unit subU (x = y; istrunc_paths (A.1).1 n (H:= (trunc_succ (H := A.1.2))) x y))
                (fun _ : (O subU (x = y; istrunc_paths (A.1).1 n (H:= (trunc_succ (H := A.1.2))) x y)).1.1  => x)
                (fun _ : (O subU (x = y; istrunc_paths (A.1).1 n (H:= (trunc_succ (H := A.1.2))) x y)).1.1  => y)
                
                (equiv_inv (IsEquiv := isequiv_ap (H:= O_equiv subU (x = y; istrunc_paths (A.1).1 n (H:= (trunc_succ (H := A.1.2))) x y) A)
                                                  (fun _ : (O subU (x = y; istrunc_paths (A.1).1 n (H:= (trunc_succ (H := A.1.2))) x y)).1.1  => x)
                                                  (fun _ : (O subU (x = y; istrunc_paths (A.1).1 n (H:= (trunc_succ (H := A.1.2))) x y)).1.1  => y))
                           (path_forall
                              ((fun _ : (O subU (x = y; istrunc_paths (A.1).1 n (H:= (trunc_succ (H := A.1.2))) x y)).1.1  => x) o (O_unit subU (x = y; istrunc_paths (A.1).1 n (H:= (trunc_succ (H := A.1.2))) x y)))
                              ((fun _ : (O subU (x = y; istrunc_paths (A.1).1 n (H:= (trunc_succ (H := A.1.2))) x y)).1.1  => y) o (O_unit subU (x = y; istrunc_paths (A.1).1 n (H:= (trunc_succ (H := A.1.2))) x y)))
                              idmap))
                u)^) | unfold path_forall, ap10; repeat rewrite eisretr; reflexivity].
  Qed.

  (** Things' *)
  
  
  Lemma reflect_factoriality_arrow_space
        (P:Trunk n)
        (Q R: subuniverse_Type)
        (f : P.1 -> (Q.1.1 -> R.1.1))
        (g : P.1 -> (R.1.1 -> Q.1.1))
        (S := ((Q.1.1 -> R.1.1; trunc_arrow (H0 := R.1.2)); subuniverse_arrow Q.1.1 R) : subuniverse_Type )
        (T := ((R.1.1 -> Q.1.1; trunc_arrow (H0 := Q.1.2)); subuniverse_arrow R.1.1 Q) : subuniverse_Type )
        (RR := ((R.1.1 -> R.1.1; trunc_arrow (H0 := R.1.2)); subuniverse_arrow R.1.1 R) : subuniverse_Type )
  : (λ v, (O_rec P S f v) o (O_rec P T g v)) = (λ v, O_rec P RR (λ v, (f v) o (g v)) v).
    simpl in *.
    pose (foo := @equiv_inj _ _ _ (O_equiv subU P RR)).
    specialize (foo (λ w, O_rec P S f w o O_rec P T g w) (λ w, O_rec P RR (λ v : P .1, f v o g v) w)). simpl in foo.
    apply foo; clear foo.
    apply path_forall; intro v. 
    transitivity ((λ v : P .1, f v o g v) v).
    - apply path_forall; intro r; simpl.
      pose (foo := ap10 (O_rec_retr P S f) v). 
      rewrite foo. 
      apply ap.
      pose (bar := ap10 (O_rec_retr P T g) v). 
      rewrite bar.
      reflexivity.
    - apply path_forall; intro r; simpl.
      pose (foo := ap10 (O_rec_retr P RR (λ (v0 : P .1) (x : (R .1) .1), f v0 (g v0 x))) v). 
      rewrite foo.
      reflexivity.
  Defined.

  
  Lemma transport_arrow_space
        (P Q : subuniverse_Type)
        (p : P.1.1 = Q.1.1)
  : (λ x0:Q.1.1, (transport idmap p (transport idmap p^ x0))) = idmap.
    destruct p; reflexivity.
  Qed.

  Lemma transport_arrow_space_dep_path
        (P Q : subuniverse_Type)
        (R : Trunk n)
        (p : R.1 -> P.1.1 = Q.1.1)
  : (λ v:R.1, λ x0:Q.1.1, (transport idmap (p v) (transport idmap (p v)^ x0))) = λ v, idmap.
    apply path_forall; intro v.
    apply transport_arrow_space.
  Qed.

  Lemma ap10_O_retr_sect (P:Trunk n) (Q:subuniverse_Type) f x0
  : (ap10
       (O_rec_sect P Q
                   f) (O_unit subU P x0)) =
    (ap10
       (O_rec_retr P Q
                   (λ x1 : P.1, f (O_unit subU P x1))) x0).

    unfold O_rec_retr, O_rec_sect. simpl.
    pose (foo := O_equiv subU P Q).
    pose (adj := eisadj _ (IsEquiv := foo)).
    specialize (adj f). simpl in adj. 

    transitivity (ap10 (ap
                      (λ (f : ((O subU P) .1) .1 → (Q .1) .1) (x : P .1), f (O_unit subU P x))
                      (eissect
                         (λ (f : ((O subU P) .1) .1 → (Q .1) .1) 
                            (x : P .1), f (O_unit subU P x)) f)) x0).

    pose (rew := @ap10_ap_precompose).  rewrite rew. reflexivity.
    apply (ap (λ u, ap10 u x0) (x:=(ap
                                      (λ (f0 : ((O subU P) .1) .1 → (Q .1) .1) (x : P .1), f0 (O_unit subU P x))
                                      (eissect
                                         (λ (f0 : ((O subU P) .1) .1 → (Q .1) .1) (x : P .1),
                                          f0 (O_unit subU P x)) f))) (y:=(eisretr
                                                                          (λ (f0 : ((O subU P) .1) .1 → (Q .1) .1) (x : P .1), f0 (O_unit subU P x))
                                                                          (λ x1 : P .1, f (O_unit subU P x1))))).
    exact adj^.
  Defined.

  Definition O_invol_ : forall T, O subU T = (O subU) ( pr1 ((O subU) T))
    := λ T, (O_modal (O subU T)).

  Lemma OO_unit_idmap (T:Trunk n)
  : O_unit subU (O subU T).1 = equiv_path _ _ ((O_invol_ T)..1..1).
    unfold O_invol_. unfold O_modal.
    pose (rew := eissect _ (IsEquiv := isequiv_unique_subuniverse (O subU T) (O subU (O subU T) .1)) (truncn_unique (O subU T) .1 (O subU (O subU T) .1) .1
                                                                                                              (path_universe_uncurried
                                                                                                                 {|
                                                                                                                   equiv_fun := O_unit subU (O subU T) .1;
                                                                                                                   equiv_isequiv := O_modal_equiv (O subU T) |}))). 
    simpl in rew; rewrite rew; clear rew.

    pose (rew := eissect _ (IsEquiv := isequiv_truncn_unique (O subU T).1 (O subU (O subU T) .1).1) (path_universe_uncurried
                                                                                                 {|
                                                                                                   equiv_fun := O_unit subU (O subU T) .1;
                                                                                                   equiv_isequiv := O_modal_equiv (O subU T) |})). 
    simpl in rew. unfold pr1_path. rewrite rew; clear rew.
    unfold path_universe_uncurried. rewrite eisretr. simpl. reflexivity.
  Defined.

End Reflective_Subuniverse. 