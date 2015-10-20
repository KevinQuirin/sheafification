(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Export MyTacs.
Require Import HoTT.
Require Export Utf8_core.

Set Universe Polymorphism.
Global Set Primitive Projections.

Section Reflective_subuniverse_Definition.

Local Open Scope path_scope.

Context `{ua: Univalence}.
Context `{fs: Funext}.

(* Definition 10, (i) to (iv) *)
Record subuniverse_struct n
  := Build_subuniverse_struct { 
         
         subuniverse_HProp : TruncType n -> hProp  ;
         
         OO : TruncType n -> {T : TruncType n | subuniverse_HProp T} ;

         OO_unit : forall T:TruncType n, T -> (OO T).1;
         
         OO_equiv : forall (P : TruncType n) (Q : {T:TruncType n & subuniverse_HProp T}),
             IsEquiv (fun f : (OO P).1 -> Q.1 => f o (OO_unit P)) 
       }.

End Reflective_subuniverse_Definition.

Section Reflective_Subuniverse.

  Variable n:trunc_index.

  Variable subU : subuniverse_struct n.

  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  Definition IsSubu T := trunctype_type (subuniverse_HProp n subU T).
  Global Instance ishprop_issubu T
    : IsHProp (IsSubu T).
  Proof.
    apply istrunc_trunctype_type.
  Qed.
 
  Existing Class IsSubu.
 
  Class subuniverse_Type  :=
    Build_subuniverse_Type
      { st : TruncType n ;
        subu_struct: IsSubu st
      }.
  Arguments st T : clear implicits, rename.

  Global Coercion st : subuniverse_Type >-> TruncType.

  Definition O : TruncType n -> subuniverse_Type 
    := λ T, Build_subuniverse_Type (OO n subU T).1 (OO n subU T).2.

  Definition O_unit : forall T:TruncType n, T -> O T
    := λ T x, OO_unit n subU T x.

  Definition O_equiv : forall (P : TruncType n) (Q : subuniverse_Type),
      IsEquiv (fun f : (O P) -> Q => f o (O_unit P))
    := λ P Q, OO_equiv n subU P (st Q; @subu_struct Q).

  Global Opaque O. Global Opaque O_unit. Global Opaque O_equiv.
  
  (* Global Arguments subuniverse_HProp {n} subU T : rename. *)
  (* Global Arguments O {n} subU T : rename. *)
  (* Global Arguments O_unit {n} subU T x : rename. *)
  (* Global Arguments O_equiv {n} subU P Q : rename. *)
  
  Definition subuniverse_Type_sigma_equiv
    : {T : TruncType n & IsSubu T} <~>  subuniverse_Type.
  Proof.
    (* Why does [issig] tactic doesn't work ? *)
    refine (equiv_adjointify _ _ _ _).
    intros [T s]. exists T. exact s.
    intros T. exists (st T). exact subu_struct.
    intro; reflexivity.
    intro; reflexivity.
  Defined.
  
  Instance subuniverse_Type_is_TruncTypeSn : IsTrunc (trunc_S n) subuniverse_Type.
  Proof.
    refine (trunc_equiv' _ subuniverse_Type_sigma_equiv).
    refine trunc_sigma.
    intro T.
    refine (@trunc_leq -1 (n.+1) tt _ _).
  Defined.
  
  Definition O_rec (P : TruncType n) (Q : subuniverse_Type)
    : (P -> Q) -> (O P) -> Q
    := (@equiv_inv _ _ _ (O_equiv _ _)).

  Definition O_rec_retr (P : TruncType n) (Q : subuniverse_Type) f
  : O_rec _ _ f o (O_unit _) = f :=
    @eisretr _ _ _ (O_equiv P Q) f.

  Definition O_rec_sect (P : TruncType n) (Q : subuniverse_Type) f :=
    @eissect _ _ _ (O_equiv P Q) f.
  
  Definition O_rec_const (P:TruncType n) (Q:subuniverse_Type) y : O_rec P Q (λ _, y) = (λ _, y)
    := eissect _ (IsEquiv := O_equiv P Q) (λ x, y).

  Lemma transport_O_rec (P:TruncType n) (Q R:subuniverse_Type) (B:= λ S:subuniverse_Type, st S) (eq : Q = R) f r:
    transport B eq (O_rec P Q f r) = O_rec P R (λ v, transport B eq (f v)) r.
    destruct eq. simpl. reflexivity.
  Defined.
  
  Definition O_unit_retract_equiv (T:TruncType n) (μ : (O T) -> T) (η := O_unit T) : Sect η μ -> IsEquiv η.
  Proof.
    intros H. refine (isequiv_adjointify _ μ _ _).
    - assert (η o μ o η = idmap o η).
      apply (ap (fun x => η o x)).
      apply path_forall; intro y.
      exact (H y).
      exact (apD10 (@equiv_inj _ _ _ (O_equiv T (O T)) (η o μ) idmap X)).
    - exact H.
  Defined.
    
  Instance O_modal_equiv (P : subuniverse_Type) : IsEquiv (O_unit P).
  apply O_unit_retract_equiv with (μ := (O_rec P P idmap)).
  pose (f := O_rec_retr P P idmap). 
  intro. eapply apD10 in f. exact (f x).
  Defined.

  Definition unique_subuniverse : forall (T T' : subuniverse_Type), st T = st T' -> T = T'.
  Proof.
    intros T T' X. destruct T as [T sT], T' as [T' sT'].
    cbn in X. destruct X.
    assert (X: sT = sT') by apply path_ishprop. destruct X.
    reflexivity.
 (* cbn. *)
 (*                                                                                      destruct T, T'. eapply (eq_dep_subset' (λ x, let (a, _) := subuniverse_HProp subU x in a) _ _ _ X).  *)
 (*    Grab Existential Variables. intro. simpl. exact ((subuniverse_HProp subU a) .2). *)
  Defined.

  Definition isequiv_unique_subuniverse (T T':subuniverse_Type)
    : IsEquiv (unique_subuniverse T T').
  Proof.
    refine (isequiv_adjointify _ _ _ _).
    - intro p. apply (ap st p).
    - intro p; destruct p.
      unfold unique_subuniverse; simpl.
      destruct T as [[T TrT] ShT].
      match goal with
      |[|- match ?foo in (_ = y) return _ with | _ => _ end = _] => assert (r: idpath = foo) by apply path_ishprop
      end.
      destruct r. reflexivity.
    - intro p. unfold unique_subuniverse. 
      destruct T as [T ShT], T' as [T' ShT']; simpl in *. destruct p.
      assert (X: ShT = ShT') by apply path_ishprop.
      destruct X.
      match goal with
      |[|- ap _ match ?foo in (_ = y) return _ with | _ => _ end = _] => assert (r: idpath = foo) by apply path_ishprop
      end. destruct r; reflexivity.
  Defined.
  Opaque isequiv_unique_subuniverse.
  
      
  Definition O_modal (T:subuniverse_Type) : T = O T.
  Proof.
    apply unique_subuniverse; apply path_trunctype; cbn.
    exact (BuildEquiv _ _ (O_unit T) (O_modal_equiv _)).
  Defined.

  Definition O_invol : forall T, O (O T) = O T.
    intro T; symmetry; apply O_modal.
  Defined.

  Definition subuniverse_struct_transport (T U: TruncType n) (f : (T <~> U)) :
    (IsSubu T) -> (IsSubu U).
  Proof.
    intro x. destruct T, U. 
    apply path_universe_uncurried in f; cbn in f. destruct f.
    assert (r: istrunc_trunctype_type = istrunc_trunctype_type0) by apply path_ishprop.
    destruct r. exact x.
  Defined.
  
  Definition subuniverse_iff_O (T:TruncType n) : 
    IsEquiv (O_unit T) = IsSubu T.
  Proof.
    apply path_universe_uncurried. apply equiv_iff_hprop.
    - refine (fun X => subuniverse_struct_transport _ _ (BuildEquiv _ _ _ (isequiv_inverse _ (feq:=X))) _).
      apply subu_struct.
    - exact (fun X => O_modal_equiv (Build_subuniverse_Type T X)).
  Defined.

(* ○-lift of functions *)
  
  Definition function_lift (A B : TruncType n) (f : A -> B)
    : (O A) -> (O B).
    apply O_rec; intro x; apply O_unit; apply f; exact x.
  Defined.

  Definition function_lift_modal (A:TruncType n) (B:subuniverse_Type) (f : A -> B) : (O A) -> B.
    apply O_rec. exact f.
  Defined.

  Notation "'○' f" := (function_lift _ _ f) (at level 0).
  Notation "'○' f" := (function_lift_modal _ _ f) (at level 0).
  
  Lemma reflect_factoriality_pre
        (X:TruncType n)
        (Y Z:subuniverse_Type)
        (g : Y -> Z)
        (f : X -> Y)
  : g o (O_rec X Y f) = O_rec X Z (g o f).
  Proof.
    apply (@equiv_inj _ _ _ (O_equiv X Z) (g o (O_rec X Y f)) (O_rec X Z (g o f))).
    transitivity (g o f).
    - apply (ap (λ f, g o f)).
      exact (O_rec_retr X Y f).
    - exact (O_rec_retr X Z (g o f))^.
  Defined.

  Lemma reflect_factoriality_post
        (X Y:TruncType n)
        (Z:subuniverse_Type)
        (g:Y -> Z)
        (f:X -> Y)
  : (O_rec Y Z g) o (function_lift X Y f) = O_rec X Z (g o f).
  Proof.
    transitivity (O_rec X Z ((O_rec Y Z g) o (O_unit Y o f))).
    - apply reflect_factoriality_pre.
    - apply ap.
      transitivity (((O_rec Y Z g) o O_unit Y) o f).
      reflexivity.
      exact (ap (λ u, u o f) (O_rec_retr Y Z g)).
  Defined.

  Lemma reflect_functoriality
        (X Y Z:TruncType n)
        (g:Y -> Z)
        (f:X -> Y)
  : (function_lift Y Z g) o (function_lift X Y f) = function_lift X Z (g o f).
    apply reflect_factoriality_post.
  Defined.

  Lemma O_rec_O_unit (A : subuniverse_Type) (B : TruncType n) (f : B -> A) (x : (O B)) :
    O_unit A (O_rec B A f x) = O_rec B (O A) ((O_unit A) o f) x.
  Proof.
    assert (X: O_rec B (O A) (O_unit A o f) x = O_rec B (O A) ((O_unit A) o (O_rec B A f) o (O_unit B)) x).
    { pose (foo := O_rec_retr B A f).
      apply (ap (fun u => O_rec B (O A) u x)).
      apply (ap (fun u => O_unit A o u)).
      exact foo^. }
    rewrite X; clear X.
    assert (X: forall U, O_rec B (O A) (U o O_unit B) x = U x).
    { intro U.
      exact (apD10 (O_rec_sect B (O A) U) x). }
    exact (inverse (X (O_unit A o O_rec B A f))).
  Defined.

  Definition function_lift_modal_square (A : TruncType n) (B : subuniverse_Type) (f : A -> B) : (@equiv_inv _ _ (O_unit B) (O_modal_equiv B)) o (function_lift A B f) o (O_unit A) =  f.
    apply path_forall; intro x; unfold function_lift; simpl.
    exact (transport (λ U, O_rec B B (λ x : B, x) U = f x) (inverse (apD10 ((O_rec_retr A (O B)) ((O_unit B) o f)) x)) (apD10 (O_rec_retr B B idmap) (f x))).
  Defined.

  Definition function_lift_compose (A B C : TruncType n) ( f : A -> B) (g : B -> C) :
    (function_lift A C (g o f)) = (function_lift B C g) o (function_lift A B f).
    apply path_forall; intro x; simpl.
    unfold function_lift.
    assert (X: O_rec A (O C) (((O_unit C o g) o f)) = O_rec A (O C) (((O_rec B (O C) (O_unit C o g) o O_unit B) o f))).
    { pose (foo := O_rec_retr B (O C) (O_unit C o g)).
      apply (transport (λ U, _ = O_rec _ _ (λ x0, U (f x0))) foo^). reflexivity. }
    rewrite X; clear X.

    assert (X: O_rec A (O C)
     (O_rec B (O C) (O_unit C o g) o (O_unit B o f)) =
            O_rec A (O C)
     (O_rec B (O C) (O_unit C o g) o (O_rec A (O B) (O_unit B o f) o O_unit A))).
    { pose (foo := O_rec_retr A (O B) (O_unit B o f)).
      apply (transport (λ U, _ = O_rec _ _ (λ x0, O_rec _ _ _ (U x0))) foo^). reflexivity. }
    etransitivity. exact (ap10 X x).

    pose (foo := apD10 (O_rec_sect A (O C) (O_rec B (O C) (O_unit C o g)
       o O_rec A (O B) (O_unit B o f))) x).

    unfold O_rec, equiv_inv in *; simpl in *.
    rewrite foo. reflexivity.
  Defined.

  Definition function_lift_square (A B C X : TruncType n) (π1 : X -> A) (π2 : X -> B) (f : A -> C) (g : B -> C) (comm : (f o π1) = (g o π2)) : ( (function_lift A C f) o (function_lift X A π1) ) = ( (function_lift B C g) o (function_lift X B π2) ).
    unfold function_lift in *; simpl in *.
    apply path_forall; intro x; simpl.

    pose (foo1 := apD10 (function_lift_compose X A C π1 f) x). unfold function_lift in foo1; simpl in foo1.
    pose (foo2 := apD10 (function_lift_compose X B C π2 g) x). unfold function_lift in foo2; simpl in foo2.
    pose (foo3 := ap (λ u, O_rec X (O C) (λ x0, O_unit C (u x0)) x) (x:=f o π1) (y:=g o π2) comm). simpl in foo3.

    exact ((inverse foo1) @ foo3 @ foo2).
  Defined.

  Definition function_lift_idmap A : function_lift A A idmap = idmap
    := O_rec_sect A (O A) idmap.

  Lemma function_lift_equiv A B f 
  : IsEquiv f -> IsEquiv (function_lift A B f).
    intro H.
    eapply (isequiv_adjointify (function_lift A B f) (function_lift B A (@equiv_inv A B f H))).
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

  Lemma function_lift_equiv' (A B:TruncType n) (H : A <~> B)
  : (O A) <~> (O B).
    exists (function_lift A B H).
    apply function_lift_equiv. exact (equiv_isequiv H).
  Defined.

  (* TODO *)
  (* Lemma function_lift_transport A B (p:A=B) *)
  (* : (ap (O) p) = (@path_universe _ (O A).1.1 (O B).1.1 (function_lift A B (transport idmap p..1)) (function_lift_equiv A B ((equiv_path A.1 B.1 p..1)) _)) . *)
  (*   destruct p. simpl. *)
  (*   unfold path_universe, path_universe_uncurried. *)
  (*   apply (@equiv_inj _ _ _ (isequiv_equiv_path _ _)). *)
  (*   rewrite eisretr. apply equal_equiv. simpl. *)
  (*   apply path_forall; intro a. simpl. *)
  (*   unfold function_lift. simpl. *)
  (*   exact ((ap10 (O_rec_sect A (O A) idmap) a)^). *)
  (* Qed. *)

(* The universal property commute with η *)

  Definition equal_fun_modal (A:TruncType n) (B:subuniverse_Type) (f g:(O A) -> B) (η := O_unit A) : ((f o η = g o η) -> (f=g))
    := λ H, ((inverse (eissect _ (IsEquiv := (O_equiv A B)) f) @ (ap equiv_inv H) @ (eissect _ (IsEquiv := (O_equiv A B)) g))).
  Arguments equal_fun_modal (A B) (f g) π : clear implicits.
    
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
      
  Definition universality_unit (A:TruncType n) (B:subuniverse_Type) (f g:(O A) -> B)
             (η := O_unit A) (π : (f o η = g o η))
  : forall a, apD10 (equal_fun_modal A B f g π) (η a) = apD10 π a.
    intro a. unfold equal_fun_modal. destruct (O_equiv A B). simpl.
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
    apply (universality_unit_lemma _ _ _ _ _ _ equiv_inv π eisretr eissect a).
  Defined.

(* Things *)

  Lemma O_rec_O_rec_dep_retr
        (A: TruncType n)
        (B: A -> TruncType n)
        f g
        (H : forall a, f a (g a) = a)
  : O_rec A (O A) (λ x:A, O_rec (B x) (O A) (λ y, O_unit A (f x y)) (O_unit (B x) (g x))) = idmap.
    simpl.
    assert (X:forall x0 : A, (function_lift (B x0) A (f x0) (O_unit (B x0) (g x0)))  = (O_unit A x0)).
    intro a.
    etransitivity. exact (ap10 (O_rec_retr (B a) (O A) (λ x : (B a), O_unit A (f a x))) (g a)).
    apply ap; apply H.
    transitivity (
        O_rec A (O A)
              (λ x0 : A,
                      (function_lift (B x0) A (f x0))
                        (O_unit (B x0) (g x0)))
      ).

    transitivity (O_rec A (O A)  (λ x0 : A, O_unit A x0)).
    apply ap. apply path_forall; intro a; exact (X a).
    rewrite (path_forall _ _ X).
    reflexivity.
    rewrite (path_forall _ _ X).
    apply (O_rec_sect A (O A) idmap).
  Qed.

  Lemma O_rec_O_rec_dep_sect
        (A: TruncType n)
        (B: A -> TruncType n)
        f g
        (H : forall a, f a (g a) = a)
  : O_rec A (O A) (λ x:A, O_rec (B x) (O A) (λ y, O_unit A (f x (O_unit (B x) y))) (g x)) = idmap.
    simpl.
    transitivity (O_rec A (O A) (λ x : A, O_unit A x)).
    apply ap. apply path_forall; intro a.
    etransitivity; try exact (ap10 (O_rec_sect (B a) (O A) (λ u, O_unit A (f a u))) (g a)).
    apply ap. apply H.
    exact (O_rec_sect A (O A) idmap).
  Qed.

  
  Lemma O_rec_O_rec (A B C : TruncType n) f g x (H : forall b c, (f (g b c) c) = b)
  : O_rec A
          (O B)
          (λ u:A, O_rec C
                          (O B)
                          (λ v:C, O_unit B (f u v))
                          x)
          o (O_rec B
                 (O A)
                 (λ u:B, O_rec C
                                 (O A)
                                 (λ v:C, O_unit A (g u v))
                                 x)
                 ) = idmap.

    apply (equal_fun_modal B (O B)).
    apply path_forall; intro b.

    pose (eq := ap10 (O_rec_retr B (O A) (λ u : B, O_rec C (O A) (λ v : C, O_unit A (g u v)) x)) b); simpl in eq.
    rewrite eq; clear eq.

    pose (eq := ap10 (reflect_factoriality_post C A (O B) (λ u : A, O_rec C (O B) (λ v : C, O_unit B (f u v)) x) (g b)) x); unfold function_lift in eq; simpl in eq.
    rewrite eq; clear eq.

    assert ((λ x, 
            O_rec C (O B)
                  (λ x0 : C,
                          O_rec C (O B) (λ v : C, O_unit B (f (g b x0) v)) x) x) = (λ _, O_unit B b)).

    apply (@equiv_inj _ _ _ (O_equiv C (O B))).
    apply path_forall; intro c.
    pose (foo := ap10 (O_rec_retr C (O B) (λ x1 : C,
       O_rec C (O B) (λ v : C, O_unit B (f (g b x1) v))
         (O_unit C c))) c).
    rewrite foo; clear foo.
    pose (foo := ap10 (O_rec_retr C (O B) (λ v : C, O_unit B (f (g b c) v))) c).
    rewrite foo; clear foo.
    apply ap. exact (H b c).
    
    exact (ap10 X x).
  Qed.

  Lemma equiv_nj_inverse (A:TruncType n) (a b:A)
    : (O (BuildTruncType n (a=b))) = (O (BuildTruncType n (b=a))).
  Proof.
    apply ap.
    apply path_trunctype; cbn.
    exact (equiv_adjointify inverse inverse (λ x, inv_V _) (λ x, inv_V _)).
  Defined.

  Global Instance subuniverse_forall (A:Type) (B:A -> TruncType n) (H: forall x, IsSubu (B x))
    : IsSubu (BuildTruncType n (forall x:A, (B x))). (* Theorem 7.7.2 *)
  Proof.
    pose (ev := λ x, (λ (f:(forall x, (B x))), f x)).
    pose (ζ := λ x:A, O_rec (BuildTruncType n (∀ x0 : A, (B x0))) (Build_subuniverse_Type (B x) (H x)) (ev x)).
    pose (h := λ z, λ x, ζ x z).
    simpl in *.
    rewrite <- (subuniverse_iff_O).
    set (η := (O_unit (BuildTruncType n (∀ x : A, (B x))))).
    apply O_unit_retract_equiv with (μ := h).
    intro φ.
    unfold h, ζ, ev; clear h; clear ζ; clear ev.
    apply path_forall; intro x.
    pose (foo := @O_rec_retr (BuildTruncType n (∀ x : A, (B x))) (Build_subuniverse_Type (B x) (H x)) (λ f : ∀ x0 : A, (B x0), f x)).
    exact (apD10 foo φ).
  Defined.
  
  Global Instance subuniverse_arrow (A : Type) (B : subuniverse_Type) :
    IsSubu (BuildTruncType n (A -> B)).
    apply subuniverse_forall.
    intro a. exact subu_struct.
  Defined.

(* Product, Proposition 11 *)
  Global Instance subuniverse_product (A B : subuniverse_Type) :
    IsSubu (BuildTruncType n (A*B)).
    rewrite <- subuniverse_iff_O.
    pose (μ := λ (X : ((O (BuildTruncType n (A*B))))),
               (O_rec (BuildTruncType n (A*B)) A
                      (λ x : A*B, (fst x)) X,
                O_rec (BuildTruncType n (A*B)) B
                      (λ x : A*B, (snd x)) X)).
    apply O_unit_retract_equiv with (μ := μ).
    intro x; destruct x as [a b].
    unfold μ; apply path_prod.
    - simpl.
     exact (apD10 (O_rec_retr (BuildTruncType n (A*B)) A (λ x : A*B, fst x)) (a,b)). 
    - simpl.
      exact (apD10 (O_rec_retr (BuildTruncType n (A*B)) B (λ x :A*B, snd x)) (a,b)). 
  Defined.
  
  Definition subuniverse_product_fun (A B : TruncType n) : (O (BuildTruncType n (A*B))) -> (O A)*(O B)
    := function_lift_modal
         (BuildTruncType n (A*B))
         (Build_subuniverse_Type (BuildTruncType n ((O A)*(O B))) _)
         (λ x, (O_unit A (fst x), O_unit B (snd x))).

  Definition subuniverse_product_inv (A B : TruncType n) : (O A)*(O B) -> (O (BuildTruncType n (A*B))).
    intro x. destruct x as [p p0].
    generalize dependent p; apply O_rec; intro p.
    generalize dependent p0; apply O_rec; intro p0.
    apply (O_unit).
    exact (p,p0).
  Defined.

  Definition product_universal (A B : TruncType n) (C : subuniverse_Type) :
    (A * B -> C) <~> ((O A)*(O B) -> C).
    apply (@equiv_compose' _ (A -> B -> C) _).
    Focus 2.
    exists (λ f, λ u v, f (u,v)).
    refine (@isequiv_adjointify _ _ _ (λ u, λ x, u (fst x) (snd x)) _ _).
    intro x. apply path_forall; intro u; apply path_forall; intro v. reflexivity.
    intro x. apply path_forall; intro u. apply (transport (λ U, x U = x u) (eta_prod u)). reflexivity.

    apply (@equiv_compose' _ ((O A) -> B -> C) _).
    Focus 2. apply equiv_inverse.

    exists (λ f a b, f (O_unit A a) b).
    exact (O_equiv A (Build_subuniverse_Type (BuildTruncType n (B -> C)) _)).
    
    apply (@equiv_compose' _ ((O A) -> (O B) -> C) _).
    exists (λ f, λ u, f (fst u) (snd u)).
    apply isequiv_adjointify with (g := λ f, λ u v, f (u,v)).
    intro x. apply path_forall; intro u. rewrite (eta_prod u). reflexivity.
    intro x. apply path_forall; intro u. apply path_forall; intro v. reflexivity.

    apply equiv_postcompose'.
    apply equiv_inverse.
    exists (λ f, f o O_unit B).
    exact (O_equiv B C).
  Defined.

  Definition product_universal' (A B : TruncType n) (C : subuniverse_Type) :
    (A*B -> C) = ((O A)*(O B) -> C).
    apply path_universe_uncurried; exact (product_universal A B C).
  Defined.
  
  (* Proposition 11 *)

  Definition subuniverse_product_equiv' (A B : TruncType n) (TrP : IsTrunc n (A*B)) : (O (@BuildTruncType n (A*B) TrP)) <~> ((O A)*(O B)).
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
      pose (s0 := BuildTruncType n ((O A) ∧ (O B)) ).
      pose (s := Build_subuniverse_Type s0 (subuniverse_product (O A) (O B))).

      pose (p := λ (A:TruncType n) (f g : O A -> s) pp, ap10 (@equal_fun_modal A s f g pp)).
      revert oa; refine (p _ _ _ _); apply path_forall; intro a.
      revert ob; refine (p _ _ _ _); apply path_forall; intro b.


      assert (rew := λ P Q f, ap10 (O_rec_retr P Q f)).

      repeat rewrite rew. reflexivity.
    - simpl.
      pose (p := λ (X:TruncType n) (f g : (O X) -> (O (@BuildTruncType n (A∧B) TrP))) pp, ap10 (@equal_fun_modal X (O (@BuildTruncType n (A ∧ B) TrP)) f g pp)).
      refine (p _ _ _ _). apply path_forall.
      intros [a b]. simpl.
      assert (rew := λ P Q f, ap10 (O_rec_retr P Q f)).

      repeat rewrite rew. reflexivity.
  Defined.
    
  Definition subuniverse_product' (A B : TruncType n) (TrP : IsTrunc n (A*B)) : trunctype_type (st (O (@BuildTruncType n (A*B) TrP))) = ((O A)*(O B)).
    apply path_universe_uncurried. apply subuniverse_product_equiv'.
  Defined.
  
  (* Lemma subuniverse_product_unit (A B : TruncType n) (TrP : IsTrunc n (A.1*B.1)) *)
  (* : forall x, ((equiv_path _ _ (subuniverse_product' A B TrP)) o (O_unit (A.1*B.1 ; TrP))) x =  (O_unit A (fst x), O_unit B (snd x)). *)
  (*   intro x. *)
  (*   simpl. unfold subuniverse_product'. unfold equiv_adjointify. *)
  (*   rewrite transport_path_universe_uncurried. *)
  (*   (* unfold compose; simpl. *) *)
  (*   refine (path_prod _ _ _ _). *)
  (*   - simpl. *)
  (*     (* rewrite O_rec_retr. *) *)
  (*     refine (@apD10 _ _ ( O_rec (A.1 ∧ B.1; TrP) (O A) *)
  (*                                (λ x0 : A.1 ∧ B.1, O_unit A (fst x0)) o (O_unit (A.1 ∧ B.1; TrP))) ((O_unit A) o fst) _ x). *)
  (*     simpl. *)
  (*     apply (O_rec_retr (A.1 ∧ B.1; TrP) (O A) (λ x0 : A.1 ∧ B.1, O_unit A (fst x0))). *)
  (*   - simpl. *)
  (*     refine (@apD10 _ _ ( O_rec (A.1 ∧ B.1; TrP) (O B) *)
  (*                                (λ x0 : A.1 ∧ B.1, O_unit B (snd x0)) o (O_unit (A.1 ∧ B.1; TrP))) ((O_unit B) o snd) _ x). *)
  (*     apply O_rec_retr. *)
  (* Defined. *)
  
  (* Proposition 11 *)
  Definition subuniverse_sigma :
    (forall (A:subuniverse_Type) (B:A -> subuniverse_Type), (IsSubu (BuildTruncType n {x:A & B x}))) <->
    (forall (A:TruncType n) (B: (O A) -> subuniverse_Type) (g : forall (a:A), (B (O_unit A a))), {f : forall (z:(O A)), (B z) & forall a:A, f (O_unit A a) = g a}).
    split.
    - intro H. intros A B g.
      pose (Z := Build_subuniverse_Type (BuildTruncType n {z:(O A) & B z}) (H ((O A)) B)).
      (* pose (Z := existT (λ T, (subuniverse_HProp subU T).1) ({z:(O A).1.1 & (B z).1.1} ; trunc_sigma (H:=(O A).1.2) (H0:=λ z, (B z).1.2)) (H ((O A)) B)). *)
      pose (g' := (λ a:A, (O_unit A a ; g a)) : A -> Z).
      pose (f' := O_rec  _ Z g'). unfold O_rec in f'.
      pose (eqf :=λ a:A, (apD10 (O_rec_retr _ Z g') a)). fold f' in eqf.
      pose (g'' := λ x, (f' x).1).
      pose (f'' := λ x:(O A), x).
      pose (eq'' := path_forall _ _ (λ x, @ap _ _ pr1 _ _ (eqf x))).
      (* assert (g'' o (O_unit sf A) = f'' o (O_unit sf A)). *)
        (* exact eq''. *)
      pose (eq''' := apD10 (equal_fun_modal A (O A) (f'') (g'') eq''^)). unfold f'', g'' in eq'''; simpl in eq'''.
      pose (f := λ z, (f' z).2). simpl in f.
      set (η := O_unit A) in *.

      exists (λ z, transport (λ u, (B u)) (eq''' z)^ (f z)).
      intro a.

      unfold f. unfold g' in eqf; simpl in eqf.
      pose (p := pr1_path (eqf a)^). simpl in p.
      pose (q := pr2_path (eqf a)^). simpl in q.

      rewrite <- q. 
      assert (X: (eq''' (η a)) =  (eqf a)^ ..1).
        unfold eq''', pr1_path, eqf, q, p, f, eq''', eq'', f'', g'', eqf, f', g', Z, η in *; simpl in *.
        rewrite (universality_unit A (O A) idmap _ _ a). unfold path_forall.
        repeat rewrite apD10_V.
        rewrite (eisretr apD10).
        rewrite ap_V.
        reflexivity.
      rewrite X.
      rewrite transport_Vp. reflexivity.
    - intros H A B.
      pose (h := λ x, O_rec (BuildTruncType n {x:A & (B x)}) A pr1 x).
      pose (p := λ z, apD10 (O_rec_retr (BuildTruncType n {x:A & (B x)}) A pr1) z).
      pose (C := λ w, B(h w)).
      pose (g := λ z, (transport (λ u, (B u)) (inverse (p z)) z.2)).
      simpl in *.
      specialize (H (BuildTruncType n {x:A & (B x)}) C g).
      destruct H as [f q]. simpl in q.
      pose (k := (λ w, (h w; f w)) : (O (BuildTruncType n {x:A & (B x)})) -> (BuildTruncType n {x:A & (B x)})); simpl in k.

      rewrite <- subuniverse_iff_O.
      apply O_unit_retract_equiv with (μ := k).

      intro x; destruct x as [x1 x2]. unfold k.
      rewrite (q (x1;x2)).
      apply @path_sigma'  with (p := (p (x1;x2))).
      unfold g; simpl.
      rewrite transport_pV.
      reflexivity.
  Defined.
      
  Global Instance subuniverse_unit
    : IsSubu (BuildTruncType n Unit).
    rewrite <- subuniverse_iff_O.
    apply O_unit_retract_equiv with (μ := λ x:(O (BuildTruncType n Unit)), tt).
    intro u.
    destruct u; reflexivity.
  Defined.

  (* Proposition 11 *)
  Definition OUnit_is_Unit : trunctype_type (st (O (BuildTruncType n Unit))) = Unit
    := ap (trunctype_type) (ap st (O_modal (Build_subuniverse_Type (BuildTruncType n Unit) subuniverse_unit))^).

  (** Paths *)
  (* Proposition 11 *)
  Global Instance subuniverse_paths (A : subuniverse_Type) (x y:A)
  : IsSubu (BuildTruncType n (x = y)).
    rewrite <- subuniverse_iff_O.
    refine (O_unit_retract_equiv (BuildTruncType n (x=y)) _ _).
    - intros u.
      assert (p : (fun _:(O (BuildTruncType n (x = y))) => x) = (fun _=> y)).
      { apply (equiv_inv (IsEquiv := isequiv_ap
                                         (H:= O_equiv (BuildTruncType n (x = y)) A)
                                         (fun _ : (O (BuildTruncType n (x = y)))  => x)
                                         (fun _ : (O (BuildTruncType n (x = y)))  => y))).
        apply path_forall; intro v. exact v. }
      exact (ap10 p u).
    - intro u.
      etransitivity;
      [exact ((@ap10_ap_precompose _ _ _
                (O_unit (BuildTruncType n (x = y)))
                (fun _ : (O (BuildTruncType n (x = y))) => x)
                (fun _ : (O (BuildTruncType n (x = y))) => y)
                
                (equiv_inv (IsEquiv := isequiv_ap (H:= O_equiv (BuildTruncType n (x = y)) A)
                                                  (fun _ : (O (BuildTruncType n (x = y))) => x)
                                                  (fun _ : (O (BuildTruncType n (x = y))) => y))
                           (path_forall
                              ((fun _ : (O (BuildTruncType n (x = y))) => x) o (O_unit (BuildTruncType n (x = y))))
                              ((fun _ : (O (BuildTruncType n (x = y))) => y) o (O_unit (BuildTruncType n (x = y))))
                              idmap))
                u)^) | unfold path_forall, ap10; repeat rewrite eisretr; reflexivity].
  Qed.

  Lemma O_rec_inv (T:TruncType (trunc_S n)) (a b:T)
    : (O (BuildTruncType n (a = b))) -> (O (BuildTruncType n (b = a))).
  Proof.
    apply function_lift. 
    exact inverse.
  Defined.

  Lemma O_rec_inv_equiv (T:TruncType (trunc_S n)) (a b:T)
    : IsEquiv (O_rec_inv T a b).
  Proof.
    refine (isequiv_adjointify _ _ _ _);
    [ exact (O_rec_inv _ b a) | |];
    intro x; unfold O_rec_inv;
    rewrite <- (ap10 (function_lift_compose _ _ _ _ _)); cbn;
    match goal with
    |[|- function_lift _ _ ?ff _ = _] => assert (X: idmap = ff) by (apply path_forall; intro y; symmetry; apply inv_V)
    end;
    destruct X;
    apply (ap10 (function_lift_idmap _)).
  Defined.
  
  Lemma O_rec_concat (T:TruncType (trunc_S n)) (a b c :T)
  : (O (BuildTruncType n (a = b))) -> (O (BuildTruncType n (b = c)))
    -> (O (BuildTruncType n (a =c))).
  Proof.
    intros p q.
    revert q; apply function_lift_modal; intro q.
    revert p; apply function_lift_modal; intro p.
    apply O_unit; exact (p@q).
  Defined.
                                                                
  (* Lemma O_rec_concat (T:TruncType (trunc_S n)) (a b c :T.1) *)
  (* : (O (a=b; istrunc_paths T.1 n (H:=T.2) _ _)).1.1 -> (O (b=c; istrunc_paths T.1 n (H:=T.2) _ _)).1.1 *)
  (*   -> (O (a=c; istrunc_paths T.1 n (H:=T.2) _ _)).1.1. *)
  (*   intros p q. *)
  (*   revert q; apply O_rec; intro q. *)
  (*   revert p; apply O_rec; intro p. *)
  (*   apply O_unit. *)
  (*   exact (p@q). *)
  (* Defined. *)

  (* Lemma O_rec_concat_pV (T:TruncType (trunc_S n)) (a b :T.1) (p:(O (a=b; istrunc_paths T.1 n (H:=T.2) _ _)).1.1) *)
  (*   : O_rec_concat T a b a p (O_rec_inv T a b p) = O_unit (a = a; istrunc_paths T.1 n (H:=T.2) a a) 1. *)
  (* Proof. *)
  (*   unfold O_rec_inv, O_rec_concat; cbn. *)
  (*   unfold function_lift_modal. *)
  (*   rewrite (ap10 (reflect_factoriality_post _ _ _ _ _) _); cbn. *)
  (*   unfold function_lift. *)
  (*   pose (T.2). *)
  (*   pose (O_rec_retr (a = b; istrunc_paths T.1 n a b) *)
  (*       (O (a = a; istrunc_paths T.1 n a a))). *)
  (*   pose (ap10 (function_lift_compose (a=b;istrunc_paths T.1 n (H:=T.2) _ _) (b=a;istrunc_paths T.1 n (H:=T.2) _ _) (a=b;istrunc_paths T.1 n (H:=T.2) _ _) inverse (λ q : b = a, ○ (λ p0 : a = b, p0 @ q) p))). *)
        
  (** Things' *)
  
  
  Lemma reflect_factoriality_arrow_space
        (P:TruncType n)
        (Q R: subuniverse_Type)
        (f : P -> (Q -> R))
        (g : P -> (R -> Q))
        (S := Build_subuniverse_Type (BuildTruncType n (Q -> R)) _)
        (T := Build_subuniverse_Type (BuildTruncType n (R -> Q)) _)
        (RR := Build_subuniverse_Type (BuildTruncType n (R -> R)) _)
  : (λ v, (O_rec P S f v) o (O_rec P T g v)) = (λ v, O_rec P RR (λ v, (f v) o (g v)) v).
    simpl in *.
    pose (foo := @equiv_inj _ _ _ (O_equiv P RR)).
    specialize (foo (λ w, O_rec P S f w o O_rec P T g w) (λ w, O_rec P RR (λ v : P, f v o g v) w)). simpl in foo.
    apply foo; clear foo.
    apply path_forall; intro v. 
    transitivity ((λ v : P, f v o g v) v).
    - apply path_forall; intro r; simpl.
      pose (foo := ap10 (O_rec_retr P S f) v). 
      rewrite foo. 
      apply ap.
      pose (bar := ap10 (O_rec_retr P T g) v). 
      rewrite bar.
      reflexivity.
    - apply path_forall; intro r; simpl.
      pose (foo := ap10 (O_rec_retr P RR (λ (v0 : P) (x : R), f v0 (g v0 x))) v). 
      rewrite foo.
      reflexivity.
  Defined.

  
  Lemma transport_arrow_space
        (P Q : subuniverse_Type)
        (p : trunctype_type (st P) = trunctype_type (st Q))
  : (λ x0:Q, (transport idmap p (transport idmap p^ x0))) = idmap.
    destruct p; reflexivity.
  Qed.

  Lemma transport_arrow_space_dep_path
        (P Q : subuniverse_Type)
        (R : TruncType n)
        (p : R -> trunctype_type (st P) = trunctype_type (st Q))
  : (λ v:R, λ x0:Q, (transport idmap (p v) (transport idmap (p v)^ x0))) = λ v, idmap.
    apply path_forall; intro v.
    apply transport_arrow_space.
  Qed.

  Lemma ap10_O_retr_sect (P:TruncType n) (Q:subuniverse_Type) f x0
  : (ap10
       (O_rec_sect P Q
                   f) (O_unit P x0)) =
    (ap10
       (O_rec_retr P Q
                   (λ x1 : P, f (O_unit P x1))) x0).

    unfold O_rec_retr, O_rec_sect. simpl.
    pose (foo := O_equiv P Q).
    pose (adj := eisadj _ (IsEquiv := foo)).
    specialize (adj f). simpl in adj. 

    transitivity (ap10 (ap
                      (λ (f : (O P) → Q) (x : P), f (O_unit P x))
                      (eissect
                         (λ (f : (O P) → Q) 
                            (x : P), f (O_unit P x)) f)) x0).
    pose (rew := @ap10_ap_precompose).  rewrite rew. reflexivity.
    apply (ap (λ u, ap10 u x0) (x:=(ap
                                      (λ (f0 : ((O P)) → (Q)) (x : P), f0 (O_unit P x))
                                      (eissect
                                         (λ (f0 : ((O P)) → (Q)) (x : P),
                                          f0 (O_unit P x)) f))) (y:=(eisretr
                                                                          (λ (f0 : ((O P)) → (Q)) (x : P), f0 (O_unit P x))
                                                                          (λ x1 : P, f (O_unit P x1))))).
    exact adj^.
  Defined.

  Definition O_invol_ : forall T, O T = O (O T)
    := λ T, (O_modal (O T)).

  Lemma OO_unit_idmap (T:TruncType n)
  : O_unit (O T) = equiv_path _ _ (ap trunctype_type (ap st ((O_invol_ T)))).
      unfold O_invol_. unfold O_modal.
      Transparent isequiv_unique_subuniverse.
      pose (rew := eissect _ (IsEquiv := isequiv_unique_subuniverse (O T) (O (O T))) (path_trunctype
                                                                                        {|
                                                                                          equiv_fun := O_unit (O T);
                                                                                          equiv_isequiv := O_modal_equiv (O T) |})).
      simpl in rew. rewrite rew; clear rew.
      Opaque isequiv_unique_subuniverse.
    exact (ap (equiv_fun) (eissect _ (IsEquiv := @isequiv_path_trunctype ua n (O T) (O (O T))) {|
           equiv_fun := O_unit (O T);
           equiv_isequiv := O_modal_equiv (O T) |}))^.
  Defined.


End Reflective_Subuniverse.