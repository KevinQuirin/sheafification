Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import lemmas epi_mono equivalence truncation univalence sub_object_classifier limit_colimit modalities.
Require Import sheaf_base_case.

Set Universe Polymorphism.
Global Set Primitive Projections.
Set Implicit Arguments.

Local Open Scope path_scope.
Local Open Scope equiv_scope.
Local Open Scope type_scope.

(* Readability *)
Arguments trunc_arrow {H} {A} {B} {n} H0: simpl never.
Arguments trunc_sigma {A} {P} {n} H H0: simpl never.
Arguments istrunc_paths {A} {n} H x y: simpl never.
Arguments truncn_unique _ {n} A B H: simpl never.


  Context `{ua: Univalence}.
  Context `{fs: Funext}.
  
Variable n0 : trunc_index.

Definition n := trunc_S n0.

Variable nj : subuniverse_struct n.

Variable j_is_nj : forall P, (j P).1 = (nj.(O) (P.1; IsHProp_IsTrunc P.2 n0)).1.1.

Variable j_is_nj_unit : forall P x ,
                          transport idmap (j_is_nj P) (Oj_unit P x) = nj.(O_unit) (P.1; IsHProp_IsTrunc P.2 n0) x.

(* Left Exactness *)

Definition islex n (subU : subuniverse_struct n)
  := forall (X Y:Trunk n) (f : X.1 -> Y.1) (y:Y.1), (O subU (existT (λ T, IsTrunc n T) (hfiber f y) (trunc_sigma X.2 (λ a, istrunc_paths (trunc_succ (H:=Y.2)) _ _)))).1.1 = {rx : (O subU X).1.1 & function_lift subU X Y f rx = O_unit subU Y y}.


Lemma lex_compat_func (X Y:Trunk n) (f: X.1 -> Y.1) (y:Y.1)
: forall a:{a:X.1 & f a = y}, (function_lift nj X Y f (O_unit nj _ a.1) = O_unit nj Y y).
  intros a. simpl.
  pose (foo := ap10 (O_rec_retr X (O nj Y) (λ x : X .1, O_unit nj Y (f x))) a.1). unfold compose in foo; simpl in foo.
  exact (transport (λ U, O_rec X (O nj Y) (λ x : X .1, O_unit nj Y (f x)) (O_unit nj X a.1) = O_unit nj Y U) a.2 foo).
Defined.

Variable islex_nj : islex nj.

Variable lex_compat : forall (X Y:Trunk n) (f: X.1 -> Y.1) (y:Y.1) (a:{a:X.1 & f a = y}),
                       ((equiv_path _ _ (islex_nj X Y f y)) o (O_unit nj _)) a = (O_unit nj _ a.1; lex_compat_func X Y f a).

Section Sheafification.

  Definition nJ := {T : Trunk n & (nj.(O) T).1.1}.

  Definition incl_Aeq_Eeq (E:Type) (χ:E -> Trunk n) (x:{e:E & (χ e).1})
  : {e':{e:E & (χ e).1} & x.1 = e'.1} -> {e':E & x.1 = e'}
    := λ X, (X.1.1;X.2).

  Definition eq_dense_1 (E:Type) (χ:E -> Trunk n) (x:{e:E & (χ e).1})
  : {e':{e:E & (χ e).1} & x.1 = e'.1} <~> (χ x.1).1.
    exists (λ X:(∃ e' : ∃ e : E, (χ e) .1, x .1 = e' .1), (transport (λ u, (χ u).1) (X.2)^ X.1.2)).
    apply isequiv_adjointify with (g := (λ X, ((x.1;X);1)) : ((χ x.1).1 -> {e':{e:E & (χ e).1} & x.1 = e'.1})).
    - intro u. exact 1.
    - intro u. destruct u as [[e' e] p]. simpl in *. destruct p. simpl. exact 1.
  Defined.

  Definition is_dense_eq (E:Type) (char : E -> Trunk n) := forall e:E, ({e':E & e=e'}) = (O nj (char e)).1.1.

  Definition is_dense_diag (E:Type) (char : E -> Trunk n) (dense_eq : is_dense_eq char)
    := forall x:{e:E & (char e).1}, forall u:{e':{e:E & (char e).1} & x.1 = e'.1}, (equiv_path _ _ (dense_eq x.1)) o (incl_Aeq_Eeq char x) = (O_unit nj _) o ((eq_dense_1 char x)).

  Record EnJ (E:Type) :=
    {
      char :> E -> Trunk n ;
      dense_eq : forall e:E, ({e':E & e=e'}) = (O nj (char e)).1.1 ;
      dense_diag : forall x:{e:E & (char e).1}, forall u:{e':{e:E & (char e).1} & x.1 = e'.1}, (equiv_path _ _ (dense_eq x.1)) o (incl_Aeq_Eeq char x) = (O_unit nj _) o ((eq_dense_1 char x))
                                                                                                                                                                       (* For A a subobject of E, and x:A, this diagram commute : *)
                                                                                                                                                                       (*                                                         *)   
                                                                                                                                                                       (*   {e':A & x.1 = e'.1} === (χ x.1).1                     *)
                                                                                                                                                                       (*          |                    |                         *)
                                                                                                                                                                       (*        ι |                    | η                       *)
                                                                                                                                                                       (*          |                    |                         *)
                                                                                                                                                                       (*          v                    v                         *)
                                                                                                                                                                       (*    {e':E & x.1 = e'}  === (O nj (χ x.1)).1.1            *)
                                                                                                                                                                       
    }.


  Definition witness_is_eta (E:Type) (χ:EnJ E) (x:{e:E & (χ e).1})
  : transport idmap (dense_eq χ x .1) (x .1; 1) = O_unit nj (χ x .1) x.2
    := ap10 (dense_diag χ x (x;1)) (x;1).

  Definition EnJ_is_nJ (E:Type) (χ : EnJ E)
  : forall e:E, (O nj (χ e)).1.1
    := λ e, transport (λ T, T) (dense_eq χ e) (e;idpath).

  Definition dense_eta_equal (E:Type) (χ : EnJ E) (x:E) : forall (v w:(χ x).1), O_unit nj (χ x) v = O_unit nj (χ x) w.
    intros v w.
    assert (forall (a b:(∃ e' : E, x = e')), a=b).
    intros a b.
    destruct a as [a p], b as [b q]. simpl.
    apply @path_sigma' with (p := p^@q).
    destruct p. destruct q. simpl. exact idpath.
    rewrite (dense_eq χ) in X; apply X.
  Defined.

  Definition E_to_χmono_map (T:Trunk (trunc_S n)) E (χ : E -> J) (f : E -> (pr1 T)) : 
    (nchar_to_sub (pr1 o χ)).1 -> T.1 := f o pr1.

  Definition E_to_χ_map (T:Trunk (trunc_S n)) E (χ : EnJ E) (f : E -> (pr1 T)) : 
    (nchar_to_sub χ).1 -> T.1 := f o pr1.

  Definition separated T :=  ∀ E (χ : EnJ E), IsMono (E_to_χ_map T (E:=E) χ).
  
  Definition Snsheaf_struct T := (separated T) /\ (∀ E (χ : E -> J), IsEquiv (E_to_χmono_map T (E:=E) (χ:=χ))). 

  Definition SnType_j_Type := {T : Trunk (trunc_S n) & Snsheaf_struct T}.

  Definition separated_is_HProp T : IsHProp (separated T).
    repeat (apply trunc_forall).
  Defined.

  Definition Snsheaf_struct_is_HProp T : IsHProp (Snsheaf_struct T).
    apply trunc_prod.
  Defined.

  Definition nj_inter_f (A : Trunk n) (φ : A.1 -> Trunk n) : 
    (nj.(O) ({a:A.1 & (φ a).1}; trunc_sigma (A.2) (fun a => (φ a).2))).1.1 ->
    (nj.(O) ({a:A.1 & (nj.(O) (φ a)).1.1}; trunc_sigma (A.2) (fun a => (nj.(O) (φ a)).1.2))).1.1
    := function_lift
         nj
         ({a:A.1 & (φ a).1}; trunc_sigma (A.2) (fun a => (φ a).2))
         ({a:A.1 & (nj.(O) (φ a)).1.1}; trunc_sigma (A.2) (fun a => (nj.(O) (φ a)).1.2))
         (λ X, (X.1;nj.(O_unit) _ X.2)).

  Definition nj_inter_g (A : Trunk n) (φ : A.1 -> Trunk n) : 
    (nj.(O) ({a:A.1 & (nj.(O) (φ a)).1.1}; trunc_sigma (A.2) (fun a => (nj.(O) (φ a)).1.2))).1.1 ->
    (nj.(O) ({a:A.1 & (φ a).1}; trunc_sigma (A.2) (fun a => (φ a).2))).1.1.
    apply O_rec. intro X.
    generalize X.2. apply O_rec; intro φa.
    apply nj.(O_unit). exact (X.1;φa).
  Defined.

  Instance nj_inter_equiv (A : Trunk n) (φ : A.1 -> Trunk n) : IsEquiv (nj_inter_f A φ).
  apply (isequiv_adjointify _ (nj_inter_g A φ)).
  - intro x. unfold nj_inter_f, nj_inter_g. simpl in *.
    transitivity (function_lift nj
                      (∃ a0 : A .1, (φ a0) .1;
                       trunc_sigma A .2 (λ a0 : A .1, (φ a0) .2))
                      (∃ a0 : A .1, ((O nj (φ a0)) .1) .1;
                       trunc_sigma  
                         A .2 (λ a0 : A .1, ((O nj (φ a0)) .1) .2))
                      (λ X : ∃ a0 : A .1, (φ a0) .1, (X .1; O_unit nj (φ X .1) X .2))
                      (O_rec
                         (∃ a0 : A .1, ((O nj (φ a0)) .1) .1;
                          trunc_sigma  
                            A .2 (λ a0 : A .1, ((O nj (φ a0)) .1) .2))
                         (O nj
                            (∃ a0 : A .1, (φ a0) .1;
                             trunc_sigma  A .2
                                          (λ a0 : A .1, (φ a0) .2)))
                         (λ X : ∃ a0 : A .1, ((O nj (φ a0)) .1) .1,
                            (function_lift nj (φ X.1) (∃ a0 : A .1, (φ a0) .1;
                                                       trunc_sigma  
                                                         A .2 (λ a0 : A .1, (φ a0) .2)) (λ b, (X.1;b)))
                              X .2) x)
      ); auto with path_hints.

    pose (foo := ap10 (reflect_factoriality_pre
                         (∃ a0 : A .1, ((O nj (φ a0)) .1) .1;
                          trunc_sigma  
                            A .2 (λ a0 : A .1, ((O nj (φ a0)) .1) .2))
                         (((O nj
                              (∃ a0 : A .1, (φ a0) .1;
                               trunc_sigma A .2
                                           (λ a0 : A .1, (φ a0) .2)))))
                         (((O nj
                              (∃ a0 : A .1, ((O nj (φ a0)) .1) .1;
                               trunc_sigma 
                                 A .2 (λ a0 : A .1, ((O nj (φ a0)) .1) .2)))))
                         (function_lift nj
                                        (∃ a0 : A .1, (φ a0) .1;
                                         trunc_sigma  A .2 (λ a0 : A .1, (φ a0) .2))
                                        (∃ a0 : A .1, ((O nj (φ a0)) .1) .1;
                                         trunc_sigma 
                                           A .2 (λ a0 : A .1, ((O nj (φ a0)) .1) .2))
                                        (λ X : ∃ a0 : A .1, (φ a0) .1, (X .1; O_unit nj (φ X .1) X .2)))
                         ((λ X : ∃ a0 : A .1, ((O nj (φ a0)) .1) .1,
                             function_lift nj (φ X .1)
                                           (∃ a0 : A .1, (φ a0) .1;
                                            trunc_sigma  A .2
                                                         (λ a0 : A .1, (φ a0) .2)) (λ b : (φ X .1) .1, (X .1; b)) 
                                           X .2))) x
         ). 
    etransitivity; try exact foo. clear foo.

    transitivity (
        O_rec
          (∃ a0 : A .1, ((O nj (φ a0)) .1) .1;
           trunc_sigma 
             A .2 (λ a0 : A .1, ((O nj (φ a0)) .1) .2))
          (O nj
             (∃ a0 : A .1, ((O nj (φ a0)) .1) .1;
              trunc_sigma 
                A .2 (λ a0 : A .1, ((O nj (φ a0)) .1) .2)))
          (λ x0 : ∃ a0 : A .1, ((O nj (φ a0)) .1) .1,
             function_lift nj (φ x0 .1)
                           (∃ a0 : A .1, ((O nj (φ a0)) .1) .1;
                            trunc_sigma
                              A .2 (λ a0 : A .1, ((O nj (φ a0)) .1) .2))
                           (λ x : (φ x0 .1) .1, (x0 .1; O_unit nj (φ x0 .1) x)) 
                           x0 .2) x
      ).
    apply (ap (λ u, O_rec
                      (∃ a0 : A .1, ((O nj (φ a0)) .1) .1;
                       trunc_sigma 
                         A .2 (λ a0 : A .1, ((O nj (φ a0)) .1) .2))
                      (O nj
                         (∃ a0 : A .1, ((O nj (φ a0)) .1) .1;
                          trunc_sigma 
                            A .2 (λ a0 : A .1, ((O nj (φ a0)) .1) .2))) u x)).
    apply path_forall; intro x0.
    exact (ap10 (reflect_functoriality
                   nj
                   (φ x0 .1)
                   (∃ a0 : A .1, (φ a0) .1;
                    trunc_sigma A .2
                                (λ a0 : A .1, (φ a0) .2))
                   (∃ a0 : A .1, ((O nj (φ a0)) .1) .1;
                    trunc_sigma
                      A .2 (λ a0 : A .1, ((O nj (φ a0)) .1) .2))
                   (λ X : ∃ a0 : A .1, (φ a0) .1, (X .1; O_unit nj (φ X .1) X .2))
                   (λ b : (φ x0 .1) .1, (x0 .1; b))) x0.2
          ).
    exact (ap10 (O_rec_O_rec_dep_sect nj
                                      (∃ a0 : A .1, ((O nj (φ a0)) .1) .1;
                                       trunc_sigma
                                         A .2 (λ a0 : A .1, ((O nj (φ a0)) .1) .2))
                                      (λ a, (φ a.1))
                                      (λ u, λ v, (u.1;v))
                                      (λ u, u.2)
                                      (λ a, eta_sigma a)) x); simpl in foo.   
  - intro x. unfold nj_inter_f, nj_inter_g. simpl.
    pose (foo := ap10 (reflect_factoriality_post
                         (∃ a : A .1, (φ a) .1;
                          trunc_sigma  A .2 (λ a : A .1, (φ a) .2))
                         (∃ a : A .1, ((O nj (φ a)) .1) .1;
                          trunc_sigma 
                            A .2 (λ a : A .1, ((O nj (φ a)) .1) .2))
                         (O nj
                            (∃ a : A .1, (φ a) .1;
                             trunc_sigma A .2 (λ a : A .1, (φ a) .2)))
                         (λ X : (∃ a : A .1, ((O nj (φ a)) .1) .1;
                                 trunc_sigma 
                                   A .2 (λ a : A .1, ((O nj (φ a)) .1) .2)) .1,
                                O_rec (φ X .1)
                                      (O nj
                                         (∃ a : A .1, (φ a) .1;
                                          trunc_sigma  A .2 (λ a : A .1, (φ a) .2)))
                                      (λ φa : (φ X .1) .1,
                                              O_unit nj
                                                     (∃ a : A .1, (φ a) .1;
                                                      trunc_sigma  A .2 (λ a : A .1, (φ a) .2))
                                                     (X .1; φa)) X .2)
                         (λ X : (∃ a : A .1, (φ a) .1;
                                 trunc_sigma 
                                   A .2 (λ a : A .1, (φ a) .2)) .1,
                                (X .1; O_unit nj (φ X .1) X .2)))
                      x
         ).
    unfold compose in foo; simpl in foo.
    etransitivity; try exact foo. clear foo.
    apply (ap10 (O_rec_O_rec_dep_retr nj
                                      (∃ a : A .1, (φ a) .1; trunc_sigma A .2 (λ a : A .1, (φ a) .2))
                                      (λ a, (φ a .1))
                                      (λ a b, (a.1;b))
                                      (λ a, a.2)
                                      (λ a, eta_sigma a))
                x).
  Defined.

  Definition nj_inter (A : Trunk n) (φ : A.1 -> Trunk n) : 
    nj.(O) ({a:A.1 & (φ a).1}; trunc_sigma (A.2) (fun a => (φ a).2)) =
    nj.(O) ({a:A.1 & (nj.(O) (φ a)).1.1}; trunc_sigma (A.2) (fun a => (nj.(O) (φ a)).1.2)).
    apply unique_subuniverse. apply truncn_unique.
    exact fs.
    apply path_universe_uncurried. exact (BuildEquiv _ _ _ (nj_inter_equiv _ _)).
  Defined.

  Definition nj_fibers_compose A B C (f : A -> B) (g : B -> C) (c : C)
             (HB : ∀ b : B, IsTrunc n (hfiber f b)) (HC : ∀ c : C, IsTrunc n (hfiber g c))
  :
    nj.(O) (hfiber (g o f) c; function_trunc_compo n f g HB HC c) =
    nj.(O) ({ w :  hfiber g c &  (nj.(O) (hfiber f (pr1 w);(HB (pr1 w)))).1.1};
            trunc_sigma (HC c) (fun a => (O nj (hfiber f a .1; HB a .1)).1 .2)).
    assert ((hfiber (g o f) c; function_trunc_compo n f g HB HC c) =
            ({ w : (hfiber g c) & hfiber f (pr1 w) }; trunc_sigma (HC c) (fun w => HB w.1))).
    apply truncn_unique. exact fs. apply fibers_composition.
    apply (transport (fun X => O nj X = _) (inverse X)). clear X.
    apply (nj_inter (hfiber g c; HC c) (fun w => (hfiber f w .1; HB w.1))).
  Defined.
  
  Definition type_j_f E (χ: E -> J) :
    (E -> subuniverse_Type nj) -> pr1 (nchar_to_sub (pr1  o χ))
    -> subuniverse_Type nj := λ α e, α (pr1 e).

  Definition type_j_inv E (χ: E -> J) : (pr1 (nchar_to_sub (pr1  o χ)) -> subuniverse_Type nj) -> E -> subuniverse_Type nj :=
    λ α e, let f := (pr2 (nchar_to_sub (pr1  o α))) in
           let m := (pr2 (nchar_to_sub (pr1  o χ))) in
           nj.(O) (nsub_to_char n ({b : _ &  pr1 (pr1 (α b))}; ((pr1 m) o (pr1 f); function_trunc_compo n (pr1 f) (pr1 m) (pr2 f) (fun e => IsHProp_IsTrunc (pr2 m e) n0))) e).

  Instance nTjTiSnTjT_eq E (χ : E -> J) : IsEquiv (λ (f : E -> subuniverse_Type nj) (t : {b : E & pr1 (pr1 (χ b))}), f (pr1 t)). 
  apply (isequiv_adjointify _ (type_j_inv (E:=E) (χ := χ))).
  - intro φ.
    unfold type_j_inv, compose. simpl. unfold nchar_to_sub, hfiber, compose in φ; simpl in φ.
    apply path_forall; intro x.
    rewrite (O_modal (φ x)).
    repeat apply ap.
    apply truncn_unique.
    exact fs.
    eapply concat; try exact (hfiber_pi1 ( (λ t : _, pr1 (pr1 (φ t)))) x).
    symmetry. apply (hfiber_mono (pr1 ) (g:=pr1 )).
    intros X Y. apply subset_is_subobject. intro.
    exact (pr2 (pr1 (χ a))).
  - intro φ.
    unfold type_j_inv, compose. simpl.
    apply path_forall; intro x.
    rewrite (O_modal (φ x)).
    unfold nsub_to_char. simpl.
    assert ((hfiber
               (λ t : {b : {b : E | ((χ b) .1) .1} | ((φ b .1) .1) .1}, (t .1) .1) x;
             function_trunc_compo n pr1 pr1
                                  (nchar_to_sub_compat (λ t : {b : E | ((χ b) .1) .1}, (φ t .1) .1))
                                  (λ e : E,
                                         IsHProp_IsTrunc (nchar_to_sub_compat (λ t : E, (χ t) .1) e) n0) x) =
            (hfiber
               (λ t : {b : {b : E | ((φ b) .1) .1} | ((χ b .1) .1) .1}, (t .1) .1) x;
             function_trunc_compo n pr1 pr1
                                  (λ e : _,
                                         IsHProp_IsTrunc (nchar_to_sub_compat (λ t : _, (χ (t.1)) .1) e) n0) 
                                  (nchar_to_sub_compat (λ t : E, (φ t) .1)) x)).
    apply truncn_unique. exact fs. apply (inter_symm (fun b => ((χ b) .1) .1) (fun b => ((φ b) .1) .1)).
    apply (transport (fun x => O nj x = _ ) (inverse X)). clear X.
    pose (X := (nj_fibers_compose x (λ e : {b : E | ((φ b) .1) .1},
                                           IsHProp_IsTrunc
                                             (nchar_to_sub_compat (λ t : {b : E | ((φ b) .1) .1}, (χ t .1) .1) e)
                                             n0) (nchar_to_sub_compat (λ t : E, (φ t) .1)))). unfold compose in X.
    apply (transport (fun x => x = _) (inverse X)). clear X.
    
    apply ap. apply truncn_unique. simpl.
    (* etransitivity. *)
    exact fs.
    apply path_universe_uncurried.
    eapply transitive_equiv.
    apply equiv_sigma_contr.
    intro. pose (f := j_is_nj (hfiber pr1 a .1; 
                               (nchar_to_sub_compat (λ t : {b : E | ((φ b) .1) .1}, (χ t .1) .1)
                                                    a .1))).
    apply (transport (fun X => Contr X) f).
    simpl.
    apply (transport (fun X => Contr (not (not X))) (inverse (nhfiber_pi1 _ _))).
    apply Oj_J_Contr.
    apply equiv_path.
    etransitivity. apply nhfiber_pi1. reflexivity.
  Defined.

  Definition nTjTiseparated_eq_fun_univ (E:Type) (χ:EnJ E) φ1 φ2
             (p: E_to_χ_map (subuniverse_Type nj; subuniverse_Type_is_TrunkSn (subU:=nj)) χ φ1 =
                 E_to_χ_map (subuniverse_Type nj; subuniverse_Type_is_TrunkSn (subU:=nj)) χ φ2)
             (x:E)
  :  ((φ1 x).1.1 -> (φ2 x).1.1).
    unfold E_to_χ_map in p.
    generalize dependent (EnJ_is_nJ χ x).
    pose (p0 := O_rec (((χ x))) (existT (fun T => (subuniverse_HProp nj T).1) (((φ1 x) .1) .1 → ((φ2 x) .1) .1 ; trunc_arrow ((φ2 x) .1).2) (subuniverse_arrow (((φ1 x) .1) .1) (φ2 x)))); simpl in p0.
    apply p0.
    intro v. simpl.

    assert (eq := (ap10 p (x;v))). unfold compose in eq; simpl in eq.
    exact (transport (λ U, U) (eq..1..1)).
  Defined.
  
  Lemma nTjTiseparated_eq_fun_univ_invol (E:Type) (χ:EnJ E) φ1 φ2 (p: E_to_χ_map
                                                                        (subuniverse_Type nj; subuniverse_Type_is_TrunkSn (subU:=nj)) χ φ1 =
                                                                      E_to_χ_map
                                                                        (subuniverse_Type nj; subuniverse_Type_is_TrunkSn (subU:=nj)) χ φ2) (x:E)
  : forall (y:(φ2 x).1.1), nTjTiseparated_eq_fun_univ p x (nTjTiseparated_eq_fun_univ p^ x y) = y.
  Proof.
    intro y. unfold nTjTiseparated_eq_fun_univ; simpl.
    unfold E_to_χ_map in p; simpl in *.

    pose (foo := ap10 (ap10 (reflect_factoriality_arrow_space
                               (χ x)
                               (φ1 x)
                               (φ2 x)
                               (λ v : (χ x) .1,
                                      transport idmap
                                                (ap10 p (x; v))..1..1)
                               (λ v : (χ x) .1,
                                      transport idmap
                                                
                                                (ap10 p ^ (x; v))..1..1))
                            (EnJ_is_nJ χ x)) y
         ). unfold compose in foo; simpl in foo.
    apply (transport (λ u, u = y) foo^). clear foo.

    pose (fooo := @transport_arrow_space_dep_path n nj fs (φ1 x) (φ2 x) (χ x) (λ v, (ap10 p (x;v))..1..1)).
    simpl in fooo.

    transitivity (O_rec (χ x)
                    ((((φ2 x) .1) .1 → ((φ2 x) .1) .1; trunc_arrow ((φ2 x).1.2));
                     subuniverse_arrow ((φ2 x) .1) .1 (φ2 x))
                    (λ (v : (χ x) .1) (x0 : ((φ2 x) .1) .1),
                     transport idmap
                               
                               (ap10 p (x; v))..1..1
                               (transport idmap
                                          
                                          (ap10 p (x; v))..1..1^ x0)) (EnJ_is_nJ χ x) y); auto with path_hints.

    apply (ap (λ u, O_rec (χ x)
                          ((((φ2 x) .1) .1 → ((φ2 x) .1) .1; trunc_arrow ((φ2 x).1.2));
                           subuniverse_arrow ((φ2 x) .1) .1 (φ2 x))
                          u (EnJ_is_nJ χ x) y)).
    apply path_forall; intro v. apply path_forall; intro x0.
    apply ap. 
    apply (ap (λ U, transport idmap
                              U x0)).
    transitivity ((ap10 p (x; v))^..1..1).
    apply ap. apply ap.
    apply (ap10_V p (x;v)).
    unfold pr1_path.
    rewrite ap_V. rewrite ap_V. exact 1.
    
    apply (transport (λ U, O_rec (χ x)
                                 ((((φ2 x) .1) .1 → ((φ2 x) .1) .1; trunc_arrow ((φ2 x).1.2));
                                  subuniverse_arrow ((φ2 x) .1) .1 (φ2 x))
                                 U
                                 (EnJ_is_nJ χ x) y = y) fooo^).
    clear fooo; simpl.
    pose (foo := ap10 (ap10 (O_rec_const (χ x) ((((φ2 x) .1) .1 → ((φ2 x) .1) .1; trunc_arrow ((φ2 x).1.2));
                                                subuniverse_arrow ((φ2 x) .1) .1 (φ2 x)) idmap) (EnJ_is_nJ χ x)) y). simpl in foo.
    etransitivity; [exact foo | exact 1].
  Defined.

  Definition nTjTiseparated_eq_inv (E:Type) (χ:EnJ E) φ1 φ2 :
    E_to_χ_map
      (subuniverse_Type nj; subuniverse_Type_is_TrunkSn (subU:=nj)) χ φ1 =
    E_to_χ_map 
      (subuniverse_Type nj; subuniverse_Type_is_TrunkSn (subU:=nj)) χ φ2
    -> φ1 = φ2.
    intro p.
    simpl in *.
    unfold E_to_χ_map in p; simpl in p.
    apply path_forall; intro x.
    apply unique_subuniverse; apply truncn_unique.
    exact fs.
    apply path_universe_uncurried.
    exists (nTjTiseparated_eq_fun_univ p x).
    apply isequiv_adjointify with (g := nTjTiseparated_eq_fun_univ (inverse p) x).
    - exact (nTjTiseparated_eq_fun_univ_invol p x).
    - exact (transport (λ u, ∀ y : ((φ1 x) .1) .1, nTjTiseparated_eq_fun_univ (inverse p) x (nTjTiseparated_eq_fun_univ u x y) = y) (inv_V p) (nTjTiseparated_eq_fun_univ_invol (inverse p) x)).
  Defined.

  Lemma nTjTiseparated_eq : separated (subuniverse_Type nj ; @subuniverse_Type_is_TrunkSn _ nj).
    intros E χ φ1 φ2.
    apply isequiv_adjointify with (g := @nTjTiseparated_eq_inv E χ φ1 φ2).
    - intro p. 
      unfold E_to_χ_map in *; simpl in *.
      apply (@equiv_inj _ _ _ (isequiv_ap10 (φ1 o (@pr1 _ (fun e => (χ e).1))) (φ2 o pr1))).
      apply path_forall; intro x.

      unfold nTjTiseparated_eq_inv.
      rewrite ap10_ap_precompose. unfold ap10 at 1, path_forall; rewrite eisretr.

      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_unique_subuniverse _ _))). apply isequiv_inverse.
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_truncn_unique _ _))). apply isequiv_inverse. 
      apply (@equiv_inj _ _ _ (isequiv_equiv_path ((φ1 o pr1) x).1.1 ((φ2 o pr1) x).1.1)).
      repeat rewrite eissect.
      unfold path_universe_uncurried. rewrite eisretr.
      apply equal_equiv.
      unfold nTjTiseparated_eq_fun_univ, EnJ_is_nJ. 
      apply (transport (λ U, O_rec _ ((((φ1 (pr1 x)).1).1 → ((φ2 (pr1 x)).1).1;
      trunc_arrow ((φ2 (pr1 x)).1).2);
     subuniverse_arrow ((φ1 (pr1 x)).1).1 (φ2 (pr1 x))) _ U = _) ((witness_is_eta χ x)^)).
      etransitivity;
        try exact (ap10 (O_rec_retr (χ x.1) ((((φ1 x .1) .1) .1 → ((φ2 x .1) .1) .1; trunc_arrow ((φ2 x.1).1.2)); subuniverse_arrow ((φ1 x .1) .1) .1 (φ2 x .1)) (λ v : (χ x .1) .1, transport idmap ((ap10 p (x .1; v)) ..1) ..1)) x.2).
      repeat apply ap. destruct x as [x1 x2]. exact 1.
      
    - intro p; destruct p.
      unfold E_to_χ_map, nTjTiseparated_eq_inv in *; simpl in *.
      eapply concat; [idtac | apply (path_forall_1 φ1)]; apply ap.
      apply path_forall; intro x; simpl.
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_unique_subuniverse _ _))). apply isequiv_inverse.
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_truncn_unique _ _))). apply isequiv_inverse.
      apply (@equiv_inj _ _ _ (isequiv_equiv_path (((φ1 x) .1) .1) (((φ1 x) .1) .1))).
      repeat rewrite eissect. unfold path_universe_uncurried. rewrite eisretr; simpl.
      unfold equiv_path. simpl.
      apply equal_equiv.
      unfold transport, nTjTiseparated_eq_fun_univ; simpl.
      exact (ap10 (O_rec_const  (χ x) ((((φ1 x) .1) .1 → ((φ1 x) .1) .1; trunc_arrow ((φ1 x).1.2));
                                       subuniverse_arrow ((φ1 x) .1) .1 (φ1 x)) idmap) (EnJ_is_nJ χ x)). 
  Defined.

  Lemma nType_j_Type_is_SnType_j_Type : Snsheaf_struct (subuniverse_Type nj ;
                                                        @subuniverse_Type_is_TrunkSn _ nj).
  Proof.
    split.
    apply nTjTiseparated_eq.
    intros E χ. unfold E_to_χ_map, compose; simpl.
    exact (nTjTiSnTjT_eq _).
  Defined.

  Definition nType_j_Type_sheaf : SnType_j_Type :=
    ((subuniverse_Type nj; @subuniverse_Type_is_TrunkSn _ nj);nType_j_Type_is_SnType_j_Type).

  Instance dep_prod_SnType_j_Type_eq
           (A : Type)
           (B : A -> SnType_j_Type)
  : forall (E:Type) (χ : E -> J) (H := λ a, (snd (pr2 (B a))) E χ),
      IsEquiv (λ (f : E -> ∀ a : A, pr1 (pr1 (B a))) (t : {b : E & pr1 (pr1 (χ b))}), f (pr1 t)).
  intros E χ H.   
  apply (isequiv_adjointify _ (λ g e a, (@equiv_inv _ _ _ (H a) (λ x, g x a) e))).
  - intro φ.
    apply path_forall; intro x.
    apply path_forall; intro a.
    destruct (H a); simpl in *.
    clear eisadj; clear eissect.
    unfold nchar_to_sub, compose in equiv_inv; simpl.
    unfold Sect, nchar_to_sub, compose, E_to_χmono_map, compose in eisretr.
    specialize (eisretr (λ x, φ x a)).
    exact (ap10 eisretr x).
  - intro φ.
    apply path_forall; intro x.
    apply path_forall; intro a.
    destruct (H a); simpl in *.
    clear eisadj; clear eisretr.
    unfold nchar_to_sub, compose in equiv_inv; simpl.
    unfold Sect, nchar_to_sub, compose, E_to_χ_map, compose in eissect.
    specialize (eissect (λ x, φ x a)).
    exact (ap10 eissect x).
  Defined.

  Definition dep_prod_SnType_j_Type_sep_inv
             (A : Type)
             (B : A -> SnType_j_Type)
             (E : Type)
             (χ : EnJ E)
             (x y : E -> ∀ a : A, ((B a) .1) .1)
  : (λ (f : E -> ∀ a : A, ((B a) .1) .1) (t : {b : E | ((χ b)) .1}),
     f t .1) x =
    (λ (f : E -> ∀ a : A, ((B a) .1) .1) (t : {b : E | ((χ b)) .1}),
     f t .1) y
    -> x = y.
    intro H; simpl in H.
    apply path_forall; intro u.
    apply path_forall; intro a.
    refine (@ap10 _ _ (λ u, x u a) (λ u, y u a) _ u).
    pose ((fst (B a).2) E χ (λ v, x v a) (λ v, y v a)).
    exact (equiv_inv (IsEquiv := i) (path_forall _ _ (λ t, apD10 ((apD10 H) t) a))).
  Defined.

  Lemma ap_path_forall (A B C:Type) (f:A -> B) (g h:B -> C) (eq:forall x, g x = h x)              
  : ap (λ u, u o f) (path_forall g h eq) = path_forall (g o f) (h o f) (λ x, (eq (f x))).
    apply (@equiv_inj _ _ _ (isequiv_ap10 _ _)).
    unfold ap10 at 2, path_forall at 2; rewrite eisretr.
    apply path_forall; intro a.
    rewrite ap10_ap_precompose.
    unfold ap10, path_forall; rewrite eisretr. exact 1.
  Qed.

  Lemma dep_prod_SnType_j_Type_sep
        (A : Type)
        (B : A -> SnType_j_Type)
  : forall (E:Type) (χ : EnJ E), IsMono
                                   (λ (f : E -> ∀ a : A, (B a).1.1) (t : {b : E & (χ b).1}), f (t.1)).
    intros E χ.
    unfold IsMono.
    intros f g.
    apply @isequiv_adjointify with (g := @dep_prod_SnType_j_Type_sep_inv A B E χ f g).
    - unfold Sect.
      intro p.
      unfold dep_prod_SnType_j_Type_sep_inv. 
      unfold E_to_χ_map, compose. simpl.
      unfold equiv_inv.
      pose (foo := @ap_path_forall (∃ b : E, (χ b) .1)
                                   E
                                   (∀ a : A, ((B a) .1) .1)
                                   pr1
                                   f
                                   g
                                   (λ u : E,
                                          path_forall (f u) (g u)
                                                      (λ a : A,
                                                             ap10
                                                               ((let (equiv_inv, eisretr, eissect, _) :=
                                                                     fst (B a) .2 E χ (λ v : E, f v a) (λ v : E, g v a) in
                                                                 equiv_inv)
                                                                  (path_forall (λ t : ∃ b : E, (χ b) .1, f t .1 a)
                                                                               (λ t : ∃ b : E, (χ b) .1, g t .1 a)
                                                                               (λ t : ∃ b : E, (χ b) .1, apD10 (apD10 p t) a))) u))).
      apply (transport (λ U, U=p) foo^); clear foo.
      apply (@equiv_inj _ _ _ (isequiv_ap10 _ _)).
      unfold ap10 at 1, path_forall at 1; rewrite eisretr.
      apply path_forall; intro x.
      apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)); unfold path_forall at 1; rewrite eisretr.
      apply path_forall; intro a.

      rewrite <- (@ap10_ap_precompose (∃ b : E, (χ b) .1)
                             E
                             (((B a) .1) .1)
                             pr1
                             (λ v, f v a)
                             (λ v, g v a)
                             ((let (equiv_inv, eisretr, eissect, _) :=
                                   fst (B a) .2 E χ (λ v : E, f v a) (λ v : E, g v a) in
                               equiv_inv)
                                (path_forall (λ t : ∃ b : E, (χ b) .1, f t .1 a)
                                             (λ t : ∃ b : E, (χ b) .1, g t .1 a)
                                             (λ t : ∃ b : E, (χ b) .1, apD10 (apD10 p t) a)))
                             x).
      rewrite (@eisretr _ _ _ (fst (B a) .2 E χ (λ v : E, f v a) (λ v : E, g v a))).

      unfold ap10, path_forall; rewrite eisretr.
      exact 1.
    - intro v. unfold dep_prod_SnType_j_Type_sep_inv. 
      unfold E_to_χ_map. simpl.
      destruct v. simpl.
      etransitivity; [idtac | apply path_forall_1]; apply ap; apply path_forall; intro x.
      etransitivity; [idtac | apply path_forall_1]; apply ap; apply path_forall; intro y.
      assert ((apD10
                 ((let (equiv_inv, eisretr, eissect, _) :=
                       fst (B y) .2 E χ (λ v : E, f v y) (λ v : E, f v y) in
                   equiv_inv)
                    (path_forall (λ t : ∃ b : E, (χ b) .1, f t .1 y)
                                 (λ t : ∃ b : E, (χ b) .1, f t .1 y) (λ t : ∃ b : E, (χ b) .1, 1)))) = λ _, 1).
      apply (@equiv_inj _ _ _ (isequiv_path_forall _ _)).
      unfold path_forall. rewrite eissect. 
      apply (@equiv_inj _ _ _ (fst (B y) .2 E χ (λ v : E, f v y) (λ v : E, f v y))).
      pose (foo := @eisretr _ _ _ (fst (B y) .2 E χ (λ v : E, f v y) (λ v : E, f v y))).
      unfold Sect, equiv_inv in foo; simpl in foo.
      rewrite foo.
      unfold E_to_χ_map. simpl.
      apply (@equiv_inj _ _ _ (isequiv_ap10 _ _)).
      unfold ap10 at 1;
        rewrite eisretr.
      apply path_forall; intro t.
      rewrite ap10_ap_precompose.
      unfold ap10; rewrite eisretr. exact 1.
      exact (apD10 X x).
  Defined.
  
  Definition dep_prod_SnType_j_Type : forall A (B : A -> SnType_j_Type) ,
                                        Snsheaf_struct (forall a, pr1 (pr1 (B a)); 
                                                        @trunc_forall _ A (fun a => pr1 (pr1 (B a))) (trunc_S n) (fun a => pr2 (pr1 (B a)))).
    intros. split. 
    exact (dep_prod_SnType_j_Type_sep _).
    exact (dep_prod_SnType_j_Type_eq _).
  Defined.

  Definition closed E (χ : E -> Trunk n) := forall e, IsEquiv (nj.(O_unit) (χ e)).
  
  Definition closed' E A (m : {f : A -> E & forall b:E, IsTrunc n (hfiber f b)}) := closed (nsub_to_char n (A;m)).

  Definition cloture E (χ : E -> Trunk n) : E -> Trunk n := pr1 o nj.(O) o χ.
  
  Definition cloture' E A (m : {f : A -> E & forall b:E, IsTrunc n (hfiber f b)}) :=
    nchar_to_sub (cloture (nsub_to_char n (A;m))).

  Definition cloture_is_closed (E :Type) (χ : E -> Trunk n) : closed (cloture χ).
    intro. apply O_modal_equiv. exact fs.
  Defined.

  Lemma cloture_is_closed' (A:Type) (E:Type) (m : {f : A -> E & forall e:E, IsTrunc n (hfiber f e)}) : closed' (pr2 (cloture' m)).
    unfold closed', cloture'. 
    rewrite (eta_sigma (nchar_to_sub (cloture (nsub_to_char n (A; m))))).
    pose (f := cloture_is_closed (nsub_to_char n (A; m))). 
    rewrite <- (@nsub_eq_char_retr ua fs n _ (cloture (nsub_to_char n (A; m)))) in f.
    exact f.
  Defined.
  
  Definition δ (T:Trunk (trunc_S n)) : T.1 * T.1-> Trunk n.
    intros x. exists (fst x = snd x). apply istrunc_paths.
    exact T.2.
  Defined.

  Definition Δ (T:Trunk (trunc_S n)) := nchar_to_sub (δ T).
  
  Definition clδ T := pr1  o nj.(O) o (δ T).

  Definition clΔ T := (nchar_to_sub (clδ T)).

  Lemma equal_hfibers (A B:Type) (r:A=B) (f g:A -> B) e (p : f = equiv_path _ _ r) (q : g = equiv_path _ _ r)
  : {a:A & a = e} <~> {a:A & f a = g e}.

    exists (λ x:(∃ a : A, a = e), (x.1 ; (ap f x.2) @ (ap10 (p@q^) e))).
    destruct r.
    assert (f=idmap).
    apply path_forall; intro x. exact (ap10 p x).
    destruct p. destruct q.
    rewrite X. simpl.
    apply @isequiv_adjointify with  (g:= ( λ x, (x.1; x.2))).
    - intro x. simpl. hott_simpl.
    - intro x. simpl. hott_simpl. 
  Defined.
  
(* In modalities *)
  Definition O_invol_ : forall T, O nj T = (O nj) ( pr1 ((O nj) T))
    := λ T, (O_modal (O nj T)).

  Lemma OO_unit_idmap (T:Trunk n)
  : O_unit nj (O nj T).1 = equiv_path _ _ ((O_invol_ T)..1..1).
    unfold O_invol_. unfold O_modal.
    pose (rew := eissect _ (IsEquiv := isequiv_unique_subuniverse (O nj T) (O nj (O nj T) .1)) (truncn_unique fs (O nj T) .1 (O nj (O nj T) .1) .1
                                                                                                              (path_universe_uncurried
                                                                                                                 {|
                                                                                                                   equiv_fun := O_unit nj (O nj T) .1;
                                                                                                                   equiv_isequiv := O_modal_equiv (O nj T) |}))). 
    simpl in rew; rewrite rew; clear rew.

    pose (rew := eissect _ (IsEquiv := isequiv_truncn_unique (O nj T).1 (O nj (O nj T) .1).1) (path_universe_uncurried
                                                                                                 {|
                                                                                                   equiv_fun := O_unit nj (O nj T) .1;
                                                                                                   equiv_isequiv := O_modal_equiv (O nj T) |})). 
    simpl in rew. unfold pr1_path. rewrite rew; clear rew.
    unfold path_universe_uncurried. rewrite eisretr. simpl. exact 1.
  Defined.
(* End In modalities *)
        
  Lemma dicde_l (E:Type) (φ:E -> Trunk n) (A:={e:E & (φ e).1}) (clA := {e:E & (O nj (φ e)).1.1}) (e:clA)
  : (∃ rx : ((O nj (φ e .1)) .1) .1,
       rx =
      e.2) =(∃ rx : ((O nj (φ e .1)) .1) .1,
       O_rec (φ e .1) (O nj (O nj (φ e .1)) .1)
             (λ x : (φ e .1) .1,
                    O_unit nj (O nj (φ e .1)) .1 (O_unit nj (φ e .1) x)) rx =
       O_unit nj (O nj (φ e .1)) .1 e .2)
    .
    apply path_universe_uncurried.
    assert (foo := @equal_hfibers
                   ((O nj (φ e .1)).1.1)
                   ((O nj (O nj (φ e .1)) .1).1.1)
                   ((O_invol_ (φ e .1))..1..1)
                   (O_rec (φ e .1) (O nj (O nj (φ e .1)) .1)
                          (λ x : (φ e .1) .1, O_unit nj (O nj (φ e .1)) .1 (O_unit nj (φ e .1) x)))
                   (O_unit nj (O nj (φ e .1)) .1)
                   e.2). simpl in foo.
    apply foo. clear foo.
    - simpl.
      pose (bar := O_rec_sect (φ e .1) (O nj (O nj (φ e .1)) .1) (O_unit nj _)). unfold compose in bar. simpl in bar.
      unfold O_rec, compose; simpl.
      exact (bar @ OO_unit_idmap _).
    - apply OO_unit_idmap.
  Defined.
    
  Lemma dicde_ll
        (E : Type)
        (φ : E → Trunk n)
        (A := ∃ e : E, (φ e) .1 : Type)
        (clA := ∃ e : E, ((O nj (φ e)) .1) .1 : Type)
        (a : ∃ e : E, ((O nj (φ e)) .1) .1)
        (x : ∃ π : (φ a .1) .1, O_unit nj (φ a .1) π = a .2)
        (π : ∃ π : (φ a .1) .1, O_unit nj (φ a .1) π = a .2)
        (π' : ∃ π : (φ a .1) .1, O_unit nj (φ a .1) π = a .2)
  : equiv_path _ _ (dicde_l φ a) (a .2; 1) =
    (O_unit nj (φ a .1) π' .1;
     lex_compat_func (φ a .1) (O nj (φ a .1)) .1 (O_unit nj (φ a .1)) π').
    (* simpl. *)
    (* apply (moveR_transport_V idmap (dicde_l φ a)). *)
    unfold dicde_l.   
    unfold path_universe_uncurried.
    rewrite eisretr. simpl. hott_simpl.
    apply @path_sigma' with (p := π'.2^). simpl. destruct π' as [b p]. simpl. destruct p. simpl.
    unfold lex_compat_func. simpl.
    apply ap10_O_retr_sect.
  Defined.
    
  Lemma path_sigma_eta (A : Type) (P : A → Type) (u : ∃ x, P x)
  : path_sigma P u (u.1;u.2) 1 1 = (eta_sigma u)^.
  destruct u. simpl. exact 1.
  Defined.

  Lemma dense_into_cloture_dense_eq (E:Type) (φ:E -> Trunk n) (A:={e:E & (φ e).1}) (clA := {e:E & (O nj (φ e)).1.1})
  : is_dense_eq (λ e:clA, ({π : (φ e.1).1 & O_unit nj _ π = e.2} ; trunc_sigma (φ e .1) .2
              (λ a : (φ e .1) .1,
               istrunc_paths (trunc_succ (H:=(O nj (φ e.1)).1.2)) (O_unit nj (φ e .1) a) e .2))).
    intro e.
    assert (rew := ((islex_nj (φ e .1) (O nj (φ e .1)).1 (O_unit nj _) e.2) @ (dicde_l φ e)^)).
    (* path_via ((∃ rx : ((O nj (φ e .1)) .1) .1, rx = e .2)). *)
    apply path_universe_uncurried.
    apply (transport (λ U, (∃ e' : clA, e = e') <~> U) (islex_nj (φ e .1) (O nj (φ e .1)).1 (O_unit nj _) e.2)^).
    apply (transport (λ U, (∃ e' : clA, e = e') <~> U) (dicde_l φ e)).
    
    exists ((λ x:(∃ e' : clA, e = e'), existT (λ u, u = e.2) e.2 1)).
    apply @isequiv_adjointify with (g:= (λ x:(∃ rx : ((O nj (φ e .1)) .1) .1, rx = e .2), ((e.1;x.1); path_sigma _ e (e.1;x.1) 1 x.2^))).

    - intros [x p]. destruct p. exact 1.
    - intros [x p]. destruct p. simpl.
      apply @path_sigma' with (p := eta_sigma _).
      rewrite path_sigma_eta.
      simpl.
      reflexivity.
      
      (* pose (foo := trans_paths clA clA (λ _, e) idmap (e.1;e.2) e (eta_sigma e) (eta_sigma e)^). simpl in foo. *)
      (* etransitivity. exact foo. *)
      (* simpl. rewrite ap_idmap. *)
      (* rewrite concat_pp_p. *)
      (* rewrite concat_Vp. *)
      (* rewrite concat_p1. *)
      (* rewrite ap_const. hott_simpl. *)
  Defined.

  Lemma transport_equiv (A: Type) (f g:A -> Type) (x y: A) (p: x=y) (q: f x <~> g x)
  : transport (λ a:A, f a <~> g a) p q
    = (equiv_compose' (equiv_path _ _ (ap g p)) (equiv_compose' q (equiv_inverse (equiv_path _ _ (ap f p))))).
    path_induction.
    destruct q. apply equal_equiv. simpl. done.
  Defined.

  Lemma dense_into_cloture_dense_diag (E:Type) (φ:E -> Trunk n) (A:={e:E & (φ e).1}) (clA := {e:E & (O nj (φ e)).1.1})
  : is_dense_diag (dense_into_cloture_dense_eq φ).
    intros x p.
    unfold compose. unfold dense_into_cloture_dense_eq.
    apply path_forall; intro y.
    unfold path_universe_uncurried. rewrite eisretr.
    simpl.
    destruct x as [a x]. simpl in x. simpl in p. destruct p as [a' q]. destruct a' as [a' π]. simpl in q.
    destruct q. simpl.
    destruct y as [[a' π'] q]. simpl in *. destruct q. simpl in *.
    unfold incl_Aeq_Eeq. simpl.
    rewrite <- transport_pp.
    rewrite transport_equiv. simpl.
    rewrite ap_idmap.
    rewrite ap_const.
    unfold compose.
    simpl.
    (* rewrite inv_pp. *)
    rewrite transport_pp.

    pose (foo := lex_compat (φ a .1) (O nj (φ a .1)).1 (O_unit nj (φ a .1))). unfold compose, equiv_path in foo; simpl in foo.
    specialize (foo a.2 π'). simpl in foo.
    unfold hfiber in foo. simpl in foo.
    (* assert (bar := foo..1); simpl in bar. *)

    apply (moveR_transport_V idmap (islex_nj (φ a .1) (O nj (φ a .1)) .1 (O_unit nj (φ a .1)) a .2) (transport idmap (dicde_l φ a)  (a .2; 1))).

    apply (transport (λ U, transport idmap (dicde_l φ a) (a .2; 1) = U) foo^).
    clear foo.
    apply dicde_ll. exact π. exact π'.
  Qed.
  
  Definition dense_into_cloture (E:Type) (φ:E -> Trunk n) (A:={e:E & (φ e).1}) (clA := {e:E & (O nj (φ e)).1.1})
  : EnJ clA.
    refine (Build_EnJ (dense_into_cloture_dense_eq φ) _).
    apply dense_into_cloture_dense_diag.
  Defined.
End Sheafification.