Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import equiv truncation univalence sub_object_classifier limit_colimit modalities.
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
Arguments truncn_unique {n} A B H: simpl never.

Variable n0 : trunc_index.

Definition n := trunc_S n0.

Variable nj : subuniverse_struct n.

Variable j_is_nj : forall P, (j P).1 = (nj.(O) (P.1; IsHProp_IsTrunc P.2 n0)).1.1.

Variable j_is_nj_unit : forall P x ,
                          transport idmap (j_is_nj P) (Oj_unit P x) = nj.(O_unit) (P.1; IsHProp_IsTrunc P.2 n0) x.

Section Sheafification.


  Definition nJ := {T : Trunc n & (nj.(O) T).1.1}.

  Definition incl_Aeq_Eeq (E:Type) (χ:E -> Trunc n) (x:{e:E & (χ e).1})
  : {e':{e:E & (χ e).1} & x.1 = e'.1} -> {e':E & x.1 = e'}
    := λ X, (X.1.1;X.2).

  Definition eq_dense_1 (E:Type) (χ:E -> Trunc n) (x:{e:E & (χ e).1})
  : {e':{e:E & (χ e).1} & x.1 = e'.1} <~> (χ x.1).1.
    exists (λ X, (transport (λ u, (χ u).1) (X.2)^ X.1.2)).
    apply isequiv_adjointify with (g := (λ X, ((x.1;X);1)) : ((χ x.1).1 -> {e':{e:E & (χ e).1} & x.1 = e'.1})).
    - intro u. exact 1.
    - intro u. destruct u as [[e' e] p]. simpl in *. destruct p. simpl. exact 1.
  Defined.

  Definition is_dense_eq (E:Type) (char : E -> Trunc n) := forall e:E, ({e':E & e=e'}) = (O nj (char e)).1.1.

  Definition is_dense_diag (E:Type) (char : E -> Trunc n) (dense_eq : is_dense_eq char)
    := forall x:{e:E & (char e).1}, forall u:{e':{e:E & (char e).1} & x.1 = e'.1}, (equiv_path _ _ (dense_eq x.1)) o (incl_Aeq_Eeq char x) = (O_unit nj _) o ((eq_dense_1 char x)).

  Record EnJ (E:Type) :=
    {
      char :> E -> Trunc n ;
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

  Definition E_to_χmono_map (T:Trunc (trunc_S n)) E (χ : E -> J) (f : E -> (pr1 T)) : 
    (nchar_to_sub (pr1 o χ)).1 -> T.1 := f o pr1.

  Definition E_to_χ_map (T:Trunc (trunc_S n)) E (χ : EnJ E) (f : E -> (pr1 T)) : 
    (nchar_to_sub χ).1 -> T.1 := f o pr1.

  Definition separated T :=  ∀ E (χ : EnJ E), IsMono (E_to_χ_map T (E:=E) χ).
  
  Definition Snsheaf_struct T := (separated T) /\ (∀ E (χ : E -> J), IsEquiv (E_to_χmono_map T (E:=E) (χ:=χ))). 

  Definition SnType_j_Type := {T : Trunc (trunc_S n) & Snsheaf_struct T}.

  Definition separated_is_HProp T : IsHProp (separated T).
    repeat (apply trunc_forall).
  Defined.

  Definition Snsheaf_struct_is_HProp T : IsHProp (Snsheaf_struct T).
    apply trunc_prod.
  Defined.

  Definition nj_inter_f (A : Trunc n) (φ : A.1 -> Trunc n) : 
    (nj.(O) ({a:A.1 & (φ a).1}; trunc_sigma (A.2) (fun a => (φ a).2))).1.1 ->
    (nj.(O) ({a:A.1 & (nj.(O) (φ a)).1.1}; trunc_sigma (A.2) (fun a => (nj.(O) (φ a)).1.2))).1.1
    := function_lift
         nj
         ({a:A.1 & (φ a).1}; trunc_sigma (A.2) (fun a => (φ a).2))
         ({a:A.1 & (nj.(O) (φ a)).1.1}; trunc_sigma (A.2) (fun a => (nj.(O) (φ a)).1.2))
         (λ X, (X.1;nj.(O_unit) _ X.2)).

  Definition nj_inter_g (A : Trunc n) (φ : A.1 -> Trunc n) : 
    (nj.(O) ({a:A.1 & (nj.(O) (φ a)).1.1}; trunc_sigma (A.2) (fun a => (nj.(O) (φ a)).1.2))).1.1 ->
    (nj.(O) ({a:A.1 & (φ a).1}; trunc_sigma (A.2) (fun a => (φ a).2))).1.1.
    apply O_rec. intro X.
    generalize X.2. apply O_rec; intro φa.
    apply nj.(O_unit). exact (X.1;φa).
  Defined.

  Instance nj_inter_equiv (A : Trunc n) (φ : A.1 -> Trunc n) : IsEquiv (nj_inter_f A φ).
  apply (isequiv_adjointify _ (nj_inter_g A φ)).
  - intro x. unfold nj_inter_f, nj_inter_g. simpl in *.
    path_via (
        function_lift nj
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
      ).

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

    path_via (
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

  Definition nj_inter (A : Trunc n) (φ : A.1 -> Trunc n) : 
    nj.(O) ({a:A.1 & (φ a).1}; trunc_sigma (A.2) (fun a => (φ a).2)) =
    nj.(O) ({a:A.1 & (nj.(O) (φ a)).1.1}; trunc_sigma (A.2) (fun a => (nj.(O) (φ a)).1.2)).
    apply unique_subuniverse. apply truncn_unique.
    apply univalence_axiom. exact (BuildEquiv _ _ _ (nj_inter_equiv _ _)).
  Defined.

  Definition nj_fibers_compose A B C (f : A -> B) (g : B -> C) (c : C)
             (HB : ∀ b : B, IsTrunc n (hfiber f b)) (HC : ∀ c : C, IsTrunc n (hfiber g c))
  :
    nj.(O) (hfiber (g o f) c; function_trunc_compo n f g HB HC c) =
    nj.(O) ({ w :  hfiber g c &  (nj.(O) (hfiber f (pr1 w);(HB (pr1 w)))).1.1};
            trunc_sigma (HC c) (fun a => (O nj (hfiber f a .1; HB a .1)).1 .2)).
    assert ((hfiber (g o f) c; function_trunc_compo n f g HB HC c) =
            ({ w : (hfiber g c) & hfiber f (pr1 w) }; trunc_sigma (HC c) (fun w => HB w.1))).
    apply truncn_unique. apply fibers_composition.
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
    apply truncn_unique. apply (inter_symm (fun b => ((χ b) .1) .1) (fun b => ((φ b) .1) .1)).
    apply (transport (fun x => O nj x = _ ) (inverse X)). clear X.
    pose (X := (nj_fibers_compose x (λ e : {b : E | ((φ b) .1) .1},
                                           IsHProp_IsTrunc
                                             (nchar_to_sub_compat (λ t : {b : E | ((φ b) .1) .1}, (χ t .1) .1) e)
                                             n0) (nchar_to_sub_compat (λ t : E, (φ t) .1)))). unfold compose in X.
    apply (transport (fun x => x = _) (inverse X)). clear X.
    
    apply ap. apply truncn_unique. simpl. etransitivity.
    apply univalence_axiom. apply equiv_sigma_contr.
    intro. pose (f := j_is_nj (hfiber pr1 a .1; 
                               (nchar_to_sub_compat (λ t : {b : E | ((φ b) .1) .1}, (χ t .1) .1)
                                                    a .1))).
    apply (transport (fun X => Contr X) f).
    simpl.
    apply (transport (fun X => Contr (not (not X))) (inverse (nhfiber_pi1 _ _))).
    apply Oj_J_Contr.
    etransitivity. apply nhfiber_pi1. reflexivity.
  Defined.

  Definition nTjTiseparated_eq_fun_univ (E:Type) (χ:EnJ E) φ1 φ2
             (p: E_to_χ_map (subuniverse_Type nj; subuniverse_Type_is_TruncSn (subU:=nj)) χ φ1 =
                 E_to_χ_map (subuniverse_Type nj; subuniverse_Type_is_TruncSn (subU:=nj)) χ φ2)
             (x:E)
  :  ((φ1 x).1.1 -> (φ2 x).1.1).
    unfold E_to_χ_map in p.
    generalize dependent (EnJ_is_nJ χ x).
    apply (O_rec (((χ x))) (existT (fun T => (subuniverse_HProp nj T).1) (((φ1 x) .1) .1 → ((φ2 x) .1) .1 ; trunc_arrow ((φ2 x) .1).2) (subuniverse_arrow (((φ1 x) .1) .1) (φ2 x)))).
    intro v. simpl.

    assert (eq := (ap10 p (x;v))). unfold compose in eq; simpl in eq.
    exact (transport (λ U, U) (eq..1..1)).
  Defined.
  
  Lemma nTjTiseparated_eq_fun_univ_invol (E:Type) (χ:EnJ E) φ1 φ2 (p: E_to_χ_map
                                                                        (subuniverse_Type nj; subuniverse_Type_is_TruncSn (subU:=nj)) χ φ1 =
                                                                      E_to_χ_map
                                                                        (subuniverse_Type nj; subuniverse_Type_is_TruncSn (subU:=nj)) χ φ2) (x:E)
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

    pose (fooo := @transport_arrow_space_dep_path n nj (φ1 x) (φ2 x) (χ x) (λ v, (ap10 p (x;v))..1..1)).
    simpl in fooo.

    path_via (O_rec (χ x)
                    ((((φ2 x) .1) .1 → ((φ2 x) .1) .1; trunc_arrow ((φ2 x).1.2));
                     subuniverse_arrow ((φ2 x) .1) .1 (φ2 x))
                    (λ (v : (χ x) .1) (x0 : ((φ2 x) .1) .1),
                     transport idmap
                               
                               (ap10 p (x; v))..1..1
                               (transport idmap
                                          
                                          (ap10 p (x; v))..1..1^ x0)) (EnJ_is_nJ χ x) y).

    apply (ap (λ u, O_rec (χ x)
                          ((((φ2 x) .1) .1 → ((φ2 x) .1) .1; trunc_arrow ((φ2 x).1.2));
                           subuniverse_arrow ((φ2 x) .1) .1 (φ2 x))
                          u (EnJ_is_nJ χ x) y)).
    apply path_forall; intro v. apply path_forall; intro x0.
    apply ap. 
    apply (ap (λ U, transport idmap
                              U x0)).
    path_via ((ap10 p (x; v))^..1..1).
    apply ap. apply ap.
    apply (ap10_V p (x;v)).
    unfold projT1_path.
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
      (subuniverse_Type nj; subuniverse_Type_is_TruncSn (subU:=nj)) χ φ1 =
    E_to_χ_map 
      (subuniverse_Type nj; subuniverse_Type_is_TruncSn (subU:=nj)) χ φ2
    -> φ1 = φ2.
    intro p.
    simpl in *.
    unfold E_to_χ_map in p; simpl in p.
    apply path_forall; intro x.
    apply unique_subuniverse; apply truncn_unique.
    apply univalence_axiom.
    exists (nTjTiseparated_eq_fun_univ p x).
    apply isequiv_adjointify with (g := nTjTiseparated_eq_fun_univ (inverse p) x).
    - exact (nTjTiseparated_eq_fun_univ_invol p x).
    - exact (transport (λ u, ∀ y : ((φ1 x) .1) .1, nTjTiseparated_eq_fun_univ (inverse p) x (nTjTiseparated_eq_fun_univ u x y) = y) (inv_V p) (nTjTiseparated_eq_fun_univ_invol (inverse p) x)).
  Defined.

  Lemma nTjTiseparated_eq : separated (subuniverse_Type nj ; @subuniverse_Type_is_TruncSn _ nj).
    intros E χ φ1 φ2.
    apply isequiv_adjointify with (g := @nTjTiseparated_eq_inv E χ φ1 φ2).
    - intro p. 
      unfold E_to_χ_map in *; simpl in *.
      apply (@equiv_inj _ _ _ (isequiv_ap10 (φ1 o (pr1 (P:=fun e => (χ e).1))) (φ2 o pr1))).
      apply path_forall; intro x.

      unfold nTjTiseparated_eq_inv.
      rewrite ap_ap10_L. unfold ap10 at 1, path_forall; rewrite eisretr.

      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_unique_subuniverse _ _))). apply isequiv_inverse.
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_truncn_unique _ _))). apply isequiv_inverse. 
      apply (@equiv_inj _ _ _ (isequiv_equiv_path ((φ1 o pr1) x).1.1 ((φ2 o pr1) x).1.1)).
      repeat rewrite eissect.
      unfold univalence_axiom. rewrite eisretr.
      apply equal_equiv.
      unfold nTjTiseparated_eq_fun_univ, EnJ_is_nJ. 
      rewrite (witness_is_eta χ x). 
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
      repeat rewrite eissect. unfold univalence_axiom. rewrite eisretr; simpl.
      unfold equiv_path. simpl.
      apply equal_equiv.
      unfold transport, nTjTiseparated_eq_fun_univ; simpl.
      exact (ap10 (O_rec_const  (χ x) ((((φ1 x) .1) .1 → ((φ1 x) .1) .1; trunc_arrow ((φ1 x).1.2));
                                       subuniverse_arrow ((φ1 x) .1) .1 (φ1 x)) idmap) (EnJ_is_nJ χ x)). 
  Defined.

  Lemma nType_j_Type_is_SnType_j_Type : Snsheaf_struct (subuniverse_Type nj ;
                                                        @subuniverse_Type_is_TruncSn _ nj).
  Proof.
    split.
    apply nTjTiseparated_eq.
    intros E χ. unfold E_to_χ_map, compose; simpl.
    exact (nTjTiSnTjT_eq _).
  Defined.

  Definition nType_j_Type_sheaf : SnType_j_Type :=
    ((subuniverse_Type nj; @subuniverse_Type_is_TruncSn _ nj);nType_j_Type_is_SnType_j_Type).

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
    exact (equiv_inv (path_forall _ _ (λ t, apD10 ((apD10 H) t) a))).
  Defined.

  Lemma ap_path_forall (A B C:Type) (f:A -> B) (g h:B -> C) (eq:forall x, g x = h x)              
  : ap (λ u, u o f) (path_forall g h eq) = path_forall (g o f) (h o f) (λ x, (eq (f x))).
    apply (@equiv_inj _ _ _ (isequiv_ap10 _ _)).
    unfold ap10 at 2, path_forall at 2; rewrite eisretr.
    apply path_forall; intro a.
    rewrite ap_ap10_L.
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

      rewrite <- (@ap_ap10_L E
                             (((B a) .1) .1)
                             (∃ b : E, (χ b) .1)
                             (λ v, f v a)
                             (λ v, g v a)
                             pr1
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
      rewrite ap_ap10_L.
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

  Definition closed E (χ : E -> Trunc n) := forall e, IsEquiv (nj.(O_unit) (χ e)).
  
  Definition closed' E A (m : {f : A -> E & forall b:E, IsTrunc n (hfiber f b)}) := closed (nsub_to_char n (A;m)).

  Definition cloture E (χ : E -> Trunc n) : E -> Trunc n := pr1 o nj.(O) o χ.
  
  Definition cloture' E A (m : {f : A -> E & forall b:E, IsTrunc n (hfiber f b)}) :=
    nchar_to_sub (cloture (nsub_to_char n (A;m))).

  Definition cloture_is_closed (E :Type) (χ : E -> Trunc n) : closed (cloture χ).
    intro. apply O_modal_equiv.
  Defined.

  Lemma cloture_is_closed' (A:Type) (E:Type) (m : {f : A -> E & forall e:E, IsTrunc n (hfiber f e)}) : closed' (pr2 (cloture' m)).
    unfold closed', cloture'. 
    rewrite eta_sigma.
    pose (f := cloture_is_closed (nsub_to_char n (A; m))). 
    rewrite <- (@nsub_eq_char_retr n _ (cloture (nsub_to_char n (A; m)))) in f.
    exact f.
  Defined.
  
  Definition δ (T:Trunc (trunc_S n)) : T.1 * T.1-> Trunc n.
    intros x. exists (fst x = snd x). apply istrunc_paths.
    exact T.2.
  Defined.

  Definition ΔΣ (T:Trunc (trunc_S n)) := {a:T.1 & {b:T.1 & a = b}}.

  Definition Δ (T:Trunc (trunc_S n)) := nchar_to_sub (δ T).

  Lemma Δ_is_ΔΣ T : (ΔΣ T) = (Δ T).1 .
    unfold Δ, ΔΣ. simpl.
    pose (foo := (Δ T).2). simpl in foo.
    apply univalence_axiom.
    exists ((λ x, ((x.1, x.2.1);x.2.2)) : (∃ a b : T .1, a = b) -> (∃ b : T .1 ∧ T .1, fst b = snd b)).
    apply isequiv_adjointify with (g := (λ x, (fst x.1;(snd x.1;x.2))) : (∃ b : T .1 ∧ T .1, fst b = snd b) -> (∃ a b : T .1, a = b)).
    - intro x. destruct x as [[x y] z]. exact 1.
    - intro x. destruct x as [x [y z]]. exact 1.
  Defined.
  
  Definition clδ T := pr1  o nj.(O) o (δ T).

  Definition clΔ T := (nchar_to_sub (clδ T)).

  Definition clΔΣ (T: Trunc (trunc_S n)) := {a:T.1 & {b:T.1 & (O nj (a=b; istrunc_paths (T.2) a b)).1.1}}.

  Lemma clΔ_is_clΔΣ T : (clΔΣ T) = (clΔ T).1.
    unfold clΔΣ, clΔ, clδ, δ, compose. simpl.
    apply univalence_axiom.
    exists ((λ x, ((x.1, x.2.1);x.2.2)) : (∃ a b : T .1, ((O nj (a = b; istrunc_paths T .2 a b)) .1) .1) -> (∃ b : T .1 ∧ T .1, ((O nj (fst b = snd b; istrunc_paths T .2 (fst b) (snd b))) .1) .1)).
    apply isequiv_adjointify with (g := (λ x, (fst x.1;(snd x.1;x.2))) : (∃ b : T .1 ∧ T .1, ((O nj (fst b = snd b; istrunc_paths T .2 (fst b) (snd b))) .1) .1) -> (∃ a b : T .1, ((O nj (a = b; istrunc_paths T .2 a b)) .1) .1)).
    - intro x. destruct x as [[x y] z]. exact 1.
    - intro x. destruct x as [x [y z]]. exact 1.
  Defined.

  Lemma dense_into_cloture_dense_eq_trunc (E:Type) (φ:E -> Trunc n) (A:={e:E & (φ e).1}) (clA := {e:E & (O nj (φ e)).1.1}) (x:clA)
  : IsTrunc n {y : (φ x.1).1 & x.2 = O_unit nj _ y}.
    apply trunc_sigma.
    exact (φ x.1).2.
    intro a. apply istrunc_paths.
    apply @trunc_succ.
    exact (O nj (φ x.1)).1.2.
  Defined.

  Lemma sigma_sigma (A:Type) (B : A -> Type) (P : A -> Type) (Q : forall a:A, P a -> (B a) -> Type)
  : {x : {a:A & P a} & {b : (B x.1) & (Q x.1 x.2 b)}}
    = {x:A & {p : P x & {b : B x & Q x p b}}}.
    apply univalence_axiom.

    exists ((λ X, (X.1.1;(X.1.2;(X.2.1;X.2.2))))).
    apply isequiv_adjointify with (g := (λ X, ((X.1;X.2.1) ; (X.2.2.1;X.2.2.2))):((∃ (x : A) (p : P x) (b : B x), Q x p b) -> (∃ (x : ∃ a : A, P a) (b : B x .1), Q x .1 x .2 b))).
    - intro X.
      simpl. destruct X as [X s]. simpl. destruct s as [Y s]. simpl. destruct s. simpl. exact 1.
    - intro X.
      simpl. destruct X as [X s]. destruct X as [X Y], s as [s t]. simpl. exact 1.
  Qed.

  Lemma dense_into_cloture_dense_eq_eq (E:Type) (φ:E -> Trunc n) (A:={e:E & (φ e).1}) (clA := {e:E & (O nj (φ e)).1.1})
  : A = {x:clA & {π : (φ x.1).1 & x.2 = O_unit nj _ π}}.

    unfold clA.
    pose (foo := sigma_sigma).
    specialize (foo E (λ x, (φ x) .1) (λ e, ((O nj (φ e)) .1) .1)). simpl in foo.
    specialize (foo (λ a, λ p, λ q, p = O_unit nj _ q)). simpl in foo.
    rewrite foo; clear foo.
    
    apply univalence_axiom.

    exists ((λ x, (x.1; (O_unit nj _ x.2 ; (x.2 ; 1)))) : A -> (∃ (x : E) (p : ((O nj (φ x)) .1) .1) (b : (φ x) .1),
                                                                  p = O_unit nj (φ x) b)).

    apply isequiv_adjointify with (g := (λ x, (x.1 ; x.2.2.1)) : (∃ (x : E) (p : ((O nj (φ x)) .1) .1) (b : (φ x) .1), p = O_unit nj (φ x) b) -> A).

    (* exists ((λ x, ((x.1; O_unit nj _ x.2) ; (x.2; 1))): A -> (∃ (x : clA) (π : (φ x .1) .1), x .2 = O_unit nj (φ x .1) π)). *)
    (* apply isequiv_adjointify with (g := (λ x, (x.1.1; x.2.1)) : (∃ (x : clA) (π : (φ x .1) .1), x .2 = O_unit nj (φ x .1) π) -> A). *)
    - intro x. simpl.
      destruct x as [e [ca [p eq]]]; simpl in *.
      (* destruct x as [[e ca] [p eq]]. simpl in *. *)
      (* apply @path_sigma' with (p := path_sigma' (λ e, ((O nj (φ e)) .1) .1) 1 eq^). *)
      (* unfold path_sigma', path_sigma. unfold clA. rewrite transport_projT1_path_sigma_uncurried. *)

      
      
      apply @path_sigma' with (p:=1). simpl.
      apply @path_sigma' with (p:=eq^). simpl.

      rewrite transport_sigma'. simpl.
      apply @path_sigma' with (p:=1).
      simpl.
      destruct eq. exact 1.
    - intro X. destruct X as [X a]. exact 1.
  Qed.


  (* Lemma nj_sigma_func (X Y:Trunc n) f y *)
  (* : (O nj ({x:X.1 & f x = y} ; trunc_sigma X.2 (λ a, trunc_succ (H := istrunc_paths Y.2 _ _)))).1.1 -> {rx : (O nj X).1.1 & function_lift nj X Y f rx = O_unit nj _ y}. *)
  (*   intro x. simpl. *)
  (*   exists ((function_lift nj (∃ x : X .1, f x = y; trunc_sigma X .2 (λ a : X .1, trunc_succ)) X pr1) x). *)
  (*   pose (foo := ap10 (reflect_functoriality nj (∃ x0 : X .1, f x0 = y; trunc_sigma X .2 (λ a : X .1, trunc_succ (H:=istrunc_paths Y.2 _ _))) X Y f pr1) x). *)
  (*   etransitivity; try exact foo. *)
  (*   unfold function_lift. simpl in *. *)
  (*   apply (@ap10 _ _ _ (λ _, O_unit nj Y y)). *)
  (*   apply (@equiv_inj _ _ _ (O_equiv nj (∃ x0 : X .1, f x0 = y; trunc_sigma X .2 (λ a : X .1, trunc_succ)) *)
  (*    (O nj Y))). *)
  (*   rewrite O_rec_retr. unfold compose; simpl in *. *)
  (*   apply path_forall; intro u. apply ap. exact u.2. *)
  (* Defined. *)

  

  Lemma dense_into_cloture_dense_eq (E:Type) (φ:E -> Trunc n) (A:={e:E & (φ e).1}) (clA := {e:E & (O nj (φ e)).1.1})
  : is_dense_eq (λ x:clA, ({π : (φ x.1).1 & x.2 = O_unit nj _ π} ; @dense_into_cloture_dense_eq_trunc E φ x)).
    
  Admitted.

  Lemma dense_into_cloture_dense_diag (E:Type) (φ:E -> Trunc n) (A:={e:E & (φ e).1}) (clA := {e:E & (O nj (φ e)).1.1})
  : is_dense_diag (dense_into_cloture_dense_eq φ).
  Admitted.
  
  Definition dense_into_cloture (E:Type) (φ:E -> Trunc n) (A:={e:E & (φ e).1}) (clA := {e:E & (O nj (φ e)).1.1})
  : EnJ clA.
    refine (Build_EnJ (dense_into_cloture_dense_eq φ) _).
    apply dense_into_cloture_dense_diag.
  Defined.
End Sheafification.