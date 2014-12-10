Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import lemmas epi_mono equivalence univalence sub_object_classifier reflective_subuniverse modalities.
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

Section Definitions.

  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  Parameter n0 : trunc_index.

  Definition n := trunc_S n0.

  Parameter mod_nj : Modality n.

  Definition nj := underlying_subu n mod_nj.

  Parameter j_is_nj : forall P, (j P).1 = (nj.(O) (P.1; IsHProp_IsTrunc P.2 n0)).1.1.

  Parameter j_is_nj_unit : forall P x ,
                          transport idmap (j_is_nj P) (Oj_unit P x) = nj.(O_unit) (P.1; IsHProp_IsTrunc P.2 n0) x.

  
  Parameter islex_mod_nj : IsLex mod_nj.

  Definition islex_nj := islex_to_hfibers_preservation mod_nj islex_mod_nj.
  Definition lex_compat := islex_to_hfibers_preservation_compat mod_nj islex_mod_nj.
  
  
  Definition nJ := {T : Trunk n & (nj.(O) T).1.1}.

  Definition incl_Aeq_Eeq (E:Type) (χ:E -> Trunk n) (x:{e:E & (χ e).1})
  : {e':{e:E & (χ e).1} & x.1 = e'.1} -> {e':E & x.1 = e'}
    := λ X, (X.1.1;X.2).

  Definition eq_dense_1 (E:Type) (χ:E -> Trunk n) (x:{e:E & (χ e).1})
  : {e':{e:E & (χ e).1} & x.1 = e'.1} <~> (χ x.1).1.
    exists (λ X:(∃ e' : ∃ e : E, (χ e) .1, x .1 = e' .1), (transport (λ u, (χ u).1) (X.2)^ X.1.2)).
    apply isequiv_adjointify with (g := (λ X, ((x.1;X);1)) : ((χ x.1).1 -> {e':{e:E & (χ e).1} & x.1 = e'.1})).
    - intro u. reflexivity.
    - intro u. destruct u as [[e' e] p]. simpl in *. destruct p. simpl. reflexivity.
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
    destruct p. destruct q. simpl. reflexivity.
    rewrite (dense_eq χ) in X; apply X.
  Defined.

  Definition E_to_χmono_map (T:Trunk (trunc_S n)) E (χ : E -> J) (f : E -> (pr1 T)) : 
    (nchar_to_sub (pr1 o χ)).1 -> T.1 := f o pr1.

  Definition Snsheaf_struct T := (∀ E (χ : E -> J), IsEquiv (E_to_χmono_map T (E:=E) (χ:=χ))). 

  Definition SnType_j_Type := {T : Trunk (trunc_S n) & Snsheaf_struct T}.

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



  Lemma nType_j_Type_is_SnType_j_Type : Snsheaf_struct (existT (IsTrunc (n.+1)) (subuniverse_Type nj) (@subuniverse_Type_is_TrunkSn _ nj ua)).
  Proof.
    intros E χ. 
    exact (nTjTiSnTjT_eq _).
  Defined.


  Definition nType_j_Type_sheaf : SnType_j_Type :=
    ((existT (IsTrunc (n.+1)) (subuniverse_Type nj) (@subuniverse_Type_is_TrunkSn _ nj ua));nType_j_Type_is_SnType_j_Type).

  Instance dep_prod_SnType_j_Type_eq
           (A : Type)
           (B : A -> SnType_j_Type)
  : forall (E:Type) (χ : E -> J) (H := λ a, ((pr2 (B a))) E χ),
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
    (* unfold Sect, nchar_to_sub, compose, E_to_χ_map, compose in eissect. *)
    specialize (eissect (λ x, φ x a)).
    exact (ap10 eissect x).
  Defined.

  Definition dep_prod_SnType_j_Type : forall A (B : A -> SnType_j_Type) ,
                                        Snsheaf_struct (forall a, pr1 (pr1 (B a)); 
                                                        @trunc_forall _ A (fun a => pr1 (pr1 (B a))) (trunc_S n) (fun a => pr2 (pr1 (B a)))).
    intros. 
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
      
End Definitions.