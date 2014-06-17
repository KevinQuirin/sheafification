Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import equiv truncation univalence sub_object_classifier limit_colimit modalities.

Set Universe Polymorphism.
Global Set Primitive Projections.
Set Implicit Arguments.

Local Open Scope path_scope.
Local Open Scope equiv_scope.
Local Open Scope type_scope.

Context {univalence_axiom : Univalence}.
Context {funext : Funext}.

Arguments trunc_sigma {A} {P} {n} H H0: default implicits, simpl never.

Section Reflective_Subuniverse_base_case.
  
  Instance _j (P:HProp) : IsHProp (not (not (pr1 P))).
  repeat (apply trunc_forall; intro). Defined.

  Definition j (P:HProp) := (not (not (pr1 P));_j _).

  Instance _is_classical (P:HProp) : IsHProp (pr1 (j P) -> pr1 P).
  apply (@trunc_forall _ _ (fun _ => P.1)). intro. exact (pr2 P). Defined.  
  
  Definition is_classical (P:HProp) := (pr1 (j P) -> pr1 P ; _is_classical (P:=P)).

  Definition Oj (P:HProp) : {P : HProp & pr1 (is_classical P)}.
    exists (j P). exact (λ X X0, X (λ X1, X1 X0)). Defined.
    
  Definition Oj_unit (P:HProp) : pr1 P -> pr1 (pr1 (Oj P)) := fun x k => k x.

  Definition Oj_equiv (P : Trunc minus_one) (Q : {T : Trunc minus_one & pr1 (is_classical T)}) :
      (pr1 P -> pr1 (pr1 Q)) -> pr1 (pr1 (Oj P)) -> pr1 (pr1 Q).
    intros f jp. apply (pr2 Q). intro notQ. apply jp. intro p. exact (notQ (f p)). Defined.
  
  Definition subuniverse_Prop : subuniverse_struct minus_one.
  apply (Build_subuniverse_struct is_classical Oj Oj_unit). 
  intros. eapply log_equiv_is_equiv.
  apply (@trunc_forall _ _ (fun P => _)); intro. exact Q.1.2.
  apply (@trunc_forall _ _ (fun P => _)); intro. exact Q.1.2.
  exact (Oj_equiv _).
  Defined.  

End Reflective_Subuniverse_base_case.

(* induction step based on induction principle *)

Definition J :=
  pr1 (nchar_to_sub (pr1 (P:=_) o Oj)).
  (* {P : HProp & j (pr1 P)} *)

Definition Oj_J_Contr (χ:J) : Contr ((j χ.1).1).
  apply BuildContr with (center := χ.2).
  intro. apply allpath_hprop.
Defined.

Section Sheafification.

  Variable n0 : trunc_index.

  Definition n := trunc_S n0.

  Variable nj : subuniverse_struct n.

  Variable j_is_nj : forall P, (j P).1 = (nj.(O) (P.1; IsHProp_IsTrunc P.2 n0)).1.1.

  Variable j_is_nj_unit : forall P x ,
             transport idmap (j_is_nj P) (Oj_unit P x) = nj.(O_unit) (P.1; IsHProp_IsTrunc P.2 n0) x.

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
    apply (O_rec (((χ x))) (existT (fun T => (subuniverse_HProp nj T).1) (((φ1 x) .1) .1 → ((φ2 x) .1) .1 ; trunc_arrow (H0 := ((φ2 x) .1).2)) (subuniverse_arrow (((φ1 x) .1) .1) (φ2 x)))).
    intro v. simpl.

    assert (eq := (ap10 p (x;v))). unfold compose in eq; simpl in eq.
    exact (transport (λ U, U) (eq..1..1)).
    (* exact (transport (λ T:subuniverse_Type nj, (φ1 x).1.1 -> T.1.1) eq idmap). *)
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
     ((((φ2 x) .1) .1 → ((φ2 x) .1) .1; trunc_arrow);
     subuniverse_arrow ((φ2 x) .1) .1 (φ2 x))
     (λ (v : (χ x) .1) (x0 : ((φ2 x) .1) .1),
      transport idmap
        
           (ap10 p (x; v))..1..1
        (transport idmap
           
              (ap10 p (x; v))..1..1^ x0)) (EnJ_is_nJ χ x) y).

    apply (ap (λ u, O_rec (χ x)
     ((((φ2 x) .1) .1 → ((φ2 x) .1) .1; trunc_arrow);
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
    (* apply (ap_V (λ x1 : ∃ T : Trunc n, (subuniverse_HProp nj T) .1, (x1 .1) .1) (ap10 p (x; v))). *)
    
    apply (transport (λ U, O_rec (χ x)
                                 ((((φ2 x) .1) .1 → ((φ2 x) .1) .1; trunc_arrow);
                                  subuniverse_arrow ((φ2 x) .1) .1 (φ2 x))
                                 U
                                 (EnJ_is_nJ χ x) y = y) fooo^).
    clear fooo; simpl.
    pose (foo := ap10 (ap10 (O_rec_const (χ x) ((((φ2 x) .1) .1 → ((φ2 x) .1) .1; trunc_arrow);
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

      (* unfold compose in *; simpl in *. *)

      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_unique_subuniverse _ _))). apply isequiv_inverse.
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_truncn_unique _ _))). apply isequiv_inverse. 
      apply (@equiv_inj _ _ _ (isequiv_equiv_path ((φ1 o pr1) x).1.1 ((φ2 o pr1) x).1.1)).
      repeat rewrite eissect; rewrite eisretr; simpl.

      apply equal_equiv.
      unfold nTjTiseparated_eq_fun_univ, EnJ_is_nJ. 
      rewrite (witness_is_eta χ x). 
      etransitivity;
        try exact (ap10 (O_rec_retr (χ x.1) ((((φ1 x .1) .1) .1 → ((φ2 x .1) .1) .1; trunc_arrow); subuniverse_arrow ((φ1 x .1) .1) .1 (φ2 x .1)) (λ v : (χ x .1) .1, transport idmap ((ap10 p (x .1; v)) ..1) ..1)) x.2).
      repeat apply ap. destruct x as [x1 x2]. exact 1.
      
    - intro p; destruct p.
      unfold E_to_χ_map, nTjTiseparated_eq_inv in *; simpl in *.
      eapply concat; [idtac | apply (path_forall_1 φ1)]; apply ap.
      apply path_forall; intro x; simpl.
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_unique_subuniverse _ _))). apply isequiv_inverse.
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_truncn_unique _ _))). apply isequiv_inverse.
      apply (@equiv_inj _ _ _ (isequiv_equiv_path (((φ1 x) .1) .1) (((φ1 x) .1) .1))).
      repeat rewrite eissect; rewrite eisretr; simpl.
      unfold equiv_path. simpl.
      apply equal_equiv.
      unfold transport, nTjTiseparated_eq_fun_univ; simpl.
      exact (ap10 (O_rec_const  (χ x) ((((φ1 x) .1) .1 → ((φ1 x) .1) .1; trunc_arrow);
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
             
  Definition δ (T:Trunc (trunc_S n)) : ((pr1 T) * (pr1 T)) -> Trunc n.
    intro x. exists (fst x = snd x). apply istrunc_paths.
    exact T.2.
  Defined.

  Definition Δ T := (nchar_to_sub (δ T)).

  Definition clδ T := pr1  o nj.(O) o (δ T).

  Definition clΔ T := (nchar_to_sub (clδ T)).
  

  (**** from type to separated type ****)

  Definition separated_Type (T:Trunc (trunc_S n)) : Type :=
    Im (λ t : pr1 T, λ t', nj.(O) (t = t'; istrunc_paths (H:=pr2 T) (pr1 T) n t t')).

  Definition sheaf_is_separated (T : SnType_j_Type) : separated (pr1 T) := fst (T.2).
 
  Definition separated_Type_is_Trunc_Sn (T:Trunc (trunc_S n)) : IsTrunc (trunc_S n) (separated_Type T).
    unfold separated_Type; simpl.
    destruct T as [T TrT]; simpl in *.
    apply (@trunc_sigma _ (fun P => _)). 
    apply (@trunc_forall _ _ (fun P => _)). intro. 
    exact (@subuniverse_Type_is_TruncSn _ nj).
    intro φ. exact (IsHProp_IsTrunc (istrunc_truncation _ _) n). 
  Defined.

  Definition E_to_χ_map_ap (T U:Trunc (trunc_S n)) E (χ : EnJ E) (f : E -> (pr1 T))
             (g : pr1 T -> pr1 U) x y (e : x = y) : 
    ap (fun u => g o u) (ap (E_to_χ_map T χ) e) = ap (E_to_χ_map U χ) (ap (fun u => g o u) e).
    destruct e; reflexivity.
  Defined.

  Definition apf_Mono (T U:Type) (f: T -> U) (fMono : IsMonof f) X (x y : X -> T) (e e' : x = y) : 
    ap (fun u => f o u) e = ap (fun u => f o u) e' -> e = e'.
    intro. 
    rewrite <- (@eissect _ _ _ (fMono _ _ _) e). 
    rewrite <- (@eissect _ _ _ (fMono _ _ _) e'). exact (ap _ X0). 
  Defined.

  Instance separated_mono_is_separated_ (T U:Trunc (trunc_S n)) E χ g h (f: pr1 T -> pr1 U)
        (H:IsEquiv (ap (E_to_χ_map U (E:=E) χ) (x:=f o g) (y:=f o h))) (fMono : IsMonof f) : 
           IsEquiv (ap (E_to_χ_map T (E:=E) χ) (x:=g) (y:=h)).
  apply (isequiv_adjointify _ (fun X => @equiv_inv _ _ _ (fMono E g h) (@equiv_inv _ _ _ H (ap (fun u => f o u) X)))).
  - intro e. 
    apply (@apf_Mono _ _ _ fMono). 
    unfold equiv_inv.
    pose (E_to_χ_map_ap T U χ g f 
                        (@equiv_inv _ _ _ (fMono _ g h) (@equiv_inv _ _ _ H (ap (fun u => f o u) e)))).
    apply (transport (fun X => X = _) (inverse p)). clear p.
    eapply concat; try exact (@eisretr _ _ _ H (ap (fun u => f o u) e)). 
    apply ap. apply (@eisretr _ _ _ (fMono _ _ _)).
  - intro e. 
    pose (E_to_χ_map_ap T U χ g f e).
    apply (transport (fun X => equiv_inv (equiv_inv X) = _) (inverse p)).
    apply (transport (fun X => equiv_inv X = _) 
                     (inverse ((@eissect _ _ _ H (ap (fun u => f o u) e))))).
    apply eissect.
  Defined.

  Definition separated_mono_is_separated (T U:Trunc (trunc_S n)) (H:separated U) (f: pr1 T -> pr1 U)
             (fMono : IsMonof f) : separated T
 :=
    fun E χ x y => separated_mono_is_separated_ _ (H E χ (f o x) (f o y)) fMono.

  Definition T_nType_j_Type_trunc (T:Trunc (trunc_S n)) : IsTrunc (trunc_S n) (pr1 T -> subuniverse_Type nj).
    apply (@trunc_forall _ _ (fun P => _)). intro. 
    apply (@trunc_sigma _ (fun P => _)). apply Tn_is_TSn.
    intro. apply IsHProp_IsTrunc. exact (pr2 (subuniverse_HProp nj a0)).
  Defined.

  Definition T_nType_j_Type_isSheaf : forall T, Snsheaf_struct (pr1 T -> subuniverse_Type nj;
                                                    T_nType_j_Type_trunc T).
    intro.
    apply (dep_prod_SnType_j_Type (fun x:pr1 T => ((subuniverse_Type nj ; @subuniverse_Type_is_TruncSn _ nj);nType_j_Type_is_SnType_j_Type))).
  Defined.

  Definition T_nType_j_Type_sheaf T : SnType_j_Type :=  ((pr1 T -> subuniverse_Type nj; T_nType_j_Type_trunc T); T_nType_j_Type_isSheaf _).

  Definition separated_Type_is_separated (T:Trunc (trunc_S n)) : separated (separated_Type T; separated_Type_is_Trunc_Sn (T:=T)).
    apply (@separated_mono_is_separated
              (separated_Type T;separated_Type_is_Trunc_Sn (T:=T))
              (pr1 T -> subuniverse_Type nj; T_nType_j_Type_trunc T)
              (sheaf_is_separated (T_nType_j_Type_sheaf T))
              (pr1 )).
    rewrite IsMonof_isMono. intros x y. apply subset_is_subobject. intro.
    unfold squash. apply istrunc_truncation.
  Defined.

  Definition separation (T:Trunc (trunc_S n)) : {T : Trunc (trunc_S n) & separated T} :=
    ((separated_Type T ; separated_Type_is_Trunc_Sn (T:=T));separated_Type_is_separated (T:=T)).

  

  Definition separated_unit T :  pr1 T -> separated_Type T := toIm _.

  Definition kpsic_func_univ_func
             (T : Trunc (trunc_S n))
             (a : T .1)
             (b : T .1)
             (p : ((clδ T) (a, b)) .1)
             (Ωj := (T .1 → subuniverse_Type nj; T_nType_j_Type_trunc T)
                    : ∃ x, IsTrunc (trunc_S n) x)
             (inj := (pr1:separated_Type T → Ωj .1) : separated_Type T → Ωj .1)
             (X : IsMono inj)
             (t : T .1)
  : ((O nj (a = t; istrunc_paths (H:=T.2)T .1 n a t)) .1) .1 ->
    ((O nj (b = t; istrunc_paths (H:=T.2)  T .1 n b t)) .1) .1.
    apply O_rec; intro u.
    generalize dependent p; apply O_rec; intro v; apply O_unit.
    exact (v^@u).
  Defined.

  Definition kpsic_func_univ_inv
             (T : Trunc (trunc_S n))
             (a : T .1)
             (b : T .1)
             (p : ((clδ T) (a, b)) .1)
             (Ωj := (T .1 → subuniverse_Type nj; T_nType_j_Type_trunc T)
                    : ∃ x, IsTrunc (trunc_S n) x)
             (inj := (pr1:separated_Type T → Ωj .1) : separated_Type T → Ωj .1)
             (X : IsMono inj)
             (t : T .1)
  : ((O nj (b = t; istrunc_paths (H:=T.2)  T .1 n b t)) .1) .1 ->
    ((O nj (a = t; istrunc_paths (H:=T.2)T .1 n a t)) .1) .1 .
    apply O_rec; intro u.
    generalize dependent p; apply O_rec; intro v; apply O_unit.
    exact (v@u).
  Defined.

  Lemma O_rec_O_rec (A B C : Trunc n) f g x (H : forall b c, (f (g b c) c) = b)
  : O_rec A
          (O nj B)
          (λ u:A.1, O_rec C
                          (O nj B)
                          (λ v:C.1, O_unit nj B (f u v))
                          x)
          o (O_rec B
                 (O nj A)
                 (λ u:B.1, O_rec C
                                 (O nj A)
                                 (λ v:C.1, O_unit nj A (g u v))
                                 x)
                 ) = idmap.

    apply (equal_fun_modal B (O nj B)).
    unfold compose; simpl.
    apply path_forall; intro b.

    pose (eq := ap10 (O_rec_retr B (O nj A) (λ u : B .1, O_rec C (O nj A) (λ v : C .1, O_unit nj A (g u v)) x)) b); unfold compose in eq; simpl in eq.
    rewrite eq; clear eq.

    pose (eq := ap10 (reflect_factoriality_post C A (O nj B) (λ u : A .1, O_rec C (O nj B) (λ v : C .1, O_unit nj B (f u v)) x) (g b)) x); unfold compose, function_lift in eq; simpl in eq.
    rewrite eq; clear eq.

    assert ((λ x, 
            O_rec C (O nj B)
                  (λ x0 : C .1,
                          O_rec C (O nj B) (λ v : C .1, O_unit nj B (f (g b x0) v)) x) x) = (λ _, O_unit nj B b)).

    apply (@equiv_inj _ _ _ (O_equiv nj C (O nj B))).
    unfold compose; simpl.
    apply path_forall; intro c.
    pose (foo := ap10 (O_rec_retr C (O nj B) (λ x1 : C .1,
       O_rec C (O nj B) (λ v : C .1, O_unit nj B (f (g b x1) v))
         (O_unit nj C c))) c).
    unfold compose in foo; simpl in foo. rewrite foo; clear foo.
    pose (foo := ap10 (O_rec_retr C (O nj B) (λ v : C .1, O_unit nj B (f (g b c) v))) c).
    unfold compose in foo; simpl in foo. rewrite foo; clear foo.
    apply ap. exact (H b c).
    
    exact (ap10 X x).
  Qed.

  Lemma kpsic_func_univ_eq
        (T : Trunc (trunc_S n))
        (a : T .1)
        (b : T .1)
        (p : (clδ T (a, b)) .1)
        (Ωj := (T .1 → subuniverse_Type nj; T_nType_j_Type_trunc T)
               : ∃ x, IsTrunc (trunc_S n) x)
        (inj := (pr1:separated_Type T → Ωj .1) : separated_Type T → Ωj .1)
        (X : IsMono inj)
        (t : T .1)
  : (Sect (kpsic_func_univ_inv a b p X t) (kpsic_func_univ_func a b p X t))
    /\ (Sect (kpsic_func_univ_func a b p X t) (kpsic_func_univ_inv a b p X t)).
  (* : ((O nj (a = t; istrunc_paths (H:=T.2) T .1 n a t)) .1) .1 = ((O nj (b = t; istrunc_paths (H:=T.2) T .1 n b t)) .1) .1. *)
    (* apply univalence_axiom. *)
      (* exists (kpsic_func_univ_func a b p X t). *)
      (* apply isequiv_adjointify with (g := kpsic_func_univ_inv a b p X t). *)
    split.
    - intro x.
      unfold kpsic_func_univ_inv, kpsic_func_univ_func, δ; simpl. unfold clδ, compose, δ in p; simpl in p.
      pose (foo := O_rec_O_rec).
      specialize (foo (a = t; istrunc_paths (H := T.2) T .1 n a t)
                      (b = t; istrunc_paths (H := T.2) T .1 n b t)
                      (a = b; istrunc_paths (H := T.2) T .1 n a b)
                      (λ u v, v^@ u)
                      (λ u v, v @ u)
                      p
                 ); simpl in foo.
      
      refine (ap10 (f:= (O_rec (a = t; istrunc_paths T .1 n a t)
                               (O nj (b = t; istrunc_paths T .1 n b t))
                               (λ u : a = t,
                                      O_rec (a = b; istrunc_paths T .1 n a b)
                                            (O nj (b = t; istrunc_paths T .1 n b t))
                                            (λ v : a = b, O_unit nj (b = t; istrunc_paths T .1 n b t) (v ^ @ u))
                                            p)) 
                          o (O_rec (b = t; istrunc_paths T .1 n b t)
                                   (O nj (a = t; istrunc_paths T .1 n a t))
                                   (λ u : b = t,
                                          O_rec (a = b; istrunc_paths T .1 n a b)
                                                (O nj (a = t; istrunc_paths T .1 n a t))
                                                (λ v : a = b, O_unit nj (a = t; istrunc_paths T .1 n a t) (v @ u))
                                                p))) (g:=idmap) _ x).
      
      apply foo.
      intros q q'. destruct q. hott_simpl.
    - intro x. unfold kpsic_func_univ_inv, kpsic_func_univ_func, δ. simpl.
      pose (foo := O_rec_O_rec).
      specialize (foo (b = t; istrunc_paths (H := T.2) T .1 n b t)
                      (a = t; istrunc_paths (H := T.2) T .1 n a t)
                      (a = b; istrunc_paths (H := T.2) T .1 n a b)
                      (λ u v, v @ u)
                      (λ u v, v^ @ u)
                      p
                 ); simpl in foo.

      refine (ap10 (f:= (O_rec (b = t; istrunc_paths T .1 n b t)
                               (O nj (a = t; istrunc_paths T .1 n a t))
                               (λ u : b = t,
                                      O_rec (a = b; istrunc_paths T .1 n a b)
                                            (O nj (a = t; istrunc_paths T .1 n a t))
                                            (λ v : a = b, O_unit nj (a = t; istrunc_paths T .1 n a t) (v @ u))
                                            p)) 
                          o (O_rec (a = t; istrunc_paths T .1 n a t)
                                   (O nj (b = t; istrunc_paths T .1 n b t))
                                   (λ u : a = t,
                                          O_rec (a = b; istrunc_paths T .1 n a b)
                                                (O nj (b = t; istrunc_paths T .1 n b t))
                                                (λ v : a = b, O_unit nj (b = t; istrunc_paths T .1 n b t) (v ^ @ u))
                                                p))) (g:=idmap) _ x).
      apply foo.
      intros q q'. destruct q'. hott_simpl.
  Qed.

  Arguments kpsic_func_univ_eq : default implicits, simpl never.
        
  Definition kpsic_func T : (clΔ T) .1 -> kernel_pair (separated_unit T).
    intro X. destruct X as [ab p]. destruct ab as [a b]. simpl in p.
    pose (Ωj := (T.1 -> subuniverse_Type nj; T_nType_j_Type_trunc T)).
    pose (inj := pr1 : (separated_Type T) -> Ωj.1).
    assert (IsMono inj).
      intros x y. apply subset_is_subobject. intro.
      unfold squash. apply istrunc_truncation.
    unfold kernel_pair, pullback.
    exists a. exists b.
    assert (inj (separated_unit T a) = inj (separated_unit T b)).
      unfold inj, separated_unit. simpl.
      apply path_forall; intro t; simpl.
      apply unique_subuniverse; apply truncn_unique.
      unfold Oj; simpl.
      apply univalence_axiom.
      exists (kpsic_func_univ_func a b p X t).
      apply isequiv_adjointify with (g := kpsic_func_univ_inv a b p X t);
        [exact (fst (kpsic_func_univ_eq a b p X t)) | exact (snd (kpsic_func_univ_eq a b p X t))].
    exact (@equiv_inv _ _ _ (X (separated_unit T a) (separated_unit T b)) X0). 
  Defined.

  Definition kpsic_inv T : kernel_pair (separated_unit T) -> (clΔ T).1.
    unfold kernel_pair, separated_unit, clΔ, toIm, pullback. simpl.
      intro X0; destruct X0 as [a [b p]].
      exists (a,b).
      unfold clδ, δ, compose; simpl.
      pose (foo := (ap10 (projT1_path p) b)..1..1); unfold Oj, j in foo; simpl in foo.
      apply (transport idmap foo^).
      apply O_unit. exact 1.
  Defined.

  Lemma isequiv_eq_dep_subset {A:Type} {B:A -> Type} (X : ∀ a : A, IsHProp (B a)) (u v : {a:A & B a})
  : IsEquiv (eq_dep_subset X u v).
    apply @isequiv_adjointify with (g := λ p, ap pr1 p).
    - intro p. destruct p. simpl. unfold eq_dep_subset.
      destruct u as [a H]; simpl in *.
      assert (center (H=H) = 1).
        apply contr.
      apply (transport (λ u, path_sigma B (a;H) (a;H) 1 u = 1) X0^).
      exact 1.
    - intro p.
      destruct u as [u G], v as [v H].
      simpl in p; destruct p. unfold eq_dep_subset.
      pose (foo := @ap_existT). unfold path_sigma' in foo.
      rewrite <- foo.
      simpl.
      destruct (center (G=H)). simpl. exact 1.
  Defined.

  Definition equiv_VV (A B:Type) (f:A -> B) (H:IsEquiv f)
  : (f ^-1) ^-1 = f.
    hott_simpl.
  Defined.

  Definition moveR_EV (A B:Type) (f:A -> B) (IsEquiv:IsEquiv f) a b
  : a = f b -> (f ^-1) a = b.
    intro p.
    apply moveR_E. rewrite equiv_VV. exact p.
  Defined.

  Definition kpsic_aux1 (A B C D : Trunc n) f g h c d (p1:O nj A=O nj B) (p2:O nj B= O nj C) (p3:C=D)
  : O_rec A (O nj B) (λ v:A.1, O_unit nj B (f v)) (g (O_unit nj C c)) = h (O_unit nj D d).
    
    destruct p3. simpl.

   
  Admitted.
            

  Definition kernel_pair_separated_is_clΔ T : (clΔ T).1 =
    kernel_pair (toIm (λ t : pr1 T, λ t', nj.(O) (t = t'; istrunc_paths (H:=pr2 T) (pr1 T) n t t'))).
    apply univalence_axiom.
    exists (@kpsic_func T).
    apply isequiv_adjointify with (g := @kpsic_inv T).
    - intro X. unfold kpsic_inv. simpl.
      destruct X as [a [b p]]. 
      apply @path_sigma' with (p:=1).
      apply @path_sigma' with (p:=1).
      simpl.

     (*  pose (foo := @equiv_inj _ _ (eq_dep_subset (λ b0 : T .1 → (∃ T0 : Trunc n, (subuniverse_HProp nj T0) .1), *)
     (*  squash *)
     (*    (hfiber (λ t t' : T .1, O nj (t = t'; istrunc_paths (H:=T.2) T .1 n t t')) b0)) *)
     (* (λ a0 : T .1 → subuniverse_Type nj, *)
     (*  istrunc_truncation minus_one *)
     (*    (hfiber (λ t t' : T .1, O nj (t = t'; istrunc_paths (H:=T.2) T .1 n t t')) a0)) *)
     (* (truncation_incl (a; 1)) (truncation_incl (b; 1)))). simpl in foo. *)

      unfold separated_unit, toIm in p. simpl in p.

      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_eq_dep_subset
                                                     (λ a0 : T .1 → subuniverse_Type nj,
                                                             istrunc_truncation minus_one
                                                                                (hfiber (λ t t' : T .1, O nj (t = t'; istrunc_paths T .1 n t t')) a0))
                                                     (λ t' : T .1, O nj (a = t'; istrunc_paths T .1 n a t');
                                                      truncation_incl (a; 1))
                                                     (λ t' : T .1, O nj (b = t'; istrunc_paths T .1 n b t');
                                                      truncation_incl (b; 1))
            )));
      [apply isequiv_inverse | rewrite eissect].
      apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _));
        unfold path_forall; rewrite eisretr.
      apply path_forall; intro t.

      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_unique_subuniverse _ _)));
        [apply isequiv_inverse | rewrite eissect].
      
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_truncn_unique _ _)));
        [apply isequiv_inverse | rewrite eissect].

      simpl in *.

      apply (@equiv_inj _ _ _ (isequiv_equiv_path _ _)); rewrite eisretr.

      apply equal_equiv.
      unfold kpsic_func_univ_func, δ. simpl.

      apply (@equiv_inj _ _ _ (O_equiv nj (a = t; istrunc_paths T .1 n a t) (O nj (b = t; istrunc_paths T .1 n b t)))).
      rewrite (O_rec_retr).
      apply path_forall; intro u. simpl in *.

      unfold δ; simpl.
      unfold compose; simpl. destruct u.

      set (t1 := (transport idmap (((ap10 p ..1 b) ..1) ..1) ^
                  (O_unit nj (b = b; istrunc_paths T .1 n b b) 1))). simpl in t1.
      set (t2 := transport idmap (ap pr1 (apD10 p ..1 a) ..1)
                           (O_unit nj (a = a; istrunc_paths T .1 n a a) 1)). simpl in t2.

      assert (q1 := ap10 p..1 a); simpl in q1.
      assert (q2 := ap10 p..1 b); simpl in q2.
      assert (q3 : O nj (a = b; istrunc_paths (H:=T.2) T .1 n a b) = O nj (b = a; istrunc_paths (H:=T.2) T .1 n b a)).
        apply ap.
        apply truncn_unique. simpl.
        apply univalence_axiom.
        exists (λ p, p^). apply isequiv_adjointify with (g := λ p, p^); intro; hott_simpl.


      

      admit.
    - intro X. destruct X as [ab p]. destruct ab as [a b].
      (* unfold clδ, δ, compose in p. simpl in p. *)
      unfold kpsic_inv.
      apply @path_sigma' with (p:=1).
      rewrite transport_1.
      unfold clδ, δ, compose in *. simpl in p.
      apply moveR_transport_V.

      apply moveR_EV. symmetry.
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := (isequiv_equiv_path _ _)))).
  Admitted.

  Definition separated_equiv : forall (P : Trunc (trunc_S n)) (Q :{T : Trunc (trunc_S n) & separated T}),
                                 IsEquiv (fun f : separated_Type P -> pr1 (pr1 Q) =>
                                           f o (separated_unit P)).
  Abort.

  (**** From separated to sheaf ****)

  Definition closure_naturality_fun
             (E : Type)
             (F : Type)
             (A : Type)
             (m : A -> E)
             (Trm : forall b : E, IsTrunc n (hfiber m b))
             (Γ : F -> E)
  : {b : F & pr1 (pr1 (nj.(O) ( (hfiber m (Γ b) ; Trm (Γ b)))))} -> {b : F & hfiber (pr1 (P:=λ b0 : E, pr1 (cloture (nsub_to_char n (A; (m; Trm))) b0))) (Γ b)}
    := λ X, (pr1 X ; (((Γ (pr1 X) ; O_rec (hfiber m (Γ (pr1 X)); Trm (Γ (pr1 X)))
                        (nj.(O) (nsub_to_char n (A; (m; Trm)) (Γ (pr1 X))))
                        (λ Hb : pr1 (hfiber m (Γ (pr1 X)); Trm (Γ (pr1 X))),
                                nj.(O_unit) (nsub_to_char n (A; (m; Trm)) (Γ (pr1 X))) Hb) 
                        (pr2 X))) ; idpath)).

  Definition closure_naturality_inv
             (E : Type)
             (F : Type)
             (A : Type)
             (m : A -> E)
             (Trm : ∀ b : E, IsTrunc n (hfiber m b))
             (Γ : F -> E)
  : {b : F & hfiber (pr1 (P:=λ b0 : E, pr1 (cloture (nsub_to_char n (A; (m; Trm))) b0))) (Γ b)} -> {b : F & pr1 (pr1 (nj.(O) ( (hfiber m (Γ b) ; Trm (Γ b)))))}.
    intro X; exists (pr1 X).
    generalize (pr2 (pr1 (pr2 X))); apply O_rec; intro HHb; apply nj.(O_unit).
    destruct (pr2 (pr2 X)). exact HHb.
  Defined.

  Definition closure_naturality_retr
             (E : Type)
             (F : Type)
             (A : Type)
             (m : A -> E)
             (Trm : ∀ b : E, IsTrunc n (hfiber m b))
             (Γ : F -> E)
  : Sect (closure_naturality_inv Trm Γ) (closure_naturality_fun Trm Γ).
    intro X; unfold closure_naturality_fun, closure_naturality_inv; simpl.
    destruct X as [b Hb]; simpl.
    apply path_sigma' with (p := idpath); simpl.
    destruct Hb as [[b0 Hb0] eq]; simpl in *.
    destruct eq.

    pose (rew1 := ap10 (eissect _ (IsEquiv := (nj.(O_equiv) (nsub_to_char n (A; (m; Trm)) b0) (nj.(O) (existT (IsTrunc n) (hfiber m b0) (Trm b0))))) (λ x, x)) ( equiv_inv (IsEquiv := O_equiv nj (hfiber m b0; Trm b0)
                (O nj (nsub_to_char n (A; (m; Trm)) b0))) (λ t : hfiber m b0, O_unit nj (hfiber m b0; Trm b0) t) Hb0)).

    pose (rew2 := ap10 (eissect _ (IsEquiv := nj.(O_equiv) (hfiber m b0; Trm b0) (nj.(O) (nsub_to_char n (A; (m; Trm)) b0))) (λ x, x)) Hb0).

    unfold nsub_to_char, hfiber, compose in *; simpl in *.

    unfold O_rec; simpl.

    apply path_sigma' with (p := path_sigma' (λ x:E, (cloture (λ b : E, (∃ x : A, m x = b; Trm b)) x) .1) (@idpath _ b0) (rew1 @ rew2)).
    destruct (rew1 @ rew2); simpl. reflexivity.
  Defined.

  Definition closure_naturality_sect
             (E : Type)
             (F : Type)
             (A : Type)
             (m : A -> E)
             (Trm : ∀ b : E, IsTrunc n (hfiber m b))
             (Γ : F -> E)
  : Sect (closure_naturality_fun Trm Γ) (closure_naturality_inv Trm Γ).
    intro X; unfold closure_naturality_fun; simpl.
    destruct X as [b Hb]; simpl.
    apply @path_sigma' with (p := idpath); simpl.
    unfold O_rec.

    pose (rew1 := ap10 (eissect _ (IsEquiv := nj.(O_equiv) (hfiber m (Γ b); Trm (Γ b))
             (nj.(O) (nsub_to_char n (A; (m; Trm)) (Γ b)))) (λ x, x))
                         (equiv_inv (IsEquiv := O_equiv nj (nsub_to_char n (A; (m; Trm)) (Γ b))
          (O nj (hfiber m (Γ b); Trm (Γ b))))
        (λ Hb0 : hfiber m (Γ b),
         O_unit nj (nsub_to_char n (A; (m; Trm)) (Γ b)) Hb0) Hb)
         ).

    pose (rew2 := ap10 (eissect _ (IsEquiv := O_equiv nj (nsub_to_char n (A; (m; Trm)) (Γ b))
          (O nj (hfiber m (Γ b); Trm (Γ b)))) (λ x, x)) Hb).
    
    exact (rew1 @ rew2).
  Defined.

  Definition closure_naturality E F A (m : {f : A -> E & forall b:E, IsTrunc n (hfiber f b)}) (Γ : F -> E) :
    {b : F & pr1 (pr1 (nj.(O) ((hfiber (pr1 m) (Γ b)) ; (pr2 m) (Γ b))))} = {b : F & hfiber (pr1 (pr2 (cloture' m))) (Γ b)}.
    destruct m as [m Trm]; simpl.
    apply univalence_axiom.
    exists (closure_naturality_fun _ _).
    apply (isequiv_adjointify _ _ (closure_naturality_retr _ _) (closure_naturality_sect _ _)).
  Defined.

  Definition cloture_fun
        (E : Type)
        (P : E -> J)
        (Q : E -> Trunc n)
        (f : forall e:E, (P e).1.1 -> (Q e).1)
  : {e:E | (nj.(O) (pr1 (pr1 (P e)); IsHProp_IsTrunc (pr2 (pr1 (P e))) n0)).1.1} -> {e:E | (nj.(O) (Q e)).1.1}
    := (λ b, (pr1 b;
              O_rec (pr1 (pr1 (P (pr1 b))); IsHProp_IsTrunc (pr2 (pr1 (P (pr1 b)))) n0)
                    (nj.(O) (Q (pr1 b)))
                    (λ X2 : pr1 (pr1 (P (pr1 b))),
                            nj.(O_unit) (Q (pr1 b)) (f (b.1) X2))
                    (pr2 b))).
    
  Definition cloture_fun_restriction
        (E : Type)
        (P : E -> J)
        (Q : E -> Trunc n)
        (f : forall e:E, (P e).1.1 -> (Q e).1)
  :forall (e : {e:E | (P e).1.1}), pr2 (cloture_fun P Q f (pr1 e; nj.(O_unit) (pr1 (pr1 (P (pr1 e))); IsHProp_IsTrunc (pr2 (pr1 (P (pr1 e)))) n0) (pr2 e))) = nj.(O_unit) (Q (pr1 e)) ((f (pr1 e) (pr2 e)))
    := λ e, ap10 (eisretr _ (IsEquiv := (O_equiv nj (((P e .1) .1) .1; IsHProp_IsTrunc ((P e .1) .1) .2 n0) (O nj (Q e .1)))) (λ X, nj.(O_unit) _ (f _ X))) (e.2).

  Lemma cloture_fun_
        (E : Type)
        (P : E -> J)
        (Q : E -> Trunc n)
        (f : forall e:E, (P e).1.1 -> (Q e).1)
        (g : forall e:E, (nj.(O) (pr1 (pr1 (P e)); IsHProp_IsTrunc (pr2 (pr1 (P e))) n0)).1.1)
        (h : forall e:E, (Q e).1)
        (H : forall e:E, forall X:(P e).1.1, f e X = h e)
  : forall (e:E), pr2 (cloture_fun P Q f (e; g e)) = nj.(O_unit) (Q e) (h e).
    intro e.
    pose (foo := ap10 (eissect _ (IsEquiv := O_equiv nj (((P e) .1) .1; IsHProp_IsTrunc ((P e) .1) .2 n0)
          (O nj (Q e))) (λ _, O_unit nj (Q e) (h e))) (g e)); simpl in foo.
    assert ((λ X2 : ((P e) .1) .1, O_unit nj (Q e) (f e X2)) = (λ X2 : ((P e) .1) .1, O_unit nj (Q e) (h e))).
      apply path_forall; intro X2.
      rewrite <- H  with (X := X2).
      exact idpath.
    apply (transport _ foo).
    exact (ap10 (ap (equiv_inv (IsEquiv := O_equiv nj (((P e) .1) .1; IsHProp_IsTrunc ((P e) .1) .2 n0)
          (O nj (Q e)))) X) (g e)).
  Defined.

  Definition E_to_Y'A
             (A : Trunc (trunc_S n))
             (B : SnType_j_Type)
             (m : pr1 A -> pr1 (pr1 B))
             (X1 : ∀ b : pr1 (pr1 B), IsTrunc n (hfiber m b))
             (closed0 : closed' (m; X1))
             (E : Type)
             (χ : E -> J)
             (X : {b : E & pr1 ((pr1 (P:=λ b0 : HProp, ~ ~ pr1 b0) o χ) b)} -> pr1 A)
             (X0 : E)
             (inv_B : (pr1
                         (nchar_to_sub
                            (pr1
                               (P:=λ b : HProp,
                                         pr1 ((pr1 (P:=λ P : HProp, pr1 (is_classical P)) o Oj) b))
                               o χ)) -> pr1 (pr1 B)) -> E -> pr1 (pr1 B))
             (retr_B : Sect inv_B (E_to_χmono_map (pr1 B) (χ:=χ)))
             (Y := inv_B (m o X) : E -> pr1 (pr1 B))
    := (λ b, (pr1 b ; (X b ; (inverse (ap10 (retr_B (m o X)) b)))))  : {b : E & pr1 (pr1 (χ b))} -> {b : E & hfiber m (Y b)}.

  Definition clE_to_clY'A
             (A : Trunc (trunc_S n))
             (B : SnType_j_Type)
             (m : pr1 A -> pr1 (pr1 B))
             (X1 : ∀ b : pr1 (pr1 B), IsTrunc n (hfiber m b))
             (closed0 : closed' (m; X1))
             (E : Type)
             (χ : E -> J)
             (X : {b : E & pr1 ((pr1 (P:=λ b0 : HProp, ~ ~ pr1 b0) o χ) b)} -> pr1 A)
             (X0 : E)
             (inv_B : (pr1
                         (nchar_to_sub
                            (pr1
                               (P:=λ b : HProp,
                                         pr1 ((pr1 (P:=λ P : HProp, pr1 (is_classical P)) o Oj) b))
                               o χ)) -> pr1 (pr1 B)) -> E -> pr1 (pr1 B))
             (retr_B : Sect inv_B (E_to_χmono_map (pr1 B) (χ:=χ)))
             (Y := inv_B (m o X) : E -> pr1 (pr1 B))

    := cloture_fun χ (λ x, (hfiber m (Y x); X1 (Y x))) (λ e p, pr2 (E_to_Y'A _ _ closed0 _ X0 retr_B (e;p)))
:
         {b:E & pr1 (pr1 (nj.(O) (pr1 (pr1 (χ b)); IsHProp_IsTrunc (pr2 (pr1 (χ b))) n0)))} -> {b : E & pr1 (pr1 (nj.(O) (hfiber m (Y b) ; X1 (Y b))))}.

  Lemma equalpr2_restriction_χ
        (A : Trunc (trunc_S n))
        (B : SnType_j_Type)
        (m : pr1 A -> pr1 (pr1 B))
        (X1 : ∀ b : pr1 (pr1 B), IsTrunc n (hfiber m b))
        (closed0 : closed' (m; X1))
        (E : Type)
        (χ : E -> J)
        (X : {b : E & pr1 ((pr1 (P:=λ b0 : HProp, ~ ~ pr1 b0) o χ) b)} -> pr1 A)
        (X0 : E)
        (inv_B : (pr1
                    (nchar_to_sub
                       (pr1
                          (P:=λ b : HProp,
                                    pr1 ((pr1 (P:=λ P : HProp, pr1 (is_classical P)) o Oj) b))
                          o χ)) -> pr1 (pr1 B)) -> E -> pr1 (pr1 B))
        (retr_B : Sect inv_B (E_to_χmono_map (pr1 B) (χ:=χ)))
        (Y := inv_B (m o X) : E -> pr1 (pr1 B))
  : forall (b : {e : E & pr1 (pr1 (χ e))}), 
      pr2 (clE_to_clY'A _ _ closed0 _ X0 retr_B (pr1 b ; nj.(O_unit) (pr1 (pr1 (χ (pr1 b))); IsHProp_IsTrunc (pr2 (pr1 (χ (pr1 b)))) n0) (pr2 b))) = O_unit nj ({x : pr1 A & m x = Y (pr1 b)}; X1 (Y (pr1 b))) (pr2 (E_to_Y'A _ _ closed0 _ X0 retr_B b)).
  Proof.
    unfold clE_to_clY'A. intro b.
    pose (foo := cloture_fun_restriction χ (λ x, (hfiber m (Y x); X1 (Y x))) (λ e p, pr2 (E_to_Y'A _ _ closed0 _ X0 retr_B (e;p))) b).
    unfold Y, hfiber, compose in *.
    rewrite <- (eta_sigma (A:=E) (P:=λ x, ((χ x) .1) .1) b).
    apply foo.
  Defined.

  Lemma ap_equalf (A B C:Type) (x y : C -> B) (a : A) eq (φ : A -> C): (ap10 (ap (x:=x) (y:=y) (λ (f : C -> B), λ (t:A), f (φ t)) eq)) a = ap10 eq (φ a).
    destruct eq; simpl. exact idpath.
  Qed.
  
  Definition closed_to_sheaf_inv
             (A : Trunc (trunc_S n))
             (B : SnType_j_Type)
             (m : {f : pr1 A -> pr1 (pr1 B) & ∀ b : pr1 (pr1 B), IsTrunc n (hfiber f b)})
             (closed : closed' m)
             (E : Type)
             (χ : E -> J)
             (eq := snd (pr2 B) E χ)
  : ((nchar_to_sub (pr1 o χ)) .1 -> A .1) -> (E -> A .1).
    intros X X0.
    destruct (snd (pr2 B) E χ) as [inv_B retr_B sect_B adj_B].
    pose (X2:=pr2 (χ X0)). apply (transport idmap  (j_is_nj (((χ X0) .1)))) in X2.
    destruct (closed (inv_B ((pr1 m) o X) X0)) as [inv_closed retr_closed sect_closed adj_closed].
    
    exact ((pr1 (P:=_) o inv_closed) (pr2 (pr1 (pr2 (closure_naturality_fun _ _ (@clE_to_clY'A A B (pr1 m) (pr2 m) closed E χ X X0 inv_B retr_B (X0;X2))))))).
  Defined.

  Definition closed_to_sheaf_retr 
             (A : Trunc (trunc_S n))
             (B : SnType_j_Type)
             (m : {f : pr1 A -> pr1 (pr1 B) & ∀ b : pr1 (pr1 B), IsTrunc n (hfiber f b)})
             (closed : closed' m)
             (E : Type)
             (χ : E -> J)
             (eq := snd (pr2 B) E χ)

  : Sect (@closed_to_sheaf_inv A B m closed E χ) (E_to_χmono_map A (χ:=χ)).
    intro X.
    destruct m as [m Trm].
    apply path_forall; intro b.
    unfold closed_to_sheaf_inv, E_to_χmono_map, nsub_to_char, compose, hfiber, O_rec, Equivalences.internal_paths_rew in *; simpl in *.

    destruct (@snd (separated
            (@proj1_sig (Trunc (trunc_S n))
               (fun T : Trunc (trunc_S n) => Snsheaf_struct T) B)) (forall (E0 : Type) (χ0 : forall _ : E0, J),
          @IsEquiv
            (forall _ : E0,
             @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
               (@proj1_sig (Trunc (trunc_S n))
                  (fun T : Trunc (trunc_S n) => Snsheaf_struct T) B))
            (forall
               _ : @sig E0
                     (fun b0 : E0 =>
                      @proj1_sig Type
                        (fun T : Type => IsTrunc (trunc_S minus_two) T)
                        (@proj1_sig HProp
                           (fun b1 : HProp =>
                            not
                              (not
                                 (@proj1_sig Type
                                    (fun T : Type =>
                                     IsTrunc (trunc_S minus_two) T) b1)))
                           (χ0 b0))),
             @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
               (@proj1_sig (Trunc (trunc_S n))
                  (fun T : Trunc (trunc_S n) => Snsheaf_struct T) B))
            (fun
               (f : forall _ : E0,
                    @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
                      (@proj1_sig (Trunc (trunc_S n))
                         (fun T : Trunc (trunc_S n) => Snsheaf_struct T) B))
               (t : @sig E0
                      (fun b0 : E0 =>
                       @proj1_sig Type
                         (fun T : Type => IsTrunc (trunc_S minus_two) T)
                         (@proj1_sig HProp
                            (fun b1 : HProp =>
                             not
                               (not
                                  (@proj1_sig Type
                                     (fun T : Type =>
                                      IsTrunc (trunc_S minus_two) T) b1)))
                            (χ0 b0)))) =>
             f
               (@proj1_sig E0
                  (fun b0 : E0 =>
                   @proj1_sig Type
                     (fun T : Type => IsTrunc (trunc_S minus_two) T)
                     (@proj1_sig HProp
                        (fun b1 : HProp =>
                         not
                           (not
                              (@proj1_sig Type
                                 (fun T : Type =>
                                  IsTrunc (trunc_S minus_two) T) b1)))
                        (χ0 b0))) t))) (@projT2 (Trunc (trunc_S n))
         (fun T : Trunc (trunc_S n) => Snsheaf_struct T)
         B) E χ) as [inv_B retr_B sect_B adj_B].


    destruct (closed (inv_B (λ t : {b0 : E & pr1 (pr1 (P:= (λ b1:HProp, ~ ~ (pr1 b1))) (χ b0))}, m (X t)) (pr1 b))) as [inv_closed retr_closed sect_closed adj_closed].

    pose (rew1 := ap10 (eissect _ (IsEquiv :=
                                        nj.(O_equiv)
                                             ({x : pr1 A &
                                                   m x =
                                                   inv_B (λ t : {b0 : E & pr1 (pr1 (χ b0))}, m (X t)) (pr1 b)};
                Trm (inv_B (λ t : {b0 : E & pr1 (pr1 (χ b0))}, m (X t)) (pr1 b)))
                (nj.(O)
                   (nsub_to_char n (pr1 A; (m; Trm))
                                 (inv_B (λ t : {b0 : E & pr1 (pr1 (χ b0))}, m (X t))
                                        (pr1 b))))) (λ x, x))).
    unfold Sect, E_to_χ_map, nsub_to_char, hfiber, O_rec, compose in *; simpl in *.
    rewrite rew1; clear rew1.

    pose (foo := (@equalpr2_restriction_χ A B m Trm closed E χ X (pr1 b) inv_B retr_B b)).
    unfold clE_to_clY'A, E_to_Y'A, O_rec, hfiber, compose in foo; simpl in foo.
    unfold Sect, E_to_χ_map, nsub_to_char, hfiber, O_rec, compose in *; simpl in *.

    pose (bar := j_is_nj_unit ((χ b .1) .1) (b.2)).
    unfold Oj_unit, transport, Sect, E_to_χ_map, nsub_to_char, hfiber, O_rec, compose in *; simpl in *.
    
    assert ((λ k : ~ ((χ b .1) .1) .1, k b .2) = (χ b .1) .2).
      apply path_forall; intro x.
      destruct ((χ b .1) .2 x).

    assert (fooo := transport (λ x,  match j_is_nj (χ b .1) .1 in (_ = a) return a with
                                       | 1%path => x
                                     end =
                                     O_unit nj (((χ b .1) .1) .1; IsHProp_IsTrunc ((χ b .1) .1) .2 n0)
                                            b .2) X0 bar).
    simpl in fooo.
    rewrite <- fooo in foo.
    
    apply transport with (x := O_unit nj ({x : A .1 | m x = inv_B (λ t, m (X t)) b .1};
                                          Trm (inv_B (λ t : {b : E | ((χ b) .1) .1}, m (X t)) b .1))
                                      (X b; inverse (ap10 (retr_B (λ t, m (X t))) b)))
                         (y:=_).
   
    exact (inverse foo).
    rewrite sect_closed.
    exact idpath.
  Defined.

  Definition closed_to_sheaf_sect
             (A : Trunc (trunc_S n))
             (B : SnType_j_Type)
             (m : {f : pr1 A -> pr1 (pr1 B) & ∀ b : pr1 (pr1 B), IsTrunc n (hfiber f b)})
             (closed : closed' m)
             (E : Type)
             (χ : E -> J)
             (eq := snd (pr2 B) E χ)

  : Sect (E_to_χmono_map A (χ:=χ)) (@closed_to_sheaf_inv A B m closed E χ).
    destruct m as [m Trm].
    intro X; unfold closed_to_sheaf_inv; simpl in *.
    apply path_forall; intro b.
    unfold E_to_χmono_map, nsub_to_char, compose, hfiber, O_rec in *; simpl in *.
        destruct (@snd (separated
            (@proj1_sig (Trunc (trunc_S n))
               (fun T : Trunc (trunc_S n) => Snsheaf_struct T) B)) (forall (E0 : Type) (χ0 : forall _ : E0, J),
          @IsEquiv
            (forall _ : E0,
             @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
               (@proj1_sig (Trunc (trunc_S n))
                  (fun T : Trunc (trunc_S n) => Snsheaf_struct T) B))
            (forall
               _ : @sig E0
                     (fun b0 : E0 =>
                      @proj1_sig Type
                        (fun T : Type => IsTrunc (trunc_S minus_two) T)
                        (@proj1_sig HProp
                           (fun b1 : HProp =>
                            not
                              (not
                                 (@proj1_sig Type
                                    (fun T : Type =>
                                     IsTrunc (trunc_S minus_two) T) b1)))
                           (χ0 b0))),
             @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
               (@proj1_sig (Trunc (trunc_S n))
                  (fun T : Trunc (trunc_S n) => Snsheaf_struct T) B))
            (fun
               (f : forall _ : E0,
                    @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
                      (@proj1_sig (Trunc (trunc_S n))
                         (fun T : Trunc (trunc_S n) => Snsheaf_struct T) B))
               (t : @sig E0
                      (fun b0 : E0 =>
                       @proj1_sig Type
                         (fun T : Type => IsTrunc (trunc_S minus_two) T)
                         (@proj1_sig HProp
                            (fun b1 : HProp =>
                             not
                               (not
                                  (@proj1_sig Type
                                     (fun T : Type =>
                                      IsTrunc (trunc_S minus_two) T) b1)))
                            (χ0 b0)))) =>
             f
               (@proj1_sig E0
                  (fun b0 : E0 =>
                   @proj1_sig Type
                     (fun T : Type => IsTrunc (trunc_S minus_two) T)
                     (@proj1_sig HProp
                        (fun b1 : HProp =>
                         not
                           (not
                              (@proj1_sig Type
                                 (fun T : Type =>
                                  IsTrunc (trunc_S minus_two) T) b1)))
                        (χ0 b0))) t))) (@projT2 (Trunc (trunc_S n))
         (fun T : Trunc (trunc_S n) => Snsheaf_struct T)
         B) E χ) as [inv_B retr_B sect_B adj_B].
    destruct (closed (inv_B (λ t : {b0 : E & pr1 (pr1 (P:= (λ b1:HProp, ~ ~ (pr1 b1))) (χ b0))}, m (X (pr1 t))) b)) as [inv_closed retr_closed sect_closed adj_closed].

    rewrite (ap10 (eissect _ (IsEquiv :=
                             nj.(O_equiv)
                                  ({x : pr1 A &
                                        m x =
                                        inv_B (λ t : {b0 : E & pr1 (pr1 (χ b0))}, m (X (pr1 t))) b};
                                   Trm (inv_B (λ t : {b0 : E & pr1 (pr1 (χ b0))}, m (X (pr1 t))) b))
                                  (nj.(O)
                                        (nsub_to_char n (pr1 A; (m; Trm))
                      (inv_B (λ t : {b0 : E & pr1 (pr1 (χ b0))}, m (X (pr1 t)))
                         b)))) (λ x, x))).

    pose (foo := ap10 (sect_B (m o X))). 
    set (Y := inv_B (m o (X o pr1) ) : E -> pr1 (pr1 B)).

    apply transport with
      (x := O_unit nj ({x : A .1 | m x = Y b}; Trm (Y b)) (X b; inverse (foo b))) (y:=_).
  
    unfold E_to_χ_map, nsub_to_char, hfiber, O_rec, Y, compose in *; simpl in *.
   
    pose (h := (λ e, (X e; inverse (foo e))) : ∀ e : E, {x : A .1 | m x = inv_B (λ t : {b : E | ((χ b) .1) .1}, m (X t .1)) e}).
    assert ((∀ (e : E) (X0 : ((χ e) .1) .1),
          (X e;
           inverse
             (ap10 
                      (retr_B (λ t : {b : E | ((χ b) .1) .1}, m (X t .1)))
                      (e; X0))) = h e)).
      intros; unfold h, foo. apply path_sigma' with (p := idpath); simpl.
      apply ap.
      clear eq. specialize (adj_B (m o X)). unfold compose in adj_B.
      apply (transport (λ x:((λ (f : E -> (B .1) .1) (t : {b0 : E | ((χ b0) .1) .1}), f t .1)
         (inv_B (λ t : {b0 : E | ((χ b0) .1) .1}, m (X t .1))) =
       (λ t : {b0 : E | ((χ b0) .1) .1}, m (X t .1))), ((ap10  x (e; X0)) = (ap10  (sect_B (λ t : E, m (X t))) e))) (inverse adj_B)).
      clear adj_B.
      exact (@ap_equalf {b0 : E | ((χ b0) .1) .1} ((B .1) .1) E (inv_B (λ t : {b : E | ((χ b) .1) .1}, (λ t0 : E, m (X t0)) t .1)) (λ t : E, m (X t)) (e;X0) (sect_B (λ t : E, m (X t))) pr1).

    exact (inverse (@cloture_fun_ E χ (λ x, (hfiber m (Y x); Trm (Y x))) (λ e p, pr2 (E_to_Y'A _ _ closed _ b retr_B (e;p))) (λ b, match j_is_nj (χ b) .1 in (_ = y) return y with | 1%path => (χ b) .2 end) h X0 b)).
    
    rewrite sect_closed.
    exact idpath.
  Defined.

  Definition closed_to_sheaf (A:Trunc (trunc_S n)) (B:SnType_j_Type) (m : {f : (pr1 A) -> (pr1 (pr1 B)) & forall b, IsTrunc n (hfiber f b)})
  : closed' m  -> Snsheaf_struct A.
    intros x. split.
    - admit. (*TO DO*)
    - exact (λ E χ, isequiv_adjointify _ (@closed_to_sheaf_inv A B m x E χ) (@closed_to_sheaf_retr A B m x E χ) (@closed_to_sheaf_sect A B m x E χ)).
  Defined.


  Definition mono_is_hfiber (T U : Type) (m : T -> U) (Monom : IsMono m) :
    ∀ b , IsTrunc n (hfiber m b).
    intro. apply IsHProp_IsTrunc.
    apply (IsMono_IsHProp_fibers Monom).
  Defined.

  Definition separated_to_sheaf_Type (T U: Type) (m : T -> U) (Monom : IsMono m) : Type  :=
    pr1 (cloture' (m; mono_is_hfiber Monom)).    
  
  Definition separated_to_sheaf_IsTrunc_Sn (T U : Trunc (trunc_S n)) m Monom :
    IsTrunc (trunc_S n) (@separated_to_sheaf_Type T.1 U.1 m Monom).
    apply (@trunc_sigma _ (fun P => _)).
    exact (U.2).
    intro a.
    apply (@trunc_succ _ _).
    exact (pr2 (pr1 (nj.(O) (nsub_to_char n (T.1; (m ; mono_is_hfiber Monom)) a)))).
  Defined.
  
  Definition separated_to_sheaf (T:{T : Trunc (trunc_S n) & separated T}) (U:SnType_j_Type) m Monom :
     Snsheaf_struct (@separated_to_sheaf_Type T.1.1 U.1.1 m Monom; @separated_to_sheaf_IsTrunc_Sn _ _ m Monom).
    pose (foo := closed_to_sheaf (separated_to_sheaf_Type (m:=m) Monom; (@separated_to_sheaf_IsTrunc_Sn _ _ m  Monom)) U).
    unfold separated_to_sheaf_Type in *; simpl in *.

    specialize (foo (pr2 (cloture' (m;mono_is_hfiber Monom)))).
    apply foo.

    apply cloture_is_closed'.
  Defined.

  Definition IsMono_fromIm_inv {A B} (f : A -> B) (x y : Im f): x.1 = y.1 -> x=y.
    intro X.
    apply path_sigma with (p := X).
    apply allpath_hprop.
  Defined.
  
  Definition IsMono_fromIm {A B} (f : A -> B) : IsMono (fromIm (f:=f)). 
    intros x y; apply (isequiv_adjointify (ap (fromIm (f:=f))) (IsMono_fromIm_inv x y)).
    - intro a.
      destruct x as [x s]; destruct y as [y r]; simpl in *.
      destruct a; simpl in *.     unfold IsMono_fromIm_inv. simpl.
      destruct (allpath_hprop s r); simpl in *.
      reflexivity.
    - intro a.
      unfold IsMono_fromIm_inv, allpath_hprop, center.
      destruct a, x as [x s]; simpl.
      destruct (istrunc_truncation minus_one (hfiber f x) s s) as [center contr].
      rewrite (contr idpath); reflexivity.
  Defined.

  Definition sheafification_Type (T:Trunc (trunc_S n)) :=
    @separated_to_sheaf_Type (separated_Type T) 
                             (T.1 -> subuniverse_Type nj) (fromIm (f:=_)) 
                             (IsMono_fromIm (f:=_)).

  Definition sheafification_istrunc (T:Trunc (trunc_S n)) : 
    IsTrunc (trunc_S n) (sheafification_Type T).
    apply (separated_to_sheaf_IsTrunc_Sn (separated_Type T; separated_Type_is_Trunc_Sn (T:=T)) 
                              (T.1 -> subuniverse_Type nj; T_nType_j_Type_trunc T)).
  Defined.

  Definition sheafification_trunc (T:Trunc (trunc_S n)) : Trunc (trunc_S n) :=
    (sheafification_Type T ; sheafification_istrunc  (T:=T)). 

  Definition sheafification_ (T:Trunc (trunc_S n)) : Snsheaf_struct (sheafification_trunc T) :=
    separated_to_sheaf (separated_Type T; separated_Type_is_Trunc_Sn (T:=T)) (T_nType_j_Type_sheaf T) (IsMono_fromIm (f:=_)).

  Definition sheafification (T:Trunc (trunc_S n)) : SnType_j_Type :=
    ((sheafification_Type T ; sheafification_istrunc  (T:=T)); sheafification_ T).

  