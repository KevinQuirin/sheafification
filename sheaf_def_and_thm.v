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


Module Definitions (nj : subuniverse_struct) (mod : Modality nj).

  Export nj. Export mod.
  (* Module Import RS_Prop := Reflective_Subuniverse nj. *)
  Module Export Mod_Prop := Modality_theory nj mod.
  
  Definition ua := Mod_Prop.ua.
  Definition fs := Mod_Prop.fs.

  (* Import Reflective_subuniverse_base_case. *)

  Definition j := Reflective_Subuniverse_base_case.j.
  Definition Oj := Reflective_Subuniverse_base_case.O@{u a i' i}.
  Definition Oj_unit := Reflective_Subuniverse_base_case.O_unit@{u a i' i}.
  Definition Oj_equiv := Reflective_Subuniverse_base_case.O_equiv@{u a i' i j'}.

  (* Parameter n0 : trunc_index. *)

  (* Definition n := trunc_S n0. *)

  (* Parameter mod_nj : Modality n. *)

  (* Definition nj := underlying_subu n mod_nj. *)

  Set Printing Universes.
  
  Parameter j_is_nj : forall sf, forall P, (j P).1 = (O@{u a i' i} sf (P.1; IsHProp_IsTrunc P.2 n0)).1.

  Parameter j_is_nj_unit : forall sf, forall sfj, forall P x ,
                          transport idmap (j_is_nj@{u a i' i} sf P) (Oj_unit sfj P x) = (O_unit) sf (P.1; IsHProp_IsTrunc P.2 n0) x.

  
  (* Parameter islex_mod_nj : IsLex mod_nj. *)

  Definition islex_nj := islex_to_hfibers_preservation.
  Definition lex_compat := islex_to_hfibers_preservation_compat.
  
  (* Variable sf : subu_family. *)
  (* Definition sf := Mod_Prop.subU_RSProp.sf. *)
  (* Variable sfj : Reflective_Subuniverse_base_case.subu_family. *)
  
  (* Generalizable Variables sfj. *)
  
  Definition J :=
    pr1 (nchar_to_sub@{i' u i' i' i i'} (Oj@{u a i' i} tt)).
  (* {P : HProp & j (pr1 P)} *)

  Definition Oj_J_Contr (χ:J@{i' u i a}) : Contr ((j χ.1).1).
    apply BuildContr with (center := χ.2).
    intro. apply path_ishprop.
  Defined.

  
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

  Definition is_dense_eq (sf : subu_family) (E:Type@{i}) (char : E -> Trunk n) :=
    forall e:E, ({e':E & e=e'}) = (O@{u a i' i} sf (char e)).1.

  Definition is_dense_diag (sf : subu_family) (E:Type@{i}) (char : E -> Trunk n) (dense_eq : is_dense_eq@{i u a i'} sf char)
    := forall x:{e:E & (char e).1}, forall u:{e':{e:E & (char e).1} & x.1 = e'.1}, (equiv_path _ _ (dense_eq x.1)) o (incl_Aeq_Eeq char x) = (O_unit sf _) o ((eq_dense_1 char x)).

  Record EnJ (sf : subu_family) (E:Type@{i}) :=
    {
      char :> E -> Trunk@{i' i a} n ;
      dense_eq : forall e:E, ({e':E & e=e'}) = (O@{u a i' i} sf (char e)).1 ;
      dense_diag : forall x:{e:E & (char e).1}, forall u:{e':{e:E & (char e).1} & x.1 = e'.1}, (equiv_path _ _ (dense_eq x.1)) o (incl_Aeq_Eeq char x) = (O_unit sf _) o ((eq_dense_1 char x))
                                                                                                                                                                       (* For A a subobject of E, and x:A, this diagram commute : *)
                                                                                                                                                                       (*                                                         *)   
                                                                                                                                                                       (*   {e':A & x.1 = e'.1} === (χ x.1).1                     *)
                                                                                                                                                                       (*          |                    |                         *)
                                                                                                                                                                       (*        ι |                    | η                       *)
                                                                                                                                                                       (*          |                    |                         *)
                                                                                                                                                                       (*          v                    v                         *)
                                                                                                                                                                       (*    {e':E & x.1 = e'}  === (O sf (χ x.1)).1.1            *)
                                                                                                                                                                       
    }.

  Definition witness_is_eta (sf : subu_family) (E:Type@{i}) (χ:EnJ@{i i' a u} sf E) (x:{e:E & (χ e).1})
  : transport idmap (dense_eq χ x .1) (x .1; 1) = O_unit sf (χ x .1) x.2
    := ap10 (dense_diag χ x (x;1)) (x;1).

  Definition EnJ_is_nJ (sf : subu_family) (E:Type@{i}) (χ:EnJ@{i i' a u} sf E)
  : forall e:E, (O sf (χ e)).1
      := λ e, transport (λ T, T) (dense_eq χ e) (e;idpath).

  Definition dense_eta_equal (sf : subu_family) (E:Type@{i}) (χ:EnJ@{i i' a u} sf E)  (x:E) : forall (v w:(χ x).1), O_unit@{u a i' i} sf (χ x) v = O_unit sf (χ x) w.
    intros v w.
    assert (forall (a b:(∃ e' : E, x = e')), a=b).
    intros a b.
    destruct a as [a p], b as [b q]. simpl.
    apply @path_sigma' with (p := p^@q).
    destruct p. destruct q. simpl. reflexivity.
    rewrite (dense_eq χ) in X; apply X.
  Defined.

  Definition E_to_χmono_map (T:Trunk@{Si' u a} (trunc_S n)) (E:Type@{i}) (χ : E -> J@{i' u i a}) (f : E -> (pr1 T)) : 
    (nchar_to_sub (pr1 o χ)).1 -> T.1 := f o pr1.

  Definition E_to_χ_map (sf : subu_family) (T:Trunk@{Si' u a} (trunc_S n)) (E:Type@{i}) (χ : EnJ@{i i' a u} sf E) (f : E -> (pr1 T)) : 
    (nchar_to_sub χ).1 -> T.1 := f o pr1.
    
  Definition separated (sf : subu_family) (T: Trunk@{Si' u a} (n.+1)) :=  ∀ (E:Type@{i}) (χ : EnJ@{i i' a u} sf E), IsMono@{u u} (E_to_χ_map@{Si' u a i i'} T (E:=E) χ) : Type@{Si'}.
  
  Definition Snsheaf_struct (sf : subu_family) (T: Trunk@{Si' u a} (n.+1)) :=
    prod@{Si' Si'} (separated@{Si' u a i i'} sf T)
    (∀ (E:Type@{i}) (χ : E -> J@{i' u i a}),
       IsEquiv@{u u} (E_to_χmono_map@{Si' u a i i'} T χ)) : Type@{Si'}.
         
  Definition SnType_j_Type (sf : subu_family) := {T : Trunk@{Si' u a} (trunc_S n) & Snsheaf_struct@{Si' u a i i' } sf T}.

  Definition separated_is_HProp (sf : subu_family) T : IsHProp (separated sf T).
    repeat (apply trunc_forall).
  Defined.

  Definition Snsheaf_struct_is_HProp (sf : subu_family) T : IsHProp (Snsheaf_struct sf T).
    apply trunc_prod.
  Defined.

  (* If T is a n-Type, then if T is a n-sheaf, then T is also a (S n)-sheaf *)

  Definition lift_dep A (a:A) (P : A -> Type) : Lift A -> Type := P. 

  Axiom Lift_IsTrunc : forall n (T:Type@{x}), IsTrunc@{i} n T -> IsTrunc@{j} n T.
  
  Definition Lift_Trunk : forall n, Trunk@{i' i a} n -> Trunk@{i' j a} n :=
    fun n T => existT (IsTrunc n) T.1 (Lift_IsTrunc n _ T.2).
  
  Lemma nsheaf_to_Snsheaf (sf : subu_family) (T: Trunk@{Si' i a} (n.+1)) (Trn : IsTrunc n T.1)
        (nsheaf : (subuniverse_HProp@{u a i' i} sf (T.1;Trn)).1) : Snsheaf_struct@{Si' u a i i'} sf (Lift_Trunk T).
    split.
    { intros E χ u v.
      refine (isequiv_adjointify _ _ _ _).
      - unfold E_to_χ_map; simpl; intro p.
        apply path_forall; intro x.
        (* apply (@equiv_inj _ _ _ (O_modal_equiv ((T.1;Trn);nsheaf))). simpl. *)
        destruct χ as [χ χeq χdiag]. simpl in *.
        pose proof (transport idmap (χeq x) (x;1)). simpl in X.
        revert X.
        transparent assert (modal_family : (subuniverse_Type sf)).
        { refine (exist _ _ _).
          refine (exist _ (u x = v x) (istrunc_paths (trunc_succ Trn) (u x) (v x))).
          pose subuniverse_paths.
          transparent assert (sheaf : (subuniverse_Type sf)).
          refine (exist _ (T.1;Trn) nsheaf).
          specialize (p0 sf ((T.1;Trn);nsheaf) (u x) (v x)). simpl in p0.
          (* assert (istrunc_paths (trunc_succ Trn) (u x) (v x) = istrunc_paths T.2 (u x) (v x)) by apply path_ishprop. *)
          (* rewrite X in p0. *)
          exact p0. }
        apply (O_rec sf (χ x) modal_family.1 modal_family.2); unfold modal_family; clear modal_family.
        intro xx; simpl.
        exact (ap10 p (x;xx)).
      - intro p. simpl. unfold E_to_χ_map in *; simpl in *.
        apply (@equiv_inj _ _ _ (isequiv_ap10 _ _)).
        apply path_forall; intro x.
        rewrite ap10_ap_precompose.
        unfold ap10 at 1, path_forall at 1; rewrite eisretr. simpl.
        destruct χ as [χ χeq χdiag]. simpl in *.
        specialize (χdiag x (x;1)).
        unfold incl_Aeq_Eeq in χdiag.
        apply ap10 in χdiag.
        specialize (χdiag (x;1)). simpl in χdiag.
        rewrite χdiag.
        match goal with
          |[|- O_rec _ _ ?X ?Y _ _ = _] => set (sheaf_type := X); set (sheaf_sheaf := Y) end.
        exact (ap10 (O_rec_retr sf (χ x.1) sheaf_type sheaf_sheaf (λ xx : (χ x.1).1, ap10 p (x.1; xx))) x.2). 
      - intro p. destruct p. simpl.
        match goal with
          |[|- path_forall u u ?X = _] => assert (X=(λ _, 1)) end.
        { apply path_forall; intro x. rewrite O_rec_const. reflexivity. }
        rewrite X. apply path_forall_1. }
    { intros E χ. 
      refine (isequiv_adjointify _ _ _ _); simpl.
      - intros f x.
        unfold J in χ; simpl in *.
        assert (p := transport idmap (j_is_nj sf (χ x).1) (χ x).2).
        revert p. simpl. apply (O_rec sf _ (T.1;Trn) nsheaf).
        intros xx. simpl in *.
        exact (f (x;xx)).
      - intro f. apply path_forall; intro x; simpl in *.
        unfold E_to_χmono_map; simpl.
        assert ((χ x.1).2 = (Oj_unit tt (χ x.1).1 x.2)) by apply path_ishprop.
        rewrite X.
        path_via (O_rec sf (((χ x.1).1).1; IsHProp_IsTrunc ((χ x.1).1).2 n0)
                        (T.1; Trn) nsheaf (λ xx : ((χ x.1).1).1, f (x.1; xx)) (O_unit sf
                                                                                         (((χ x.1).1).1; IsHProp_IsTrunc ((χ x.1).1).2 n0)
                                                                                         x.2)).
        apply ap. exact (j_is_nj_unit sf tt (χ x.1).1 x.2).
        exact (ap10@{i i i} (O_rec_retr@{u a i' i} sf (((χ x.1).1).1; IsHProp_IsTrunc ((χ x.1).1).2 n0)
                                (T.1; Trn) nsheaf
                                (λ xx : ((χ x.1).1).1, f (x.1; xx))) x.2).
      - intro f.
        apply path_forall; intro x.
        assert (p := transport idmap (j_is_nj sf (χ x).1) (χ x).2).
        revert p. simpl.
        transparent assert (sheaf : (subuniverse_Type sf)).
        { refine (exist _ _ _).
          exists (O_rec sf (((χ x).1).1; IsHProp_IsTrunc ((χ x).1).2 n0)
                               (T.1; Trn) nsheaf (λ xx : ((χ x).1).1, E_to_χmono_map (Lift_Trunk T) _ f (x; xx))
                               (transport idmap (j_is_nj sf (χ x).1) (χ x).2) = 
                         f x).
          apply istrunc_paths. exact (trunc_succ Trn).
          exact (subuniverse_paths ((T.1;Trn);nsheaf)
                                  (O_rec sf (((χ x).1).1; IsHProp_IsTrunc ((χ x).1).2 n0)
                                         (T.1; Trn) nsheaf
                                         (λ xx : ((χ x).1).1, E_to_χmono_map (Lift_Trunk T) _ f (x; xx))
                                         (transport idmap (j_is_nj sf (χ x).1) (χ x).2))
                                  (f x)). }
          
        apply (O_rec sf _ sheaf.1 sheaf.2).
        unfold sheaf; clear sheaf. simpl. intro xx.
        pose (j_is_nj_unit sf tt (χ x).1 xx).
        assert ((χ x).2 = (Oj_unit tt (χ x).1 xx)) by apply path_ishprop.
        rewrite X.
        path_via (O_rec sf (((χ x).1).1; IsHProp_IsTrunc ((χ x).1).2 n0)
     (T.1; Trn) nsheaf (λ xx0 : ((χ x).1).1, E_to_χmono_map (Lift_Trunk T) _ f (x; xx0))
     (O_unit sf
             (((χ x).1).1; IsHProp_IsTrunc ((χ x).1).2 n0) xx)).
        apply ap; exact p.
        exact (ap10 (O_rec_retr sf (((χ x).1).1; IsHProp_IsTrunc ((χ x).1).2 n0) (T.1; Trn) nsheaf (λ xx0 : ((χ x).1).1, E_to_χmono_map (Lift_Trunk T) _ f (x; xx0))) xx). }
  Defined.

  Definition nj_inter_f (sf : subu_family@{u a}) (A : Trunk@{i' i a} n) (φ : A.1 -> Trunk@{i' i a} n) : 
    (O@{u a i' i} sf ({a:A.1 & (φ a).1}; trunc_sigma (A.2) (fun a => (φ a).2))).1 ->
    (O@{u a i' i} sf ({a:A.1 & (O sf (φ a)).1}; trunc_sigma (A.2) (fun a => (O sf (φ a)).2))).1
    := function_lift sf
         
         ({a:A.1 & (φ a).1}; trunc_sigma (A.2) (fun a => (φ a).2))
         ({a:A.1 & (O sf (φ a)).1}; trunc_sigma (A.2) (fun a => (O sf (φ a)).2))
         (λ X, (X.1;sf.(O_unit) _ X.2)).

  Definition nj_inter_g (sf : subu_family@{u a}) (A : Trunk@{i' i a} n) (φ : A.1 -> Trunk@{i' i a} n) : 
    (O@{u a i' i} sf ({a:A.1 & (O sf (φ a)).1}; trunc_sigma (A.2) (fun a => (O sf (φ a)).2))).1 ->
    (O@{u a i' i} sf ({a:A.1 & (φ a).1}; trunc_sigma (A.2) (fun a => (φ a).2))).1.
    apply O_rec; [apply subuniverse_O | intro X].
    generalize X.2. apply O_rec; [apply subuniverse_O | intro φa].
    apply sf.(O_unit). exact (X.1;φa).
  Defined.

  Instance nj_inter_equiv (sf : subu_family) (A : Trunk@{i' i a} n) (φ : A.1 -> Trunk@{i' i a} n) : IsEquiv (nj_inter_f@{u a i' i} sf A φ).
  apply (isequiv_adjointify _ (nj_inter_g sf A φ)).
  - intro x. unfold nj_inter_f, nj_inter_g. simpl in *.
    transitivity (function_lift sf                       (∃ a0 : A .1, (φ a0) .1;
                       trunc_sigma A .2 (λ a0 : A .1, (φ a0) .2))
                      (∃ a0 : A .1, ((O sf (φ a0)) .1);
                       trunc_sigma  
                         A .2 (λ a0 : A .1, ((O sf (φ a0))) .2))
                      (λ X : ∃ a0 : A .1, (φ a0) .1, (X .1; O_unit sf (φ X .1) X .2))
                      (O_rec sf
                         (∃ a0 : A .1, ((O sf (φ a0)) .1);
                          trunc_sigma  
                            A .2 (λ a0 : A .1, ((O sf (φ a0))) .2))
                         (O sf
                            (∃ a0 : A .1, (φ a0) .1;
                             trunc_sigma  A .2
                                          (λ a0 : A .1, (φ a0) .2)))
                         (subuniverse_O sf _)
                         (λ X : ∃ a0 : A .1, ((O sf (φ a0)) .1) ,
                            (function_lift sf (φ X.1) (∃ a0 : A .1, (φ a0) .1;
                                                       trunc_sigma  
                                                         A .2 (λ a0 : A .1, (φ a0) .2)) (λ b, (X.1;b)))
                              X .2) x)
      ); auto with path_hints.

    pose (foo := ap10 (reflect_factoriality_pre sf
                         (∃ a0 : A .1, ((O sf (φ a0)) .1);
                          trunc_sigma  
                            A .2 (λ a0 : A .1, ((O sf (φ a0))) .2))
                         (((O sf
                              (∃ a0 : A .1, (φ a0) .1;
                               trunc_sigma A .2
                                           (λ a0 : A .1, (φ a0) .2)))))
                         (((O sf
                              (∃ a0 : A .1, ((O sf (φ a0)) .1);
                               trunc_sigma 
                                 A .2 (λ a0 : A .1, ((O sf (φ a0))) .2)))))
                         (subuniverse_O sf _)
                         (subuniverse_O sf _)
                         (function_lift sf (∃ a0 : A .1, (φ a0) .1;
                                         trunc_sigma  A .2 (λ a0 : A .1, (φ a0) .2))
                                        (∃ a0 : A .1, ((O sf (φ a0)) .1);
                                         trunc_sigma 
                                           A .2 (λ a0 : A .1, ((O sf (φ a0))) .2))
                                        (λ X : ∃ a0 : A .1, (φ a0) .1, (X .1; O_unit sf (φ X .1) X .2)))
                         ((λ X : ∃ a0 : A .1, ((O sf (φ a0)) .1),
                             function_lift sf (φ X .1)
                                           (∃ a0 : A .1, (φ a0) .1;
                                            trunc_sigma  A .2
                                                         (λ a0 : A .1, (φ a0) .2)) (λ b : (φ X .1) .1, (X .1; b)) 
                                           X .2))) x
         ). 
    etransitivity; try exact foo. clear foo.

    transitivity (
        O_rec sf
          (∃ a0 : A .1, ((O sf (φ a0)) .1);
           trunc_sigma 
             A .2 (λ a0 : A .1, ((O sf (φ a0))) .2))
          (O sf
             (∃ a0 : A .1, ((O sf (φ a0)) .1) ;
              trunc_sigma 
                A .2 (λ a0 : A .1, ((O sf (φ a0))) .2)))
          (subuniverse_O sf _)
          (λ x0 : ∃ a0 : A .1, ((O sf (φ a0)) .1),
             function_lift sf (φ x0 .1)
                           (∃ a0 : A .1, ((O sf (φ a0)) .1);
                            trunc_sigma
                              A .2 (λ a0 : A .1, ((O sf (φ a0))) .2))
                           (λ x : (φ x0 .1) .1, (x0 .1; O_unit sf (φ x0 .1) x)) 
                           x0 .2) x
      ).
    apply (ap (λ u, O_rec sf
                      (∃ a0 : A .1, ((O sf (φ a0)) .1);
                       trunc_sigma 
                         A .2 (λ a0 : A .1, ((O sf (φ a0)) ) .2))
                      (O sf
                         (∃ a0 : A .1, ((O sf (φ a0)) .1);
                          trunc_sigma 
                            A .2 (λ a0 : A .1, ((O sf (φ a0))) .2)))
                      (subuniverse_O sf _)
                      u x)).
    apply path_forall; intro x0.
    exact (ap10 (reflect_functoriality
                   sf
                   (φ x0 .1)
                   (∃ a0 : A .1, (φ a0) .1;
                    trunc_sigma A .2
                                (λ a0 : A .1, (φ a0) .2))
                   (∃ a0 : A .1, ((O sf (φ a0)) .1);
                    trunc_sigma
                      A .2 (λ a0 : A .1, ((O sf (φ a0))) .2))
                   (λ X : ∃ a0 : A .1, (φ a0) .1, (X .1; O_unit sf (φ X .1) X .2))
                   (λ b : (φ x0 .1) .1, (x0 .1; b))) x0.2
          ).
    exact (ap10 (O_rec_O_rec_dep_sect sf
                                      (∃ a0 : A .1, ((O sf (φ a0)) .1);
                                       trunc_sigma
                                         A .2 (λ a0 : A .1, ((O sf (φ a0))) .2))
                                      (λ a, (φ a.1))
                                      (λ u, λ v, (u.1;v))
                                      (λ u, u.2)
                                      (λ a, eta_sigma a)) x); simpl in foo.   
  - intro x. unfold nj_inter_f, nj_inter_g. simpl.
    pose (foo := ap10 (reflect_factoriality_post sf
                         (∃ a : A .1, (φ a) .1;
                          trunc_sigma  A .2 (λ a : A .1, (φ a) .2))
                         (∃ a : A .1, ((O sf (φ a)) .1);
                          trunc_sigma 
                            A .2 (λ a : A .1, ((O sf (φ a))) .2))
                         (O sf
                            (∃ a : A .1, (φ a) .1;
                             trunc_sigma A .2 (λ a : A .1, (φ a) .2)))
                         (subuniverse_O sf _)
                         (λ X : (∃ a : A .1, ((O sf (φ a)) .1);
                                 trunc_sigma 
                                   A .2 (λ a : A .1, ((O sf (φ a))) .2)) .1,
                                O_rec sf (φ X .1)
                                      (O sf
                                         (∃ a : A .1, (φ a) .1;
                                          trunc_sigma  A .2 (λ a : A .1, (φ a) .2)))
                                      (subuniverse_O sf _)
                                      (λ φa : (φ X .1) .1,
                                              O_unit sf
                                                     (∃ a : A .1, (φ a) .1;
                                                      trunc_sigma  A .2 (λ a : A .1, (φ a) .2))
                                                     (X .1; φa)) X .2)
                         (λ X : (∃ a : A .1, (φ a) .1;
                                 trunc_sigma 
                                   A .2 (λ a : A .1, (φ a) .2)) .1,
                                (X .1; O_unit sf (φ X .1) X .2)))
                      x
         ).

    etransitivity; try exact foo. clear foo.
    apply (ap10 (O_rec_O_rec_dep_retr sf 
                                      (∃ a : A .1, (φ a) .1; trunc_sigma A .2 (λ a : A .1, (φ a) .2))
                                      (λ a, (φ a .1))
                                      (λ a b, (a.1;b))
                                      (λ a, a.2)
                                      (λ a, eta_sigma a))
                x).
  Defined.

  Definition nj_inter (sf : subu_family) (A : Trunk@{i' i a} n) (φ : A.1 -> Trunk@{i' i a} n): 
    O@{u a i' i} sf ({a:A.1 & (φ a).1}; trunc_sigma (A.2) (fun a => (φ a).2)) =
    O@{u a i' i} sf ({a:A.1 & (O sf (φ a)).1}; trunc_sigma (A.2) (fun a => (O sf (φ a)).2)).
    apply truncn_unique.
    exact fs.
    apply path_universe_uncurried. exact (BuildEquiv _ _ _ (nj_inter_equiv sf _ _)).
  Defined.

  Definition nj_fibers_compose (sf : subu_family) (A B C : Type@{i}) (f : A -> B) (g : B -> C) (c : C)
             (HB : ∀ b : B, IsTrunc n (hfiber f b)) (HC : ∀ c : C, IsTrunc n (hfiber g c))
  :
    O@{u a i' i} sf (hfiber (g o f) c; function_trunc_compo n f g HB HC c) =
    O@{u a i' i} sf ({ w :  hfiber g c &  (O sf (hfiber f (pr1 w);(HB (pr1 w)))).1};
            trunc_sigma (HC c) (fun a => (O sf (hfiber f a .1; HB a .1)) .2)).
    assert ((hfiber (g o f) c; function_trunc_compo n f g HB HC c) =
            ({ w : (hfiber g c) & hfiber f (pr1 w) }; trunc_sigma (HC c) (fun w => HB w.1))).
    apply truncn_unique. exact fs. apply fibers_composition.
    apply (transport (fun X => O sf X = _) (inverse X)). clear X.
    apply (nj_inter sf (hfiber g c; HC c) (fun w => (hfiber f w .1; HB w.1))).
  Defined.
  
  Definition type_j_f (sf : subu_family) (E:Type@{i}) (χ : E -> J@{i' u i a}) :
    (E -> subuniverse_Type sf) -> pr1 (nchar_to_sub (pr1  o χ))
    -> subuniverse_Type sf := λ α e, α (pr1 e).

  Definition type_j_inv (sf : subu_family) (E:Type@{i}) (χ : E -> J@{i' u i a}) : (pr1 (nchar_to_sub (pr1  o χ)) -> subuniverse_Type@{u a i' i} sf) -> E -> subuniverse_Type@{u a i' i} sf  :=
    λ α e, let f := (pr2 (nchar_to_sub (pr1  o α))) in
           let m := (pr2 (nchar_to_sub (pr1  o χ))) in
           (O sf (nsub_to_char n ({b : _ &  pr1 (pr1 (α b))}; ((pr1 m) o (pr1 f); function_trunc_compo n (pr1 f) (pr1 m) (pr2 f) (fun e => IsHProp_IsTrunc (pr2 m e) n0))) e); subuniverse_O sf _).

  Instance nTjTiSnTjT_eq (sf : subu_family) (E:Type@{i}) (χ : E -> J@{i' u i a}) : IsEquiv (λ (f : E -> subuniverse_Type@{u a i' i} sf) (t : {b : E & pr1 (pr1 (χ b))}), f (pr1 t)). 
  apply (isequiv_adjointify _ (type_j_inv (E:=E) (χ))).
  - intro φ.
    unfold type_j_inv. simpl. unfold nchar_to_sub, hfiber in φ; simpl in φ.
    apply path_forall; intro x.
    apply unique_subuniverse.
    rewrite (O_modal (φ x)).
    apply (ap (O sf)).
    apply truncn_unique.
    exact fs.
    eapply concat; try exact (hfiber_pi1 ( (λ t : _, pr1 (pr1 (φ t)))) x).
    symmetry. apply (hfiber_mono (pr1 ) (g:=pr1 )).
    intros X Y. apply subset_is_subobject. intro.
    exact (pr2 (pr1 (χ a))).
  - intro φ.
    unfold type_j_inv. simpl.
    apply path_forall; intro x.
    apply unique_subuniverse.
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
    apply (transport (fun x => O sf x = _ ) (inverse X)). clear X.
    pose (X := (nj_fibers_compose@{i u a i'} sf x (λ e : {b : E | ((φ b) .1) .1},
                                           IsHProp_IsTrunc
                                             (nchar_to_sub_compat (λ t : {b : E | ((φ b) .1) .1}, (χ t .1) .1) e)
                                             n0) (nchar_to_sub_compat (λ t : E, (φ t) .1)))).
    apply (transport (fun x => x = _) (inverse X)). clear X.
    
    apply ap. apply truncn_unique. simpl.
    (* etransitivity. *)
    exact fs.
    apply path_universe_uncurried.
    eapply transitive_equiv.
    apply equiv_sigma_contr.
    intro. pose (f := j_is_nj sf (hfiber pr1 a .1; 
                               (nchar_to_sub_compat (λ t : {b : E | ((φ b) .1) .1}, (χ t .1) .1)
                                                    a .1))).
    apply (transport (fun X => Contr X) f).
    simpl.
    apply (transport (fun X => Contr (not (not X))) (inverse (nhfiber_pi1 _ _))).
    apply Oj_J_Contr.
    apply equiv_path.
    etransitivity. apply nhfiber_pi1. reflexivity.
  Defined.

  Definition nTjTiseparated_eq_fun_univ (sf : subu_family) (E:Type@{i}) (χ : EnJ@{i i' a u} sf E) (φ1 φ2 : E → (exist (IsTrunc (n.+1)) (subuniverse_Type sf) (@subuniverse_Type_is_TrunkSn sf)).1)
             (p: E_to_χ_map (exist (IsTrunc (n.+1)) (subuniverse_Type@{u a i' i} sf)
                                   (@subuniverse_Type_is_TrunkSn sf)) χ φ1 =
                 E_to_χ_map (exist (IsTrunc (n.+1)) (subuniverse_Type@{u a i' i} sf)
                                   (@subuniverse_Type_is_TrunkSn sf)) χ φ2)
             (x:E)
  :  ((φ1 x).1.1 -> (φ2 x).1.1).

    unfold E_to_χ_map in p.
    generalize dependent (EnJ_is_nJ χ x).
    pose (p0 := O_rec sf (χ x) (existT (IsTrunc n) (((φ1 x) .1) .1 → ((φ2 x) .1) .1)  (trunc_arrow ((φ2 x) .1).2)) (subuniverse_arrow (((φ1 x) .1)) (φ2 x))); simpl in p0.
    apply p0.
    intro v. simpl.

    assert (eq := (ap10 p (x;v))). 
    exact (transport (λ U, U) (eq..1..1)).
  Defined.
  
  Lemma nTjTiseparated_eq_fun_univ_invol (sf : subu_family) (E:Type@{i}) (χ : EnJ@{i i' a u} sf E) φ1 φ2 (p: E_to_χ_map
                                                                        (exist (IsTrunc (n.+1)) (subuniverse_Type sf) (@subuniverse_Type_is_TrunkSn sf)) χ φ1 =
                                                                      E_to_χ_map
                                                                        (exist (IsTrunc (n.+1)) (subuniverse_Type sf) (@subuniverse_Type_is_TrunkSn sf)) χ φ2) (x:E)
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
         ). 
    apply (transport (λ u, u = y) foo^). clear foo.

    pose (fooo := @transport_arrow_space_dep_path sf (φ1 x) (φ2 x) (χ x) (λ v, (ap10 p (x;v))..1..1)).
    simpl in fooo.

    transitivity (O_rec sf (χ x)
                    (((φ2 x) .1) .1 → ((φ2 x) .1) .1; trunc_arrow ((φ2 x).1.2))
                     (subuniverse_arrow ((φ2 x) .1)  (φ2 x))
                    (λ (v : (χ x) .1) (x0 : ((φ2 x) .1) .1),
                     transport idmap
                               
                               (ap10 p (x; v))..1..1
                               (transport idmap
                                          
                                          (ap10 p (x; v))..1..1^ x0)) (EnJ_is_nJ χ x) y); auto with path_hints.

    apply (ap (λ u, O_rec sf (χ x)
                          (((φ2 x) .1) .1 → ((φ2 x) .1) .1; trunc_arrow ((φ2 x).1.2))
                           (subuniverse_arrow ((φ2 x) .1) (φ2 x))
                          u (EnJ_is_nJ χ x) y)).
    apply path_forall; intro v. apply path_forall; intro x0.
    apply ap. 
    apply (ap (λ U, transport idmap
                              U x0)).
    transitivity ((ap10 p (x; v))^..1..1).
    apply ap. apply ap.
    apply (ap10_V p (x;v)).
    unfold pr1_path.
    rewrite ap_V. rewrite ap_V. reflexivity.
    
    apply (transport (λ U, O_rec sf (χ x)
                                 (((φ2 x) .1) .1 → ((φ2 x) .1) .1; trunc_arrow ((φ2 x).1.2))
                                  (subuniverse_arrow ((φ2 x) .1)  (φ2 x))
                                 U
                                 (EnJ_is_nJ χ x) y = y) fooo^).
    clear fooo; simpl.
    pose (foo := ap10 (ap10 (O_rec_const sf (χ x) (((φ2 x) .1) .1 → ((φ2 x) .1) .1; trunc_arrow ((φ2 x).1.2))
                                                (subuniverse_arrow ((φ2 x) .1)  (φ2 x)) idmap) (EnJ_is_nJ χ x)) y). simpl in foo.
    etransitivity; [exact foo | reflexivity].
  Defined.

  Definition nTjTiseparated_eq_inv (sf : subu_family) (E:Type@{i}) (χ : EnJ@{i i' a u} sf E)
             (φ1 φ2 : E → (exist (IsTrunc (n.+1)) (subuniverse_Type@{u a i' i} sf) (@subuniverse_Type_is_TrunkSn sf)).1) :
    E_to_χ_map
      (exist (IsTrunc (n.+1)) (subuniverse_Type@{u a i' i} sf) (@subuniverse_Type_is_TrunkSn sf)) χ φ1 =
    E_to_χ_map 
      (exist (IsTrunc (n.+1)) (subuniverse_Type@{u a i' i} sf) (@subuniverse_Type_is_TrunkSn sf)) χ φ2
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

  Lemma nTjTiseparated_eq (sf : subu_family) :
         separated@{Si' u a i i'} sf (existT (IsTrunc (n.+1)) (subuniverse_Type@{u a i' i} sf)
                                             (@subuniverse_Type_is_TrunkSn@{u a i' i} sf)).

    intros E χ φ1 φ2.

    apply isequiv_adjointify with (g := @nTjTiseparated_eq_inv sf E χ φ1 φ2).
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
      apply (transport (λ U, O_rec sf _ (((φ1 (pr1 x)).1).1 → ((φ2 (pr1 x)).1).1;
      trunc_arrow ((φ2 (pr1 x)).1).2)
                                   (subuniverse_arrow ((φ1 (pr1 x)).1) (φ2 (pr1 x))) _ U = _) ((witness_is_eta χ x)^)). simpl.
      etransitivity;
        try exact (ap10 (O_rec_retr sf (χ x.1) (((φ1 x .1) .1) .1 → ((φ2 x .1) .1) .1; trunc_arrow ((φ2 x.1).1.2)) (subuniverse_arrow ((φ1 x .1) .1) (φ2 x .1)) (λ v : (χ x .1) .1, transport idmap ((ap10 p (x .1; v)) ..1) ..1)) x.2).
      repeat apply ap.  destruct x as [x1 x2]. simpl. 

      (* reflexivity does not apply anymore ?*)
      admit.
      
    (* reflexivity. *)
      
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
      exact (ap10 (O_rec_const sf (χ x) (((φ1 x) .1) .1 → ((φ1 x) .1) .1; trunc_arrow ((φ1 x).1.2))
                                       (subuniverse_arrow ((φ1 x) .1)  (φ1 x)) idmap) (EnJ_is_nJ χ x)). 
  Defined.

  Definition nType_j_Type (sf : subu_family) : Trunk@{Si' u a} (n.+1) :=
    (existT (IsTrunc (n.+1)) (subuniverse_Type@{u a i' i} sf) (@subuniverse_Type_is_TrunkSn sf)).


  
  Lemma nType_j_Type_is_SnType_j_Type (sf : subu_family) : Snsheaf_struct@{Si' u a i i'} sf
                                                      (nType_j_Type@{Si' u a i' i} sf).
  Proof.
    split.
    apply nTjTiseparated_eq@{Si' u a i i' i'}.
    intros E χ. unfold E_to_χ_map; simpl.
    exact (nTjTiSnTjT_eq _ _).
  Defined.

  Definition nType_j_Type_sheaf (sf : subu_family) : SnType_j_Type@{Si' u a i i'} sf :=
    (nType_j_Type@{Si' u a i' i} sf; nType_j_Type_is_SnType_j_Type@{Si' u a i i'} sf).
  
  Instance dep_prod_SnType_j_Type_eq (sf : subu_family)
           (A : Type@{u})
           (B : A -> SnType_j_Type@{Si' u a i' i} sf)
  : forall (E:Type) (χ : E -> J) (H := λ a, (snd (pr2 (B a))) E χ),
      IsEquiv (λ (f : E -> ∀ a : A, pr1 (pr1 (B a))) (t : {b : E & pr1 (pr1 (χ b))}), f (pr1 t)).
  intros E χ H.   
  apply (isequiv_adjointify _ (λ g e a, (@equiv_inv _ _ _ (H a) (λ x, g x a) e))).
  - intro φ.
    apply path_forall; intro x.
    apply path_forall; intro a.
    destruct (H a); simpl in *.
    clear eisadj; clear eissect.
    unfold nchar_to_sub in equiv_inv; simpl.
    unfold Sect, nchar_to_sub, E_to_χmono_map in eisretr.
    specialize (eisretr (λ x, φ x a)).
    exact (ap10 eisretr x).
  - intro φ.
    apply path_forall; intro x.
    apply path_forall; intro a.
    destruct (H a); simpl in *.
    clear eisadj; clear eisretr.
    unfold nchar_to_sub in equiv_inv; simpl.
    unfold Sect, nchar_to_sub, E_to_χ_map in eissect.
    specialize (eissect (λ x, φ x a)).
    exact (ap10 eissect x).
  Defined.

  Definition dep_prod_SnType_j_Type_sep_inv (sf : subu_family)
             (A : Type@{u})
             (B : A -> SnType_j_Type@{Si' u a i i'} sf)
             (E : Type)
             (χ : EnJ sf E)
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
    unfold ap10, path_forall; rewrite eisretr. reflexivity.
  Qed.

  Lemma dep_prod_SnType_j_Type_sep (sf : subu_family)
        (A : Type@{u})
        (B : A -> SnType_j_Type@{Si' u a i i'} sf)
  : forall (E:Type) (χ : EnJ sf E), IsMono
                                   (λ (f : E -> ∀ a : A, (B a).1.1) (t : {b : E & (χ b).1}), f (t.1)).
    intros E χ.
    unfold IsMono.
    intros f g.
    apply @isequiv_adjointify with (g := @dep_prod_SnType_j_Type_sep_inv sf A B E χ f g).
    - unfold Sect.
      intro p.
      unfold dep_prod_SnType_j_Type_sep_inv. 
      unfold E_to_χ_map. simpl.
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
      reflexivity.
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
      match goal with
        |[|- _ = ap10 (ap _ ?X) _] => pose (ap10_ap_precompose (pr1 : ({e:E & (χ e).1} -> E)) X) end. rewrite p.
      unfold ap10; rewrite eisretr. reflexivity.
      exact (apD10 X x).
  Defined.
  
  Definition dep_prod_SnType_j_Type (sf : subu_family) :
    forall (A: Trunk@{Si' u a} n.+1) (B : A.1 -> SnType_j_Type@{Si' u a i i'} sf) ,
      Snsheaf_struct sf (forall a, pr1 (pr1 (B a)); 
                                                        @trunc_forall _ A.1 (fun a => pr1 (pr1 (B a))) (trunc_S n) (fun a => pr2 (pr1 (B a)))).
    intros. split. 
    exact (dep_prod_SnType_j_Type_sep _).
    exact (dep_prod_SnType_j_Type_eq _).
  Defined.

  Definition test (sf : subu_family@{u a}) (T: Trunk@{Si' u a} n.+1) :=
    @dep_prod_SnType_j_Type@{Si' u a i i'} sf T (λ _, nType_j_Type_sheaf@{Si' u a i i'} sf).
  
  Definition closed (sf : subu_family@{u a}) E (χ : E -> Trunk n) := forall e, IsEquiv (O_unit sf (χ e)).
  
  Definition closed' (sf : subu_family@{u a}) E A (m : {f : A -> E & forall b:E, IsTrunc n (hfiber f b)}) := closed sf (nsub_to_char n (A;m)).

  Definition cloture (sf : subu_family@{u a}) E (χ : E -> Trunk n) : E -> Trunk n := O sf o χ.
  
  Definition cloture' (sf : subu_family@{u a}) E A (m : {f : A -> E & forall b:E, IsTrunc n (hfiber f b)}) :=
    nchar_to_sub (cloture sf (nsub_to_char n (A;m))).

  Definition cloture_is_closed (sf : subu_family@{u a}) (E :Type) (χ : E -> Trunk n) : closed sf (cloture sf χ).
    intro. apply (O_modal_equiv ((cloture sf χ e); (subuniverse_O sf _))).
  Defined.

  Lemma cloture_is_closed' (sf : subu_family@{u a}) (A:Type) (E:Type) (m : {f : A -> E & forall e:E, IsTrunc n (hfiber f e)}) : closed' sf (pr2 (cloture' sf m)).
    unfold closed', cloture'. 
    rewrite (eta_sigma (nchar_to_sub (cloture sf (nsub_to_char n (A; m))))).
    pose (f := cloture_is_closed sf (nsub_to_char n (A; m))). 
    rewrite <- (@nsub_eq_char_retr ua fs n _ (cloture sf (nsub_to_char n (A; m)))) in f.
    exact f.
  Defined.
  
  Definition δ (T:Trunk (trunc_S n)) : T.1 * T.1-> Trunk n.
    intros x. exists (fst x = snd x). apply istrunc_paths.
    exact T.2.
  Defined.

  Definition Δ (T:Trunk (trunc_S n)) := nchar_to_sub (δ T).
  
  Definition clδ (sf : subu_family@{u a}) T := O sf o (δ T).

  Definition clΔ (sf : subu_family@{u a}) T := (nchar_to_sub (clδ sf T)).

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
        
  Lemma dicde_l (sf : subu_family@{u a}) (E:Type) (φ:E -> Trunk n) (A:={e:E & (φ e).1}) (clA := {e:E & (O sf (φ e)).1}) (e:clA)
  : (∃ rx : ((O sf (φ e .1)) .1),
       rx =
      e.2) =(∃ rx : ((O sf (φ e .1)) .1),
       O_rec sf (φ e .1) (O sf (O sf (φ e .1))) (subuniverse_O sf _)
             (λ x : (φ e .1) .1,
                    O_unit sf (O sf (φ e .1)) (O_unit sf (φ e .1) x)) rx =
       O_unit sf (O sf (φ e .1)) e .2)
    .
    apply path_universe_uncurried.
    assert (foo := @equal_hfibers
                   ((O sf (φ e .1)).1)
                   ((O sf (O sf (φ e .1))).1)
                   ((O_invol_ sf (φ e .1))..1)
                   (O_rec sf (φ e .1) (O sf (O sf (φ e .1)) ) (subuniverse_O sf _)
                          (λ x : (φ e .1) .1, O_unit sf (O sf (φ e .1)) (O_unit sf (φ e .1) x)))
                   (O_unit sf (O sf (φ e .1)))
                   e.2). simpl in foo.
    apply foo. clear foo.
    - simpl.
      pose (bar := O_rec_sect sf (φ e .1) (O sf (O sf (φ e .1))) (subuniverse_O sf _) (O_unit sf _)).  simpl in bar.
      unfold O_rec; simpl in *.
      apply path_forall; intro x.
      etransitivity; try exact (ap10 bar x).
      refine (ap10 (OO_unit_idmap sf _) x).
    - apply OO_unit_idmap.
  Defined.
    
  Lemma dicde_ll (sf : subu_family)
        (E : Type)
        (φ : E → Trunk n)
        (A := ∃ e : E, (φ e) .1 : Type)
        (clA := ∃ e : E, ((O sf (φ e)) .1): Type)
        (a : ∃ e : E, ((O sf (φ e)) .1))
        (x : ∃ π : (φ a .1) .1, O_unit sf (φ a .1) π = a .2)
        (π : ∃ π : (φ a .1) .1, O_unit sf (φ a .1) π = a .2)
        (π' : ∃ π : (φ a .1) .1, O_unit sf (φ a .1) π = a .2)
  : equiv_path _ _ (dicde_l sf φ a) (a .2; 1) =
    (O_unit sf (φ a .1) π' .1;
     islex_compat_func sf (φ a .1) (O sf (φ a .1)) (O_unit sf (φ a .1)) _ π').
    unfold dicde_l.   
    unfold path_universe_uncurried.
    rewrite eisretr. simpl. hott_simpl.
    apply @path_sigma' with (p := π'.2^). simpl. destruct π' as [b p]. simpl. destruct p. simpl.
    unfold ap10, path_forall. rewrite apD10_pp. rewrite (eisretr apD10).
    rewrite apD10_V. hott_simpl.
    unfold islex_compat_func. simpl.
    exact (ap10_O_retr_sect (φ a.1) ((O sf (O sf (φ a.1))); (subuniverse_O sf (O sf (φ a.1)))) (O_unit sf (O sf (φ a.1))) b). 
  Defined.
    
  Lemma path_sigma_eta (A : Type) (P : A → Type) (u : ∃ x, P x)
  : path_sigma P u (u.1;u.2) 1 1 = (eta_sigma u)^.
  destruct u. simpl. reflexivity.
  Defined.

  Lemma dense_into_cloture_dense_eq (sf : subu_family) (E:Type) (φ:E -> Trunk n) (A:={e:E & (φ e).1}) (clA := {e:E & (O sf (φ e)).1})
  : is_dense_eq sf (λ e:clA, ({π : (φ e.1).1 & O_unit sf _ π = e.2} ; trunc_sigma (φ e .1) .2
              (λ a : (φ e .1) .1,
               istrunc_paths (trunc_succ ((O sf (φ e.1)).2)) (O_unit sf (φ e .1) a) e .2))).
    intro e.
    assert (rew := ((islex_nj sf (φ e .1) (O sf (φ e .1)) (O_unit sf _) e.2) @ (dicde_l sf φ e)^)).
    apply path_universe_uncurried.
    apply (transport (λ U, (∃ e' : clA, e = e') <~> U) (islex_nj sf (φ e .1) (O sf (φ e .1)) (O_unit sf _) e.2)^).
    apply (transport (λ U, (∃ e' : clA, e = e') <~> U) (dicde_l sf φ e)).
    
    exists ((λ x:(∃ e' : clA, e = e'), existT (λ u, u = e.2) e.2 1)).
    apply @isequiv_adjointify with (g:= (λ x:(∃ rx : ((O sf (φ e .1)) .1), rx = e .2), ((e.1;x.1); path_sigma _ e (e.1;x.1) 1 x.2^))).

    - intros [x p]. destruct p. reflexivity.
    - intros [x p]. destruct p. simpl.
      apply @path_sigma' with (p := eta_sigma _).
      rewrite path_sigma_eta.
      simpl.
      reflexivity.
  Defined.

  Lemma transport_equiv (A: Type) (f g:A -> Type) (x y: A) (p: x=y) (q: f x <~> g x)
  : transport (λ a:A, f a <~> g a) p q
    = (equiv_compose' (equiv_path _ _ (ap g p)) (equiv_compose' q (equiv_inverse (equiv_path _ _ (ap f p))))).
    path_induction.
    destruct q. apply equal_equiv. simpl. done.
  Defined.

  Lemma dense_into_cloture_dense_diag (sf : subu_family) (E:Type) (φ:E -> Trunk n) (A:={e:E & (φ e).1}) (clA := {e:E & (O sf (φ e)).1})
  : is_dense_diag (dense_into_cloture_dense_eq sf φ).
    intros x p.
    unfold dense_into_cloture_dense_eq.
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
    (* rewrite ap_const. *)
    (* unfold compose. *)
    simpl.
    rewrite transport_pp.

    pose (foo := lex_compat sf (φ a .1) (O sf (φ a .1)) (O_unit sf (φ a .1))). unfold equiv_path in foo; simpl in foo.
    specialize (foo a.2 π'). simpl in foo.
    unfold hfiber in foo. simpl in foo.
    (* assert (bar := foo..1); simpl in bar. *)

    apply (moveR_transport_V idmap (islex_nj sf (φ a .1) (O sf (φ a .1))  (O_unit sf (φ a .1)) a .2) (transport idmap (dicde_l sf φ a)  (a .2; 1))).

    apply (transport (λ U, transport idmap (dicde_l sf φ a) (a .2; 1) = U) foo^).
    clear foo.
    apply dicde_ll. exact π. exact π'.
  Qed.
  
  Definition dense_into_cloture (sf : subu_family) (E:Type) (φ:E -> Trunk n) (A:={e:E & (φ e).1}) (clA := {e:E & (O sf (φ e)).1})
  : EnJ sf clA.
    refine (Build_EnJ _ (dense_into_cloture_dense_eq sf φ) _).
    apply dense_into_cloture_dense_diag.
  Defined.

  Definition transport_density (sf : subu_family) (E:Type) (φ:E -> Trunk n) (A:={e:E & (φ e).1}) (clA := {e:E & (O sf (φ e)).1})
  : forall X, clA = X -> EnJ sf X.
    pose (e := dense_into_cloture sf φ); simpl in e.
    destruct e as [χ χeq χdiag].
    intros X p.
    refine (Build_EnJ _ _ _).
    - intro x. apply χ.
      apply (equiv_path _ _ p).
      exact x.
    - destruct p. intro x. simpl.
      apply χeq.
    - destruct p. intros x e'. simpl.
      apply χdiag. exact e'.
  Defined.

  Definition path_sigma_transport (E:Type) (φ χ : E -> Type) (eq : χ = φ) (x y : {e:E & φ e})
  : (x = y) <~> ((x.1 ; transport idmap (ap10 eq x.1)^ x.2) = (y.1 ; transport idmap (ap10 eq y.1)^ y.2)).
    destruct eq. simpl.
    apply equiv_idmap.
  Defined.

  Definition path_sigma_transport_transport (E:Type) (φ χ : E -> Type) (α : {e:E & (χ e)} -> Type) (eq : χ = φ) (x y : {e:E & φ e}) (xy : x = y) 
  : transport (λ u:{e:E & (χ e)}, α u) ((path_sigma_transport eq x y) xy)^
    =
    transport (λ u:{e:E & (φ e)}, α (u.1 ; transport idmap (ap10 eq u.1)^ u.2))
              xy^.
  destruct eq; simpl. reflexivity.
  Defined.
            
  Definition path_sigma_transport' (E:Type) (φ χ : E -> Type) (eq : χ == φ) (x y : {e:E & φ e})
  : (x = y) <~> ((x.1 ; transport idmap (eq x.1)^ x.2) = (y.1 ; transport idmap (eq y.1)^ y.2)).
    transitivity ((x.1; transport idmap (ap10 (path_forall _ _ eq) x.1)^ x.2) = (y.1; transport idmap (ap10 (path_forall _ _ eq) y.1)^ y.2)).
    refine (path_sigma_transport _ _ _).
    unfold ap10, path_forall. rewrite eisretr. 
    apply equiv_idmap.
  Defined.

  Definition path_sigma_transport'_transport (E:Type) (φ χ : E -> Type) (α : {e:E & (χ e)} -> Type) (eq : χ == φ) (x y : {e:E & φ e}) (xy : x = y)
  : transport (λ u:{e:E & (χ e)}, α u) ((path_sigma_transport' eq x y) xy)^
    =
    transport (λ u:{e:E & (φ e)}, α (u.1 ; transport idmap (eq u.1)^ u.2))
              xy^.
  simpl.
  destruct (eisretr apD10 eq). simpl.  simpl.
  exact (@path_sigma_transport_transport E φ χ α (path_forall χ φ eq) x y xy).
  Defined.
  Opaque path_sigma_transport'.

  Definition transport_density_sigma (sf : subu_family) (E:Type) (φ:E -> Trunk n) (A:={e:E & (φ e).1}) (clA := {e:E & (O sf (φ e)).1})
  : forall α:E -> Trunk n, ( pr1 o (O sf) o φ == pr1 o α) -> EnJ sf {e:E & (α e).1}.
    intros α p.
    transparent assert (X : (clA = (∃ e : E, (α e).1))).
    { apply path_universe_uncurried.
      apply (equiv_functor_sigma_id).
      intro a. apply equiv_path. apply p.
    }
    pose (e := dense_into_cloture sf φ); simpl in e.
    destruct e as [χ χeq χdiag].
    refine (Build_EnJ _ _ _).
    - intro x. apply χ.
      exists x.1.
      apply (equiv_path _ _ (p x.1)).
      exact x.2.
    - intro e. simpl in *.

      pose (eq := χeq (e.1; transport idmap (p e.1)^ e.2)).
      etransitivity; try exact eq. clear eq.
      apply path_universe_uncurried.
      refine (equiv_functor_sigma' _ _).
      apply (equiv_functor_sigma_id).
      intro a.
      apply equiv_path. exact (p a)^.
      intro a. simpl. unfold functor_sigma.
      apply path_sigma_transport'.
    - simpl.
      intros x y.
      unfold equiv_functor_sigma', equiv_functor_sigma_id, equiv_functor_sigma. simpl.

      apply path_forall; intro z.
      rewrite transport_pp.
      rewrite transport_path_universe_uncurried. simpl.
      unfold functor_sigma. simpl.
      specialize (χdiag (((x.1).1; transport idmap (p (x.1).1)^ (x.1).2); x.2)). simpl in χdiag.
      unfold incl_Aeq_Eeq in χdiag; simpl in χdiag.
      specialize (χdiag (((x.1.1 ; (equiv_path _ _ (p x.1.1)^ x.1.2)) ; x.2);1)).
      apply ap10 in χdiag.
      specialize (χdiag (((((z.1).1).1; transport idmap (p ((z.1).1).1)^ ((z.1).1).2) ; z.1.2);(path_sigma_transport' p x.1 (z.1).1) z.2)).
      simpl in χdiag.
      etransitivity; try exact χdiag.
      apply ap.
      exact (ap10 (@path_sigma_transport'_transport E (pr1 o α) (pr1 o O sf o φ) (pr1 o χ) p x.1 z.1.1 z.2) z.1.2). 
  Defined.
      
End Definitions. 