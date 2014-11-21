Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import lemmas epi_mono equivalence univalence sub_object_classifier modalities.
Require Import nat_lemmas.
Require Import colimit.
Require Import cech_nerve.
Require Import sheaf_base_case.
Require Import sheaf_def_and_thm.
Require Import cloture_hpullback.

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


Section Type_to_separated_Type.

  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  
  Local Definition n0 := sheaf_def_and_thm.n0.
  Local Definition n := sheaf_def_and_thm.n.
  Local Definition nj := sheaf_def_and_thm.nj.
  Local Definition j_is_nj := sheaf_def_and_thm.j_is_nj.
  Local Definition j_is_nj_unit := sheaf_def_and_thm.j_is_nj_unit.
  Local Definition islex_nj := sheaf_def_and_thm.islex_nj.
  Local Definition lex_compat := sheaf_def_and_thm.lex_compat.


  Definition separated_Type (T:Trunk (trunc_S n)) : Type :=
    Im (λ t : pr1 T, λ t', nj.(O) (t = t'; istrunc_paths T.2 t t')).

  Definition sheaf_is_separated (T : SnType_j_Type) : separated T.1 := fst (T.2).
 
  Definition separated_Type_is_Trunk_Sn (T:Trunk (trunc_S n)) : IsTrunc (trunc_S n) (separated_Type T).
    unfold separated_Type; simpl.
    destruct T as [T TrT]; simpl in *.
    apply (@trunc_sigma _ (fun P => _)). 
    apply (@trunc_forall _ _ (fun P => _)). intro. 
    exact (@subuniverse_Type_is_TrunkSn _ nj).
    intro φ. exact (IsHProp_IsTrunc (istrunc_truncation _ _) n). 
  Defined.

  Definition E_to_χ_map_ap (T U:Trunk (trunc_S n)) E (χ : EnJ E) (f : E -> (pr1 T))
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

  Instance separated_mono_is_separated_ (T U:Trunk (trunc_S n)) E χ g h (f: pr1 T -> pr1 U)
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

  Definition separated_mono_is_separated (T U:Trunk (trunc_S n)) (H:separated U) (f: pr1 T -> pr1 U)
             (fMono : IsMonof f) : separated T
 :=
    fun E χ x y => separated_mono_is_separated_ _ (H E χ (f o x) (f o y)) fMono.

  Definition T_nType_j_Type_trunc (T:Trunk (trunc_S n)) : IsTrunc (trunc_S n) (pr1 T -> subuniverse_Type nj).
    apply (@trunc_forall _ _ (fun P => _)). intro. 
    apply (@trunc_sigma _ (fun P => _)). apply Tn_is_TSn.
    intro. apply IsHProp_IsTrunc. exact (pr2 (subuniverse_HProp nj a0)).
  Defined.

  Definition T_nType_j_Type_isSheaf : forall T, Snsheaf_struct (pr1 T -> subuniverse_Type nj;
                                                    T_nType_j_Type_trunc T).
    intro.
    apply (dep_prod_SnType_j_Type (fun x:pr1 T => ((subuniverse_Type nj ; @subuniverse_Type_is_TrunkSn _ nj);nType_j_Type_is_SnType_j_Type))).
  Defined.

  Definition T_nType_j_Type_sheaf T : SnType_j_Type :=  ((pr1 T -> subuniverse_Type nj; T_nType_j_Type_trunc T); T_nType_j_Type_isSheaf _).

  Definition separated_Type_is_separated (T:Trunk (trunc_S n)) : separated (separated_Type T; separated_Type_is_Trunk_Sn (T:=T)).
    apply (@separated_mono_is_separated
              (separated_Type T;separated_Type_is_Trunk_Sn (T:=T))
              (pr1 T -> subuniverse_Type nj; T_nType_j_Type_trunc T)
              (sheaf_is_separated (T_nType_j_Type_sheaf T))
              (pr1 )).
    intros X f g. simpl in *.
    apply @isequiv_adjointify with (g := λ H, (path_forall _ _ (λ x, path_sigma _ _ _ (ap10 H x) (path_ishprop _ _)))).
    - intro p.
      apply (@equiv_inj _ _ _ (isequiv_ap10 _ _)).
      apply path_forall; intro x.
      apply (transport (λ U, U = ap10 p x) (ap10_ap_postcompose pr1 _ x)^).
      unfold ap10 at 1, path_forall at 1. rewrite eisretr.
      apply pr1_path_sigma.
    - intro x. destruct x. simpl.
      etransitivity; [idtac | apply path_forall_1].
      apply ap.
      apply path_forall; intro x.
      unfold path_ishprop.
      rewrite (@contr ((f x) .2 = (f x) .2) _ 1).
      apply path_sigma_1.
  Defined.

  Definition separation (T:Trunk (trunc_S n)) : {T : Trunk (trunc_S n) & separated T} :=
    ((separated_Type T ; separated_Type_is_Trunk_Sn (T:=T));separated_Type_is_separated (T:=T)).

  Definition separated_unit T :  pr1 T -> separated_Type T := toIm _.

  Definition kpsic_func_univ_func
             (T : Trunk (trunc_S n))
             (a : T .1)
             (b : T .1)
             (p : ((clδ T) (a, b)) .1)
             (Ωj := (T .1 → subuniverse_Type nj; T_nType_j_Type_trunc T)
                    : ∃ x, IsTrunc (trunc_S n) x)
             (inj := (pr1:separated_Type T → Ωj .1) : separated_Type T → Ωj .1)
             (X : IsMono inj)
             (t : T .1)
  : ((O nj (a = t; istrunc_paths T.2 a t)) .1) .1 ->
    ((O nj (b = t; istrunc_paths T.2 b t)) .1) .1.
    apply O_rec; intro u.
    generalize dependent p; apply O_rec; intro v. apply (O_unit nj).
    exact (v^@u).
  Defined.

  Definition kpsic_func_univ_inv
             (T : Trunk (trunc_S n))
             (a : T .1)
             (b : T .1)
             (p : ((clδ T) (a, b)) .1)
             (Ωj := (T .1 → subuniverse_Type nj; T_nType_j_Type_trunc T)
                    : ∃ x, IsTrunc (trunc_S n) x)
             (inj := (pr1:separated_Type T → Ωj .1) : separated_Type T → Ωj .1)
             (X : IsMono inj)
             (t : T .1)
  : ((O nj (b = t; istrunc_paths T.2 b t)) .1) .1 ->
    ((O nj (a = t; istrunc_paths T.2 a t)) .1) .1 .
    apply O_rec; intro u.
    generalize dependent p; apply O_rec; intro v; apply (O_unit nj).
    exact (v@u).
  Defined.

  Lemma kpsic_func_univ_eq
        (T : Trunk (trunc_S n))
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
    split.
    - intro x.
      unfold kpsic_func_univ_inv, kpsic_func_univ_func, δ; simpl. unfold clδ, compose, δ in p; simpl in p.
      pose (foo := O_rec_O_rec nj
                     (a = t; istrunc_paths T.2 a t)
                     (b = t; istrunc_paths T.2 b t)
                     (a = b; istrunc_paths T.2 a b)
                     (λ u v, v^@ u)
                     (λ u v, v @ u)
                     p
           ); simpl in foo.
      
      refine (ap10 (f:= (O_rec (a = t; istrunc_paths T.2 a t)
                               (O nj (b = t; istrunc_paths T.2 b t))
                               (λ u : a = t,
                                      O_rec (a = b; istrunc_paths T.2 a b)
                                            (O nj (b = t; istrunc_paths T.2 b t))
                                            (λ v : a = b, O_unit nj (b = t; istrunc_paths T.2 b t) (v ^ @ u))
                                            p)) 
                          o (O_rec (b = t; istrunc_paths T.2 b t)
                                   (O nj (a = t; istrunc_paths T.2 a t))
                                   (λ u : b = t,
                                          O_rec (a = b; istrunc_paths T.2 a b)
                                                (O nj (a = t; istrunc_paths T.2 a t))
                                                (λ v : a = b, O_unit nj (a = t; istrunc_paths T.2 a t) (v @ u))
                                                p))) (g:=idmap) _ x).
      
      apply foo.
      intros q q'. destruct q.
      rewrite concat_p1.
      apply concat_Vp.
    - intro x. unfold kpsic_func_univ_inv, kpsic_func_univ_func, δ. simpl.
      pose (foo := O_rec_O_rec nj
                     (b = t; istrunc_paths T.2 b t)
                     (a = t; istrunc_paths T.2 a t)
                     (a = b; istrunc_paths T.2 a b)
                     (λ u v, v @ u)
                     (λ u v, v^ @ u)
                     p
                 ); simpl in foo.

      refine (ap10 (f:= (O_rec (b = t; istrunc_paths T.2 b t)
                               (O nj (a = t; istrunc_paths T.2 a t))
                               (λ u : b = t,
                                      O_rec (a = b; istrunc_paths T.2 a b)
                                            (O nj (a = t; istrunc_paths T.2 a t))
                                            (λ v : a = b, O_unit nj (a = t; istrunc_paths T.2 a t) (v @ u))
                                            p)) 
                          o (O_rec (a = t; istrunc_paths T.2 a t)
                                   (O nj (b = t; istrunc_paths T.2 b t))
                                   (λ u : a = t,
                                          O_rec (a = b; istrunc_paths T.2 a b)
                                                (O nj (b = t; istrunc_paths T.2 b t))
                                                (λ v : a = b, O_unit nj (b = t; istrunc_paths T.2 b t) (v ^ @ u))
                                                p))) (g:=idmap) _ x).
      apply foo.
      intros q q'. destruct q'.
      rewrite concat_1p.
      apply concat_1p.
  Qed.

  Arguments kpsic_func_univ_eq : default implicits, simpl never.

    Lemma kpsic_aux (A B:Trunk n) (v:A.1) (eq : A.1 = B.1)
  : O_unit nj B (transport idmap eq v)
    = transport idmap
                (ap pr1
                    (ap pr1
                        (ap (O nj)
                            (truncn_unique fs A B eq)))) (O_unit nj A v).
    destruct A as [A TrA], B as [B Trb]; simpl in *.
    destruct eq.
    simpl.
    unfold truncn_unique, eq_dep_subset. simpl.
    assert (p := (center (TrA = Trb))). destruct p.
    assert ((center (TrA = TrA)) = 1).
    apply path_ishprop.
    apply (transport (λ u, O_unit nj (A; TrA) v =
                           transport idmap
                                     (ap pr1
                                         (ap pr1
                                             (ap (O nj)
                                                 (path_sigma (λ T : Type, IsTrunc n T) 
                                                             (A; TrA) (A; TrA) 1 u))))
                                     (O_unit nj (A; TrA) v)) X^).
    simpl. exact 1.
  Defined.

  Theorem separated_unit_paths_are_nj_paths T (a b:T.1) : (separated_unit T a = separated_unit T b) <~> (O nj (a=b; istrunc_paths T.2 a b)).1.1.
  Proof.
    refine (equiv_adjointify _ _ _ _).
    - intro p.
      unfold separated_unit, toIm in p. simpl in p.
      pose (p' := (ap10 p..1 a)..1..1). simpl in p'.
      transparent assert (X: (((O nj (a = b; istrunc_paths T.2 a b)) .1) .1 =
       ((O nj (b = a; istrunc_paths T.2 b a)) .1) .1)).
        repeat apply (ap pr1); apply ap.
        apply truncn_unique. exact fs.
        apply equal_inverse.
      apply (transport  idmap X^).
      apply (transport idmap p'). apply O_unit. reflexivity.
    - intro p.
      pose (Ωj := (T.1 -> subuniverse_Type nj; T_nType_j_Type_trunc T)).
      pose (inj := pr1 : (separated_Type T) -> Ωj.1).
      transparent assert (X : (IsMono inj)).
      intros x y. apply subset_is_subobject. intro.
      apply istrunc_truncation.
      assert (inj (separated_unit T a) = inj (separated_unit T b)).
      unfold inj, separated_unit. simpl.
      apply path_forall; intro t; simpl.
      apply unique_subuniverse; apply truncn_unique. exact fs.
      unfold Oj; simpl. 
      apply path_universe_uncurried.
      exists (kpsic_func_univ_func a b p X t).
      apply isequiv_adjointify with (g := kpsic_func_univ_inv a b p X t);
        [exact (fst (kpsic_func_univ_eq a b p X t)) | exact (snd (kpsic_func_univ_eq a b p X t))].
      exact (@equiv_inv _ _ _ (X (separated_unit T a) (separated_unit T b)) X0).
    - intro x.
      apply (moveR_transport_V idmap _ _ x).
      unfold pr1_path. simpl.

      pose (foo := isequiv_eq_dep_subset (λ a0 : T.1 → subuniverse_Type nj,
                                                 istrunc_truncation -1
                                                                    (hfiber
                                                                       (λ t t' : T.1,
                                                                                 O nj (t = t'; istrunc_paths T.2 t t')) a0))
                                         (λ t' : T.1, O nj (a = t'; istrunc_paths T.2 a t');
                                          tr (a; 1))
                                         (λ t' : T.1, O nj (b = t'; istrunc_paths T.2 b t');
                                          tr (b; 1))).
      assert (bar := eissect _ (IsEquiv := foo)). simpl in bar.
      unfold Sect in bar. simpl in bar.
      rewrite bar. clear bar; clear foo.

      unfold ap10, path_forall; rewrite eisretr.

      assert (rew := eissect _ (IsEquiv := isequiv_unique_subuniverse (O nj (a = a; istrunc_paths T .2 a a)) (O nj (b = a; istrunc_paths T .2 b a)))). unfold Sect in rew; simpl in rew; unfold pr1_path in rew.
      rewrite rew; clear rew.

      assert (rew := eissect _ (IsEquiv := isequiv_truncn_unique (O nj (a = a; istrunc_paths T .2 a a)).1 (O nj (b = a; istrunc_paths T .2 b a)).1)). unfold Sect in rew; simpl in rew; unfold pr1_path in rew.
      rewrite rew; clear rew.

      unfold path_universe_uncurried.
      assert (rew := equal_equiv_inv (eisretr _ (IsEquiv := isequiv_equiv_path ((O nj (a = a; istrunc_paths T .2 a a)) .1) .1 ((O nj (b = a; istrunc_paths T .2 b a)) .1) .1)

                                              {|
                                                equiv_fun := kpsic_func_univ_func a b x
                                                                                  (λ x0 y : separated_Type T,
                                                                                            subset_is_subobject
                                                                                              (λ a0 : (T .1 → subuniverse_Type nj;
                                                                                                       T_nType_j_Type_trunc T) .1,
                                                                                                      istrunc_truncation -1
                                                                                                                         (hfiber
                                                                                                                            (λ t t' : T .1,
                                                                                                                                      O nj (t = t'; istrunc_paths T .2 t t')) a0))
                                                                                              x0 y) a;
                                                equiv_isequiv := isequiv_adjointify
                                                                   (kpsic_func_univ_func a b x
                                                                                         (λ x0 y : separated_Type T,
                                                                                                   subset_is_subobject
                                                                                                     (λ a0 : (T .1 → subuniverse_Type nj;
                                                                                                              T_nType_j_Type_trunc T) .1,
                                                                                                             istrunc_truncation -1
                                                                                                                                (hfiber
                                                                                                                                   (λ t t' : T .1,
                                                                                                                                             O nj
                                                                                                                                               (t = t'; istrunc_paths T .2 t t'))
                                                                                                                                   a0)) x0 y) a)
                                                                   (kpsic_func_univ_inv a b x
                                                                                        (λ x0 y : separated_Type T,
                                                                                                  subset_is_subobject
                                                                                                    (λ a0 : (T .1 → subuniverse_Type nj;
                                                                                                             T_nType_j_Type_trunc T) .1,
                                                                                                            istrunc_truncation -1
                                                                                                                               (hfiber
                                                                                                                                  (λ t t' : T .1,
                                                                                                                                            O nj
                                                                                                                                              (t = t'; istrunc_paths T .2 t t'))
                                                                                                                                  a0)) x0 y) a)
                                                                   (fst
                                                                      (kpsic_func_univ_eq a b x
                                                                                          (λ x0 y : separated_Type T,
                                                                                                    subset_is_subobject
                                                                                                      (λ a0 : (T .1 → subuniverse_Type nj;
                                                                                                               T_nType_j_Type_trunc T) .1,
                                                                                                              istrunc_truncation -1
                                                                                                                                 (hfiber
                                                                                                                                    (λ t t' : T .1,
                                                                                                                                              O nj
                                                                                                                                                (t = t';
                                                                                                                                                 istrunc_paths T .2 t t')) a0))
                                                                                                      x0 y) a))
                                                                   (snd
                                                                      (kpsic_func_univ_eq a b x
                                                                                          (λ x0 y : separated_Type T,
                                                                                                    subset_is_subobject
                                                                                                      (λ a0 : (T .1 → subuniverse_Type nj;
                                                                                                               T_nType_j_Type_trunc T) .1,
                                                                                                              istrunc_truncation -1
                                                                                                                                 (hfiber
                                                                                                                                    (λ t t' : T .1,
                                                                                                                                              O nj
                                                                                                                                                (t = t';
                                                                                                                                                 istrunc_paths T .2 t t')) a0))
                                                                                                      x0 y) a)) |}
                                     )
             ). unfold Sect in rew. simpl in rew.

      apply (transport (λ u, (u (O_unit nj (a = a; istrunc_paths T .2 a a) 1)) = (transport idmap
                                                                                            (ap pr1
                                                                                                (ap pr1
                                                                                                    (ap (O nj)
                                                                                                        (truncn_unique fs (a = b; istrunc_paths T .2 a b)
                                                                                                                       (b = a; istrunc_paths T .2 b a) (equal_inverse a b))))) x)) rew^); clear rew.

      
      unfold kpsic_func_univ_func, δ. simpl.

      pose (foo := ap10 (O_rec_retr (a = a; istrunc_paths T .2 a a) (O nj (b = a; istrunc_paths T .2 b a)) (λ u : a = a,
                                                                                                                  O_rec (a = b; istrunc_paths T .2 a b)
                                                                                                                        (O nj (b = a; istrunc_paths T .2 b a))
                                                                                                                        (λ v : a = b, O_unit nj (b = a; istrunc_paths T .2 b a) (v ^ @ u)) x)) 1).
      unfold compose in foo; simpl in foo.
      apply (transport (λ u, u = _) foo^); clear foo.

      apply ap10.

      apply (@equiv_inj _ _ _ (O_equiv nj (a = b; istrunc_paths T .2 a b) (O nj (b = a; istrunc_paths T .2 b a)))).
      rewrite O_rec_retr.
      apply path_forall; intro v. simpl in v.
      transitivity (O_unit nj (b = a; istrunc_paths T .2 b a) (v ^)).
      apply ap. apply concat_p1.
      unfold compose; simpl.

      pose (foo := kpsic_aux).
      specialize (foo (a = b; istrunc_paths T .2 a b) (b = a; istrunc_paths T .2 b a) v (equal_inverse a b)).
      transitivity (O_unit nj (b = a; istrunc_paths T .2 b a)
                           (transport idmap (equal_inverse a b) v)); try exact foo.
      apply ap. unfold equal_inverse. unfold path_universe_uncurried.
      exact (ap10 (equal_equiv_inv (eisretr _ (IsEquiv := isequiv_equiv_path (a = b) (b = a)) {|
                                              equiv_fun := inverse;
                                              equiv_isequiv := isequiv_adjointify inverse inverse
                                                                                  (λ u : b = a,
                                                                                         match u as p in (_ = y) return ((p ^) ^ = p) with
                                                                                           | 1 => 1
                                                                                         end)
                                                                                  (λ u : a = b,
                                                                                         match u as p in (_ = y) return ((p ^) ^ = p) with
                                                                                           | 1 => 1
                                                                                         end) |})) v)^.
    - intro p.
      simpl.
      unfold separated_unit, toIm in p. simpl in p.

      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_eq_dep_subset
                                                     (λ a0 : T .1 → subuniverse_Type nj,
                                                             istrunc_truncation -1
                                                                                   (hfiber (λ t t' : T .1, O nj (t = t'; istrunc_paths T.2 t t')) a0))
                                                     (λ t' : T .1, O nj (a = t'; istrunc_paths T.2 a t');
                                                      tr (a; 1))
                                                     (λ t' : T .1, O nj (b = t'; istrunc_paths T.2 b t');
                                                      tr (b; 1))
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

      apply (@equiv_inj _ _ _ (isequiv_equiv_path _ _)); unfold path_universe_uncurried; rewrite eisretr.

      apply equal_equiv.
      unfold kpsic_func_univ_func, δ. simpl.

      apply (@equiv_inj _ _ _ (O_equiv nj (a = t; istrunc_paths T.2 a t) (O nj (b = t; istrunc_paths T.2 b t)))).
      rewrite (O_rec_retr).
      apply path_forall; intro u. simpl in *.

      unfold δ; simpl.
      unfold compose; simpl. destruct u.
      unfold ap10, pr1_path.

      transitivity (function_lift nj (a = b; istrunc_paths T.2 a b) (b = a; istrunc_paths T.2 b a) (transport idmap (equal_inverse a b)) (transport idmap (equiv_nj_inverse nj T a b) ^
                                                                                                                                          (transport idmap (ap pr1 (ap pr1 (apD10 (ap pr1 p) a)))
                                                                                                                                                     (O_unit nj (a = a; istrunc_paths T.2 a a) 1)))).

      unfold function_lift. apply (ap (λ u, O_rec (a = b; istrunc_paths T.2 a b) (O nj (b = a; istrunc_paths T.2 b a)) u (transport idmap (equiv_nj_inverse nj T a b) ^
                                                                                                                          (transport idmap (ap pr1 (ap pr1 (apD10 (ap pr1 p) a)))
                                                                                                                                     (O_unit nj (a = a; istrunc_paths T.2 a a) 1))))).
      apply path_forall; intro v. apply ap. hott_simpl.
      unfold equal_inverse.
      unfold path_universe_uncurried.
      unfold equiv_inv.
      destruct (isequiv_equiv_path (a = b) (b = a)). unfold Sect in *. unfold equiv_path in *. simpl in *. clear eisadj.
      specialize (eisretr  {|
                      equiv_fun := inverse;
                      equiv_isequiv := isequiv_adjointify inverse inverse
                                                          (λ u : b = a,
                                                                 match
                                                                   u as p0 in (_ = y) return ((p0 ^) ^ = p0)
                                                                 with
                                                                   | 1 => 1
                                                                 end)
                                                          (λ u : a = b,
                                                                 match
                                                                   u as p0 in (_ = y) return ((p0 ^) ^ = p0)
                                                                 with
                                                                   | 1 => 1
                                                                 end) |}). simpl in eisretr.

      pose (bar := equal_equiv_inv eisretr). simpl in bar.
      rewrite bar.
      exact 1.
      

      transparent assert (X : ((function_lift nj (a = b; istrunc_paths T.2 a b)
                                 (b = a; istrunc_paths T.2 b a) (transport idmap (equal_inverse a b))) = transport idmap (equiv_nj_inverse nj T a b))).

      { assert (foo := function_lift_transport).
        specialize (foo n nj ua fs (a = b; istrunc_paths T.2 a b) (b = a; istrunc_paths T.2 b a)).
        specialize (foo
                      (truncn_unique fs (a = b; istrunc_paths T.2 a b)
                                     (b = a; istrunc_paths T.2 b a)
                                     (equal_inverse a b))).
        simpl in foo.

        assert (bar := ap (equiv_inv (IsEquiv := isequiv_path_universe)) foo).
        unfold path_universe in bar.
        rewrite eissect in bar.
        simpl in bar. unfold compose in bar; simpl in bar.

        assert (baar := equal_equiv_inv bar). simpl in baar.

        clear foo; clear bar.

        unfold equiv_nj_inverse. simpl. unfold pr1_path in *. simpl in *.
        etransitivity; try exact baar^. clear baar.
        apply ap. apply ap.
        unfold truncn_unique. unfold eq_dep_subset.

        (* unfold path_sigma'. *)
        pose (rew := @pr1_path_sigma). unfold pr1_path in rew. rewrite rew. exact 1. }

      apply (transport (λ u, u (transport idmap (equiv_nj_inverse nj T a b) ^
                                (transport idmap (ap pr1 (ap pr1 (apD10 (ap pr1 p) a)))
                                           (O_unit nj (a = a; istrunc_paths T.2 a a) 1))) = transport idmap (ap pr1 (ap pr1 (apD10 (ap pr1 p) a)))
                                                                                                      (O_unit nj (a = a; istrunc_paths T.2 a a) 1)) X^).
      rewrite transport_pV. exact 1.
  Qed.

  Lemma hPullback_separated_unit_is_cl_diag (T:Trunk (n.+1)) (k:nat)
  : (hPullback n (separated_unit T) (S k) (@separated_Type_is_Trunk_Sn T) T.2)
    <~> {y : hProduct T.1 (S k) & (@cl_char_hPullback T T idmap k y).1}.
      (* Set Printing Universes.  *)
    simpl.
    apply equiv_functor_sigma_id.
    intros P.
    simpl.
    rewrite cl_char_hPullback_is_'.
    induction k.
    - simpl. apply (equiv_adjointify idmap idmap (λ _, 1) (λ _,1)).
    - simpl. destruct P as [a [b P]].
      apply equiv_functor_prod'. simpl.
      pose (separated_unit_paths_are_nj_paths T a b).
      admit.
      apply IHk.
  Defined.

  Definition Cech_nerve_separated_unit T
    := Cech_nerve_diagram n (separated_unit T) (@separated_Type_is_Trunk_Sn T) T.2.

  Definition cl_diagonal_projections T (k:nat) (p: {p:nat & Peano.le p (S k)})
  : {y : hProduct T.1 (S (S k)) & (@cl_char_hPullback T T idmap (S k) y).1} -> {y : hProduct T.1 (S k) & (@cl_char_hPullback T T idmap k y).1}.
    intro X.
    apply hPullback_separated_unit_is_cl_diag.
    refine (forget_hPullback _ _ _ _ _ _ p).
    exact ((hPullback_separated_unit_is_cl_diag T (S k))^-1 X).
  Defined.

  Definition cl_diagonal_diagram (T:Trunk (trunc_S n)) : diagram (Cech_nerve_graph).
    refine (Build_diagram _ _ _).
    - exact (λ k, {y : hProduct T.1 (S k) & (@cl_char_hPullback T T idmap k y).1}).
    - intros i j [p q] a. simpl in *.
      apply cl_diagonal_projections.
      destruct p. exact q.
      (* exists (nat_interval_to_nat i q). *)
      (* destruct p; apply (nat_interval_bounded i q). *)
      destruct p. exact a.
      (* simpl in *. *)
      (* exact (transport (λ u, ∃ y : T.1 ∧ hProduct T.1 u, (cl_char_hPullback idmap u y).1) p a). *)
  Defined.

  Lemma diagrams_are_equal (T:Trunk (trunc_S n))
  : (Cech_nerve_separated_unit T) = cl_diagonal_diagram T.
    simpl.
    unfold Cech_nerve_separated_unit, Cech_nerve_diagram, cl_diagonal_diagram.
    apply path_diagram.
    transparent assert ( path_type : ((λ n0 : nat,
                ∃ P : T.1 ∧ hProduct T.1 n0,
                (char_hPullback n (separated_unit T) n0
                   (separated_Type_is_Trunk_Sn (T:=T)) T.2 P).1) =
               (λ k : nat,
                ∃ y : T.1 ∧ hProduct T.1 k, (cl_char_hPullback idmap k y).1))).
    - apply path_forall; intro k.
      apply path_universe_uncurried.
      apply hPullback_separated_unit_is_cl_diag.
    - exists path_type. simpl.
      intros i j [p q] [P X]. simpl.
      unfold compose; simpl in *.
      unfold path_type. simpl.
      unfold ap10, path_forall; rewrite eisretr.
      pose (rew := transport_path_universe_V_uncurried (hPullback_separated_unit_is_cl_diag T j) ).
      rewrite rew; clear rew.
      unfold cl_diagonal_projections. rewrite eissect.
      destruct p.

      apply (ap (λ u, forget_hPullback n (separated_unit T) (j.+1) _ T.2 u _)).
      simpl.
      repeat rewrite transport_1.
      pose (rew := transport_path_universe (hPullback_separated_unit_is_cl_diag T (j.+1))).
      rewrite rew; clear rew.
      rewrite eissect.
      reflexivity.

      
      (* apply (ap (λ u, forget_hPullback n (separated_unit T) (j.+1) _ T.2 u _)). *)
      (* destruct p. repeat rewrite transport_1. *)
      (* pose (rew := transport_path_universe (hPullback_separated_unit_is_cl_diag T i)). *)
      (* rewrite rew; clear rew. *)
      (* rewrite eissect. *)
      (* reflexivity. *)
  Qed.

  Definition separated_Type_is_colimit_Cech_nerve (T:Trunk (trunc_S n))
  : (separated_Type T) = colimit (Cech_nerve_separated_unit T)
    := (path_universe_uncurried (GiraudAxiom n (separated_unit T) (@separated_Type_is_Trunk_Sn T) T.2 (@IsSurjection_toIm _ _ (λ t t' : T.1, O nj (t = t'; istrunc_paths T.2 t t')))))^.

  Definition separated_Type_is_colimit (T:Trunk (trunc_S n))
  : (separated_Type T) = colimit (cl_diagonal_diagram T).
    apply (transport (λ u, _ = colimit u) (diagrams_are_equal T)).
    exact (separated_Type_is_colimit_Cech_nerve T).
  Qed.
  
  Definition sep_eq_inv_Δ (P : Trunk (trunc_S n)) (Q :{T : Trunk (trunc_S n) & separated T})
  : (P .1 → (Q .1) .1) -> (separated_Type P → (Q .1) .1).
    intros f.
    destruct Q as [Q sepQ]; unfold separated in sepQ. 
    rewrite (separated_Type_is_colimit).
    refine (colimit_rectnd _ _ _ _ _).
    - simpl in *. intros i. 
      induction i as [| i fi].
      + simpl in *. exact (λ X, f (fst X.1)).
      + simpl in *. exact (λ X, f (fst X.1)).
    - intros i j [p [q Hq]]; simpl in *.
      destruct p. simpl.
      intros [[a [b x]] X].
      induction j.
      + simpl.
        induction q. simpl in x. destruct x.   
        unfold forget_hPullback.
        unfold forget_pullback'. hott_simpl.
        unfold hPullbacks_are_same. simpl.
        unfold equiv_functor_sigma', equiv_functor_sigma. simpl. hott_simpl.
        rewrite transport_path_universe_uncurried.
        (* unfold path_universe_uncurried. simpl. *)
        pose @transport_path_universe_V_uncurried.
        unfold path_universe in p.
        rewrite p.
      
      destruct p.
      (* intro x. *)
      (* destruct x as [[a x] X]. simpl in *. *)
      
      apply ap10.
      apply (transport (λ u, _ = nat_rect _ _
                    (λ (i0 : nat)
                       (_ : (∃ y : P.1 ∧ hProduct P.1 i0, (cl_char_hPullback idmap i0 y).1)
                            → Q.1)
                       (X : ∃ y : P.1 ∧ P.1 ∧ hProduct P.1 i0,
                              (cl_char_hPullback idmap i0.+1 y).1), f (fst X.1)) u) p^). 
        
      apply path_forall; intro x. simpl in x.
      unfold nat_interval_bounded.

      destruct x as [[[a b] x] P].
      simpl in *. 
      simpl.
      
      

      
        path_via (((λ (i0 : nat)
      (_ : (∃ y : P.1 ∧ hProduct P.1 i0, (cl_char_hPullback idmap i0 y).1)
           → Q.1)
      (X : ∃ y : P.1 ∧ P.1 ∧ hProduct P.1 i0,
             (cl_char_hPullback idmap i0.+1 y).1), f (fst X.1)) 0 (λ X : ∃ y : P.1 ∧ Unit, (cl_char_hPullback idmap 0 y).1, f (fst X.1))) x).
        admit.
        + simpl in *.
        
        
        
      
      
      assert (((λ i0 : nat,
                       (∃ y : P.1 ∧ hProduct P.1 i0, (cl_char_hPullback idmap i0 y).1) → Q.1) j x)
              =
              ((λ i0 : nat,
      (∃ y : P.1 ∧ hProduct P.1 i0, (cl_char_hPullback idmap i0 y).1) → Q.1) j x)).
      induction i, j.
      + simpl in *. destruct q.
      + simpl in *. destruct q.
      + simpl in *.
        assert (X : i= 0). rewrite Peano.pred_Sn. rewrite (Peano.pred_Sn i).
        apply ap. exact p.
        unfold forget_hPullback, forget_pullback'. simpl in *.
        induction X.
        destruct X.
        
        

        assert (pp := ap Peano.pred p). simpl in pp. destruct pp.
        


        
              specialize (sepQ (∃ y : P.1 ∧ hProduct P.1 i, (cl_char_hPullback idmap i y).1) (@dense_into_cloture _ _ (P.1 ∧ hProduct P.1 i) (char_hPullback _ idmap i P.2 P.2))).
      unfold E_to_χ_map, compose in sepQ. simpl in sepQ.
      unfold IsMono in sepQ. simpl in sepQ.
        specialize (sepQ (λ y, f (fst y.1)) (λ y, f (fst (snd y.1)))).
        destruct sepQ as [inv retr sect _]. simpl in *.
        unfold compose in inv; simpl in inv.
        assert ((λ
         x : ∃
             (b : ∃ y : P.1 ∧ P.1 ∧ hProduct P.1 i,
                  (cl_char_hPullback idmap i.+1 y).1)
             (π : fst b.1 = fst (snd b.1)
                  ∧ (char_hPullback n idmap i P.2 P.2 (snd b.1)).1),
             O_unit sheaf_def_and_thm.nj
               (fst b.1 = fst (snd b.1)
                ∧ (char_hPullback n idmap i P.2 P.2 (snd b.1)).1;
               λ
               x
                y : fst b.1 = fst (snd b.1)
                    ∧ (char_hPullback n idmap i P.2 P.2 (snd b.1)).1,
               trunc_equiv (path_prod_uncurried x y)) π = b.2,
         f (fst (x.1).1)) =
        (λ
         x : ∃
             (b : ∃ y : P.1 ∧ P.1 ∧ hProduct P.1 i,
                  (cl_char_hPullback idmap i.+1 y).1)
             (π : fst b.1 = fst (snd b.1)
                  ∧ (char_hPullback n idmap i P.2 P.2 (snd b.1)).1),
             O_unit sheaf_def_and_thm.nj
               (fst b.1 = fst (snd b.1)
                ∧ (char_hPullback n idmap i P.2 P.2 (snd b.1)).1;
               λ
               x
                y : fst b.1 = fst (snd b.1)
                    ∧ (char_hPullback n idmap i P.2 P.2 (snd b.1)).1,
               trunc_equiv (path_prod_uncurried x y)) π = b.2,
         f (fst (snd (x.1).1)))).
      
        




    
    apply (equiv_inv (IsEquiv := separated_unit_coeq_Δ P Q.1.1)).
    exists f.
    destruct Q as [Q sepQ].
    unfold separated in sepQ.
    unfold inj1, inj2. unfold compose; simpl in *.
    specialize (sepQ (clΔ P).1). unfold E_to_χ_map in sepQ. simpl in sepQ.
    specialize (sepQ (dense_into_cloture (δ P))).
    unfold IsMono, clδ, δ, compose in sepQ; simpl in sepQ.
    specialize (sepQ (λ X, f (fst X.1)) (λ X, f (snd X.1))).
    destruct sepQ as [inv _ _ _].

    specialize (inv (path_forall _ _ (λ x, ap f x.2.1))).
    apply ap10 in inv.

    apply path_forall; intro x.
    unfold kernel_pair, pullback in x.
    exact (inv x). 
  Defined.

  (* Definition sep_eq_inv (P : Trunk (trunc_S n)) (Q :{T : Trunk (trunc_S n) & separated T}) *)
  (* : (P .1 → (Q .1) .1) -> (separated_Type P → (Q .1) .1). *)
  (*   intros f. *)
  (*   apply (equiv_inv (IsEquiv := separated_unit_coeq P Q.1.1)). *)
  (*   exists f. *)
  (*   destruct Q as [Q sepQ]. *)
  (*   unfold separated in sepQ. *)
  (*   unfold inj1, inj2. unfold compose; simpl in *. *)
  (*   specialize (sepQ (clΔ P).1). unfold E_to_χ_map in sepQ. simpl in sepQ. *)
  (*   specialize (sepQ (dense_into_cloture (δ P))). *)
  (*   unfold IsMono, clδ, δ, compose in sepQ; simpl in sepQ. *)
  (*   specialize (sepQ (λ X, f (fst X.1)) (λ X, f (snd X.1))). *)
  (*   destruct sepQ as [inv _ _ _]. *)

  (*   specialize (inv (path_forall _ _ (λ x, ap f x.2.1))). *)
  (*   apply ap10 in inv. *)

  (*   apply path_forall; intro x. *)
  (*   unfold kernel_pair, pullback in x. exact (inv ((x.1,x.2.1) ; transport idmap (ap10 x.2.2 x.2.1)..1..1^ (O_unit nj (x.2.1 = x.2.1; istrunc_paths P .2 x.2.1 x.2.1) 1) )). *)
  (* Defined. *)

  Definition separated_equiv_Δ : forall (P : Trunk (trunc_S n)) (Q :{T : Trunk (trunc_S n) & separated T}),
                                   IsEquiv (fun f : separated_Type P -> pr1 (pr1 Q) =>
                                              f o (separated_unit P)).
    (* cf proof_separation_universal.prf *)
  Admitted.

   
  Definition separated_equiv : forall (P : Trunk (trunc_S n)) (Q :{T : Trunk (trunc_S n) & separated T}),
                                 IsEquiv (fun f : separated_Type P -> pr1 (pr1 Q) =>
                                           f o (separated_unit P)).
  Admitted.
      

  Definition separation_reflective_subuniverse
  : subuniverse_struct (trunc_S n)
    := (Build_subuniverse_struct
          (λ T, existT (λ T, IsHProp T) (separated T) (separated_is_HProp (T:=T)))
          separation
          separated_unit
          separated_equiv_Δ).
      
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
    apply path_universe_uncurried.
    exists (closure_naturality_fun _ _).
    apply (isequiv_adjointify _ _ (closure_naturality_retr _ _) (closure_naturality_sect _ _)).
  Defined.

  Definition cloture_fun
        (E : Type)
        (P : E -> J)
        (Q : E -> Trunk n)
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
        (Q : E -> Trunk n)
        (f : forall e:E, (P e).1.1 -> (Q e).1)
  :forall (e : {e:E | (P e).1.1}), pr2 (cloture_fun P Q f (pr1 e; nj.(O_unit) (pr1 (pr1 (P (pr1 e))); IsHProp_IsTrunc (pr2 (pr1 (P (pr1 e)))) n0) (pr2 e))) = nj.(O_unit) (Q (pr1 e)) ((f (pr1 e) (pr2 e)))
    := λ e, ap10 (eisretr _ (IsEquiv := (O_equiv nj (((P e .1) .1) .1; IsHProp_IsTrunc ((P e .1) .1) .2 n0) (O nj (Q e .1)))) (λ X, nj.(O_unit) _ (f _ X))) (e.2).

  Lemma cloture_fun_
        (E : Type)
        (P : E -> J)
        (Q : E -> Trunk n)
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
             (A : Trunk (trunc_S n))
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
             (A : Trunk (trunc_S n))
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
        (A : Trunk (trunc_S n))
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
             (A : Trunk (trunc_S n))
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
             (A : Trunk (trunc_S n))
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
    unfold closed_to_sheaf_inv, E_to_χmono_map, nsub_to_char, compose, hfiber, O_rec in *; simpl in *.

    destruct (@snd (separated
            (@proj1_sig (Trunk (trunc_S n))
               (fun T : Trunk (trunc_S n) => Snsheaf_struct T) B)) (forall (E0 : Type) (χ0 : forall _ : E0, J),
          @IsEquiv
            (forall _ : E0,
             @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
               (@proj1_sig (Trunk (trunc_S n))
                  (fun T : Trunk (trunc_S n) => Snsheaf_struct T) B))
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
               (@proj1_sig (Trunk (trunc_S n))
                  (fun T : Trunk (trunc_S n) => Snsheaf_struct T) B))
            (fun
               (f : forall _ : E0,
                    @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
                      (@proj1_sig (Trunk (trunc_S n))
                         (fun T : Trunk (trunc_S n) => Snsheaf_struct T) B))
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
                        (χ0 b0))) t))) (@projT2 (Trunk (trunc_S n))
         (fun T : Trunk (trunc_S n) => Snsheaf_struct T)
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
             (A : Trunk (trunc_S n))
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
            (@proj1_sig (Trunk (trunc_S n))
               (fun T : Trunk (trunc_S n) => Snsheaf_struct T) B)) (forall (E0 : Type) (χ0 : forall _ : E0, J),
          @IsEquiv
            (forall _ : E0,
             @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
               (@proj1_sig (Trunk (trunc_S n))
                  (fun T : Trunk (trunc_S n) => Snsheaf_struct T) B))
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
               (@proj1_sig (Trunk (trunc_S n))
                  (fun T : Trunk (trunc_S n) => Snsheaf_struct T) B))
            (fun
               (f : forall _ : E0,
                    @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
                      (@proj1_sig (Trunk (trunc_S n))
                         (fun T : Trunk (trunc_S n) => Snsheaf_struct T) B))
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
                        (χ0 b0))) t))) (@projT2 (Trunk (trunc_S n))
         (fun T : Trunk (trunc_S n) => Snsheaf_struct T)
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

  Definition closed_to_sheaf (A:Trunk (trunc_S n)) (B:SnType_j_Type) (m : {f : (pr1 A) -> (pr1 (pr1 B)) & forall b, IsTrunc n (hfiber f b)})
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
  
  Definition separated_to_sheaf_IsTrunc_Sn (T U : Trunk (trunc_S n)) m Monom :
    IsTrunc (trunc_S n) (@separated_to_sheaf_Type T.1 U.1 m Monom).
    apply (@trunc_sigma _ (fun P => _)).
    exact (U.2).
    intro a.
    apply (@trunc_succ _ _).
    exact (pr2 (pr1 (nj.(O) (nsub_to_char n (T.1; (m ; mono_is_hfiber Monom)) a)))).
  Defined.
  
  Definition separated_to_sheaf (T:{T : Trunk (trunc_S n) & separated T}) (U:SnType_j_Type) m Monom :
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
    apply path_ishprop.
  Defined.
  
  Definition IsMono_fromIm {A B} (f : A -> B) : IsMono (fromIm (f:=f)). 
    intros x y; apply (isequiv_adjointify (ap (fromIm (f:=f))) (IsMono_fromIm_inv x y)).
    - intro a.
      destruct x as [x s]; destruct y as [y r]; simpl in *.
      destruct a; simpl in *.     unfold IsMono_fromIm_inv. simpl.
      destruct (path_ishprop s r); simpl in *.
      reflexivity.
    - intro a.
      unfold IsMono_fromIm_inv, path_ishprop, center.
      destruct a, x as [x s]; simpl.
      destruct (istrunc_truncation -1 (hfiber f x) s s) as [center contr].
      rewrite (contr idpath); reflexivity.
  Defined.

  Definition sheafification_Type (T:Trunk (trunc_S n)) :=
    @separated_to_sheaf_Type (separated_Type T) 
                             (T.1 -> subuniverse_Type nj) (fromIm (f:=_)) 
                             (IsMono_fromIm (f:=_)).

  Definition sheafification_istrunc (T:Trunk (trunc_S n)) : 
    IsTrunc (trunc_S n) (sheafification_Type T).
    apply (separated_to_sheaf_IsTrunc_Sn (separated_Type T; separated_Type_is_Trunk_Sn (T:=T)) 
                              (T.1 -> subuniverse_Type nj; T_nType_j_Type_trunc T)).
  Defined.

  Definition sheafification_trunc (T:Trunk (trunc_S n)) : Trunk (trunc_S n) :=
    (sheafification_Type T ; sheafification_istrunc  (T:=T)). 

  Definition sheafification_ (T:Trunk (trunc_S n)) : Snsheaf_struct (sheafification_trunc T) :=
    separated_to_sheaf (separated_Type T; separated_Type_is_Trunk_Sn (T:=T)) (T_nType_j_Type_sheaf T) (IsMono_fromIm (f:=_)).

  Definition sheafification (T:Trunk (trunc_S n)) : SnType_j_Type :=
    ((sheafification_Type T ; sheafification_istrunc  (T:=T)); sheafification_ T).

  