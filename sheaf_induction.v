Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import lemmas epi_mono equivalence univalence sub_object_classifier reflective_subuniverse modalities.
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
Arguments trunc_forall {H} {A} {P} {n} H0: simpl never. 
Arguments istrunc_paths {A} {n} H x y: simpl never.
Arguments truncn_unique _ {n} A B H: simpl never.
Arguments isequiv_functor_sigma {A P B Q} f {H} g {H0}: simpl never.
                        
Section Sheafification.

  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  
  Local Definition n0 := sheaf_def_and_thm.n0.
  Local Definition n := sheaf_def_and_thm.n.
  Local Definition mod_nj := sheaf_def_and_thm.mod_nj.
  Local Definition nj := sheaf_def_and_thm.nj.
  Local Definition j_is_nj := sheaf_def_and_thm.j_is_nj.
  Local Definition j_is_nj_unit := sheaf_def_and_thm.j_is_nj_unit.
  Local Definition islex_mod_nj := sheaf_def_and_thm.islex_mod_nj.
  Local Definition islex_nj := sheaf_def_and_thm.islex_nj.
  Local Definition lex_compat := sheaf_def_and_thm.lex_compat.

  (* Definition of □T *)
  Definition separated_Type (T:Trunk (trunc_S n)) : Type :=
    Im (λ t : pr1 T, λ t', nj.(O) (t = t'; istrunc_paths T.2 t t')).

  Definition sheaf_is_separated (T : SnType_j_Type) : separated T.1 := fst (T.2).
 
  Definition separated_Type_is_Trunk_Sn (T:Trunk (trunc_S n)) : IsTrunc (trunc_S n) (separated_Type T).
    unfold separated_Type; simpl.
    destruct T as [T TrT]; simpl in *.
    apply (@trunc_sigma _ (fun P => _)). 
    apply (@trunc_forall _ _ (fun P => _)). intro. 
    exact (@subuniverse_Type_is_TrunkSn _ nj ua).
    intro φ. exact (IsHProp_IsTrunc (istrunc_truncation _ _) n). 
  Defined.

  Definition E_to_χ_map_ap (T U:Trunk (trunc_S n)) E (χ : EnJ E) (f : E -> (pr1 T))
             (g : pr1 T -> pr1 U) x y (e : x = y) : 
    ap (fun u => g o u) (ap (E_to_χ_map T χ) e) = ap (E_to_χ_map U χ) (ap (fun u => g o u) e).
    destruct e; reflexivity.
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

  (* Lemma 28 *)
  Definition separated_mono_is_separated (T U:Trunk (trunc_S n)) (H:separated U) (f: pr1 T -> pr1 U) (fMono : IsMonof f) : separated T.
    intros E χ x y.
    refine (separated_mono_is_separated_ _ (H E χ (f o x) (f o y)) fMono).
  Defined.

  Definition T_nType_j_Type_trunc (T:Trunk (trunc_S n)) : IsTrunc (trunc_S n) (pr1 T -> subuniverse_Type nj).
    apply (@trunc_forall _ _ (fun P => _)). intro. 
    apply (@trunc_sigma _ (fun P => _)). apply Tn_is_TSn.
    intro. apply IsHProp_IsTrunc. exact (pr2 (subuniverse_HProp nj a0)).
  Defined.

  Definition T_nType_j_Type_isSheaf : forall T, Snsheaf_struct (pr1 T -> subuniverse_Type nj;
                                                    T_nType_j_Type_trunc T).
    intro.
    apply (dep_prod_SnType_j_Type (fun x:pr1 T => ((existT (IsTrunc (n.+1)) (subuniverse_Type nj) (@subuniverse_Type_is_TrunkSn _ nj ua));nType_j_Type_is_SnType_j_Type))).
  Defined.

  (* For any type [T], [T -> subuniverse_Type] is modal *)
  Definition T_nType_j_Type_sheaf T : SnType_j_Type :=  ((pr1 T -> subuniverse_Type nj; T_nType_j_Type_trunc T); T_nType_j_Type_isSheaf _).

  (* Proposition 27 *)
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

  Definition mu_modal_paths_func_univ_func
             (T : Trunk (trunc_S n))
             (a : T .1)
             (b : T .1)
             (p : ((clδ T) (a, b)) .1)
             (t : T .1)
  : ((O nj (a = t; istrunc_paths T.2 a t)) .1) .1 ->
    ((O nj (b = t; istrunc_paths T.2 b t)) .1) .1.
    apply O_rec; intro u.
    generalize dependent p; apply O_rec; intro v. apply (O_unit nj).
    exact (v^@u).
  Defined.

  Definition mu_modal_paths_func_univ_inv
             (T : Trunk (trunc_S n))
             (a : T .1)
             (b : T .1)
             (p : ((clδ T) (a, b)) .1)
             (t : T .1)
  : ((O nj (b = t; istrunc_paths T.2 b t)) .1) .1 ->
    ((O nj (a = t; istrunc_paths T.2 a t)) .1) .1 .
    apply O_rec; intro u.
    generalize dependent p; apply O_rec; intro v; apply (O_unit nj).
    exact (v@u).
  Defined.

  Lemma mu_modal_paths_func_univ_eq
        (T : Trunk (trunc_S n))
        (a : T .1)
        (b : T .1)
        (p : (clδ T (a, b)) .1)
        (t : T .1)
  : (Sect (mu_modal_paths_func_univ_inv T a b p t) (mu_modal_paths_func_univ_func T a b p t))
    /\ (Sect (mu_modal_paths_func_univ_func T a b p t) (mu_modal_paths_func_univ_inv T a b p t)).
    split.
    - intro x.
      unfold mu_modal_paths_func_univ_inv, mu_modal_paths_func_univ_func, δ; simpl. unfold clδ, δ in p; simpl in p.
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
    - intro x. unfold mu_modal_paths_func_univ_inv, mu_modal_paths_func_univ_func, δ. simpl.
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

  Arguments mu_modal_paths_func_univ_eq : default implicits, simpl never.

    Lemma mu_modal_paths_aux (A B:Trunk n) (v:A.1) (eq : A.1 = B.1)
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
    simpl. reflexivity.
    Defined.

  Definition separated_unit_paths_are_nj_paths_fun T (a b:T.1) : (separated_unit T a = separated_unit T b) -> (O nj (a=b; istrunc_paths T.2 a b)).1.1.
    intro p.
    unfold separated_unit, toIm in p. simpl in p.
    pose (p' := (ap10 p..1 b)..1..1). simpl in p'.
    apply (transport idmap p'^). apply O_unit. reflexivity.
  Defined.

  Definition separated_unit_paths_are_nj_paths_inv T (a b:T.1) : (O nj (a=b; istrunc_paths T.2 a b)).1.1 -> (separated_unit T a = separated_unit T b).
    intro p.
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
    symmetry.
    apply path_universe_uncurried.
    exists (mu_modal_paths_func_univ_inv T a b p t).
    apply isequiv_adjointify with (g := mu_modal_paths_func_univ_func T a b p t);
      [exact (snd (mu_modal_paths_func_univ_eq T a b p t)) | exact (fst (mu_modal_paths_func_univ_eq T a b p t))].
    exact (@equiv_inv _ _ _ (X (separated_unit T a) (separated_unit T b)) X0).
  Defined.

  Lemma separated_unit_paths_are_nj_paths_retr T (a b:T.1)
  : Sect (separated_unit_paths_are_nj_paths_inv T a b) (separated_unit_paths_are_nj_paths_fun (b:=b)).
    unfold separated_unit_paths_are_nj_paths_fun, separated_unit_paths_are_nj_paths_inv.

      intro x.
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

      assert (rew := eissect _ (IsEquiv := isequiv_unique_subuniverse (O nj (a = b; istrunc_paths T.2 a b)) (O nj (b = b; istrunc_paths T.2 b b)))). unfold Sect in rew; simpl in rew; unfold pr1_path in rew.
      rewrite rew; clear rew.

      assert (rew := eissect _ (IsEquiv := isequiv_truncn_unique (O nj (a = b; istrunc_paths T.2 a b)).1 (O nj (b = b; istrunc_paths T.2 b b)).1)). unfold Sect in rew; simpl in rew; unfold pr1_path in rew.
      rewrite rew; clear rew.

      rewrite transport_path_universe_V_uncurried.
     
      unfold mu_modal_paths_func_univ_func, δ. simpl.

      revert x.
      transparent assert (sh : (((O nj (a = b; istrunc_paths T.2 a b)).1).1 -> subuniverse_Type nj)).
      { intro x. refine (exist _ _ _).
        exists (O_unit nj (b = b; istrunc_paths T.2 b b) 1 =
   O_rec (a = b; istrunc_paths T.2 a b) (O nj (b = b; istrunc_paths T.2 b b))
     (λ u : a = b,
      O_rec (a = b; istrunc_paths T.2 a b)
        (O nj (b = b; istrunc_paths T.2 b b))
        (λ v : a = b, O_unit nj (b = b; istrunc_paths T.2 b b) (v^ @ u)) x) x).
        apply istrunc_paths; apply trunc_succ; exact _.2.
        apply subuniverse_paths; [exact ua | exact fs]. }
      refine (O_rec_dep _ sh _).1.
      unfold sh; clear sh; intro x; simpl.
              
      pose (foo := λ P Q f, ap10 (O_rec_retr (subU := nj) P Q f)).
      simpl in foo.
      rewrite foo. rewrite foo. apply ap. hott_simpl.
  Qed.
  
  Lemma separated_unit_paths_are_nj_paths_sect T (a b:T.1)
  : Sect (separated_unit_paths_are_nj_paths_fun (b:=b)) (separated_unit_paths_are_nj_paths_inv T a b).
    unfold separated_unit_paths_are_nj_paths_fun, separated_unit_paths_are_nj_paths_inv.
      intro p.
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

      path_via (ap pr1 (apD10 (ap pr1 p) t) ..1)^^.
      apply ap. 
      apply (@equiv_inj _ _ _ (isequiv_equiv_path _ _)); unfold path_universe_uncurried; rewrite eisretr. 

      apply equal_equiv.
      unfold mu_modal_paths_func_univ_inv, δ. simpl.

      apply (@equiv_inj _ _ _ (O_equiv nj (b = t; istrunc_paths T.2 b t) (O nj (a = t; istrunc_paths T.2 a t)))).
      rewrite (O_rec_retr).
      apply path_forall; intro u. simpl in *.
      
      destruct u.
      unfold ap10, pr1_path.

      apply (ap10 (g:=idmap)).
      pose (O_rec_sect (a = b; istrunc_paths T.2 a b) (O nj (a = b; istrunc_paths T.2 a b)) idmap). simpl in p0.
      unfold O_rec.
      etransitivity; [idtac | exact p0].
      apply ap. apply path_forall; intro v. apply ap. apply concat_p1.
  Defined.


  (* For any [x,y:T], [(μ x = μ y) = ○ (x = y)] : in proof of Lemma 29 *)
  Theorem separated_unit_paths_are_nj_paths T (a b:T.1) : (separated_unit T a = separated_unit T b) <~> (O nj (a=b; istrunc_paths T.2 a b)).1.1.
  Proof.
    refine (equiv_adjointify _ _ _ _).
    - apply separated_unit_paths_are_nj_paths_fun.
    - apply separated_unit_paths_are_nj_paths_inv.
    - apply separated_unit_paths_are_nj_paths_retr.
    - apply separated_unit_paths_are_nj_paths_sect.
  Qed.

  Lemma O_rec_paths (T:Trunk (trunc_S n)) (a b c :T.1)
  : (O nj (a=b; istrunc_paths T.2 _ _)).1.1 -> (O nj (b=c; istrunc_paths T.2 _ _)).1.1
    -> (O nj (a=c; istrunc_paths T.2 _ _)).1.1.
    intros p q.
    revert p; apply O_rec; intro p.
    revert q; apply O_rec; intro q.
    apply O_unit.
    exact (p@q).
  Defined.

  Lemma separated_unit_paths_are_nj_paths_concat T (a b c:T.1) (p : (separated_unit T a = separated_unit T b)) (q : (separated_unit T b = separated_unit T c))
  : separated_unit_paths_are_nj_paths_fun (p@q)
    = O_rec_paths T a b c (separated_unit_paths_are_nj_paths_fun p) (separated_unit_paths_are_nj_paths_fun q).
    simpl.
    unfold O_rec_paths.
    unfold separated_unit_paths_are_nj_paths_fun. simpl.
    unfold pr1_path.
    path_via (transport idmap (ap pr1 (ap pr1 (ap10 (ap pr1 p) c)) @ ap pr1 (ap pr1 (ap10 (ap pr1 q) c)))^ (O_unit nj (c = c; istrunc_paths T.2 c c) 1)).
    apply (ap (λ u, transport idmap u (O_unit nj (c = c; istrunc_paths T.2 c c) 1))).
    apply ap; repeat (try rewrite ap_pp; try rewrite ap10_pp). reflexivity.

    rewrite inv_pp.
    rewrite transport_pp.

    pose (O_rec_O_rec).
    specialize (p0 n nj fs (a = b; istrunc_paths T.2 a b) (a = c; istrunc_paths T.2 a c) (b = c; istrunc_paths T.2 b c)).
    simpl in p0.    
    specialize (p0 (λ u v, u@v) (λ u v, u@v^)).

  Admitted.
    
  Lemma hPullback_separated_unit_is_cl_diag (T:Trunk (n.+1)) (k:nat)
  : (hPullback n (separated_unit T) (S k) (@separated_Type_is_Trunk_Sn T) T.2)
      <~> {y : hProduct T.1 (S k) & (@cl_char_hPullback' T T idmap k y).1}.
    simpl.
    apply equiv_functor_sigma_id.
    intros P.
    simpl.
    induction k.
    - simpl. apply (equiv_adjointify idmap idmap (λ _, 1) (λ _,1)).
    - simpl.
      apply equiv_functor_prod'. simpl.
      refine (equiv_adjointify (@separated_unit_paths_are_nj_paths_fun T (fst P) (fst (snd P))) (@separated_unit_paths_are_nj_paths_inv T (fst P) (fst (snd P))) _ _).
      apply separated_unit_paths_are_nj_paths_retr.
      apply separated_unit_paths_are_nj_paths_sect.
      apply IHk.
  Defined.

  Definition Cech_nerve_separated_unit T
    := Cech_nerve_diagram n (separated_unit T) (@separated_Type_is_Trunk_Sn T) T.2.

  Definition cl_diagonal_projections T (k:nat) (p: {p:nat & Peano.le p (S k)})
  : {y : hProduct T.1 (S (S k)) & (@cl_char_hPullback' T T idmap (S k) y).1} -> {y : hProduct T.1 (S k) & (@cl_char_hPullback' T T idmap k y).1}.
    intro X.
    exists (forget_hProduct T.1 (S k) X.1 p).
    apply forget_cl_char_hPullback'.
    exact X.2.
  Defined.

  Definition cl_diagonal_diagram (T:Trunk (trunc_S n)) : diagram (Cech_nerve_graph).
    refine (Build_diagram _ _ _).
    - exact (λ k, {y : hProduct T.1 (S k) & (@cl_char_hPullback' T T idmap k y).1}).
    - intros i j [p q] a. simpl in *.
      apply cl_diagonal_projections.
      destruct p. exact q.
      destruct p. exact a.
  Defined.

  (* Lemma 29 *)
  Lemma diagrams_are_equal_types (T:Trunk (trunc_S n))
  : diagram0 (Cech_nerve_separated_unit T) = diagram0 (cl_diagonal_diagram T).
    apply path_forall; intros ?.
    apply path_universe_uncurried.
    apply hPullback_separated_unit_is_cl_diag.
  Defined.

  (* Lemma 29 *)
  Lemma diagrams_are_equal_proj (T:Trunk (trunc_S n))
  : ∀ (i j : Cech_nerve_graph) (x : Cech_nerve_graph i j),
      diagram1 (Cech_nerve_separated_unit T) x ==
      (λ x0 : (Cech_nerve_separated_unit T) i,
              (equiv_path ((cl_diagonal_diagram T) j) ((Cech_nerve_separated_unit T) j)
                          (ap10 (diagrams_are_equal_types T) j)^)
                (diagram1 (cl_diagonal_diagram T) x
                          ((equiv_path ((Cech_nerve_separated_unit T) i)
                                       ((cl_diagonal_diagram T) i)
                                       (ap10 (diagrams_are_equal_types T) i)) x0))).
    intros i j [p [q Hq]] [P X]. simpl.
    destruct p. unfold diagrams_are_equal_types. simpl.
    unfold ap10, path_forall; rewrite eisretr.
    rewrite transport_path_universe_uncurried.
    pose (rew := transport_path_universe_V_uncurried (hPullback_separated_unit_is_cl_diag T j) ).
    rewrite rew; clear rew.
    symmetry; apply moveR_EV; symmetry.
    simpl.
    apply path_sigma' with 1; simpl.
    
    unfold equiv_functor_prod'. unfold functor_prod. simpl.
    unfold forget_hPullback, forget_cl_char_hPullback', forget_char_hPullback. simpl.
    simpl.
    match goal with
      |[|- _ = sum_rect _ _ _ ?d] => induction d as [| a]
    end.
    { destruct a. simpl. reflexivity. }
    { simpl.
      match goal with
        |[|- _ = sum_rect _ _ _ ?d] => induction d as [| b]
      end.
      { destruct a0. simpl.
        induction j.
        { reflexivity. }
        { simpl.
          refine (path_prod _ _ _ _); simpl.
          { reflexivity. }
          { simpl. apply IHj. }
        }
      }
      { simpl.
        symmetry.
        set (p' := neq_0_succ q (neq_symm 0 q a)).
        destruct p' as [p' Hp']. simpl.
        destruct Hp'.
        clear a. 
        generalize dependent j. 
        generalize dependent p'.
        induction p'; simpl.
        {
          intros j Hq P X b.
          set (k := gt_0_succ j (le_pred 2 j.+1 (le_neq_lt 1 j.+1 (neq_symm j.+1 1 b) Hq))).
          destruct k as [k Hk].
          destruct Hk. simpl.
          refine (path_prod _ _ _ _).
          { simpl.
            destruct P as [P1 [P2 [P3 P]]]. 
            destruct X as [X1 [X2 X]]. simpl in *.
            exact (separated_unit_paths_are_nj_paths_concat X1 X2)^. }
          { simpl. reflexivity. }
        }
        {
          intros j Hq P X b.
          set (k := ge_succ_succ p'.+1 j (le_pred p'.+3 j.+1 (le_neq_lt p'.+2 j.+1 (neq_symm j.+1 p'.+2 b) Hq))).
          destruct k as [k Hk]. simpl.
          destruct Hk. simpl.
          refine (path_prod _ _ _ _).
          { reflexivity. }
          { simpl.
            specialize (IHp' k%nat (le_pred p'.+2 k.+2 Hq) (snd P) (snd X) (λ x:(k.+1 = p'.+1)%nat, b (ap S x))).


            set ((le_pred p'.+3 k.+2 (le_neq_lt p'.+2 k.+2 (neq_symm k.+2 p'.+2 b) Hq))) in *.
            set ((le_neq_lt p'.+1 k.+1 (neq_symm k.+1 p'.+1 (λ x:(k.+1 = p'.+1)%nat, b (ap S x))) (le_pred p'.+2 k.+2 Hq))) in *.
            simpl in l, l0.
            assert (rew : l = l0) by admit (* Here should be a proof of IsHProp (n <= m) *).
            destruct rew.
            exact IHp'.
          }
        }
      }
    }
  Defined.
  (* This lemma is obvious on paper, but really painful to formalize. Maybe we should represent hPullback another way... *)

  (* Lemma 29 *)
  Lemma diagrams_are_equal (T:Trunk (trunc_S n))
  : (Cech_nerve_separated_unit T) = cl_diagonal_diagram T.
    (* unfold Cech_nerve_separated_unit, Cech_nerve_diagram, cl_diagonal_diagram. *)
    apply path_diagram.
    refine (exist _ _ _). 
    - apply diagrams_are_equal_types.
    - apply diagrams_are_equal_proj.
  Defined.
  
  Definition separated_Type_is_colimit_Cech_nerve (T:Trunk (trunc_S n))
    := Giraud n (separated_unit T) (@separated_Type_is_Trunk_Sn T) T.2 (@IsSurjection_toIm _ _ (λ t t' : T.1, O nj (t = t'; istrunc_paths T.2 t t'))).

  Definition separated_Type_is_colimit_Cech_nerve' (T:Trunk (trunc_S n))
  := GiraudAxiom n (separated_unit T) (@separated_Type_is_Trunk_Sn T) T.2 (@IsSurjection_toIm _ _ (λ t t' : T.1, O nj (t = t'; istrunc_paths T.2 t t'))).

  Definition diagonal_commute (T:Trunk (trunc_S n))
  : forall i, (cl_diagonal_diagram T) i -> (separated_Type T).
    simpl; intro i.
    intro u.
    apply separated_unit. exact (fst u.1).
  Defined.

  Arguments diagonal_commute T [i] x.

  Definition diagonal_pp (T:Trunk (trunc_S n))
  : forall i j, forall (g : Cech_nerve_graph i j), forall (x : cl_diagonal_diagram T i),
      (@diagonal_commute T) _ (diagram1 (cl_diagonal_diagram T) g x) = (@diagonal_commute T) _ x.
    intros i j [p [q Hq]] x; simpl in *.
    destruct p.
    unfold diagonal_commute. simpl.
    destruct q.
    - simpl. destruct x as [x p]. simpl in p.
      symmetry. 
      apply separated_unit_paths_are_nj_paths_inv.
      exact (fst p).
    - reflexivity.
  Defined.

  Definition separated_Type_is_colimit_cl_diagonal_diagram (T:Trunk (trunc_S n))
  : is_colimit (Cech_nerve_graph)
               (cl_diagonal_diagram T)
               (separated_Type T)
               (diagonal_commute T)
               (@diagonal_pp T).
    (* Here, we would like to use the fact that [separated_Type T] is the colimit of [Cech_nerve_separated_unit], that [p: Cech_nerve_separated_unit = cl_diagonal_diagram], and that commutation in these diagrams are equal modulo [p] *)
  Admitted. 

  Lemma sep_eq_inv_lemma (P : Trunk (trunc_S n)) (Q :{T : Trunk (trunc_S n) & separated T}) (f : P.1 -> Q.1.1)
  : ∀ (i j : Cech_nerve_graph) (f0 : Cech_nerve_graph i j)
      (x : (cl_diagonal_diagram P) i),
      f (fst (diagram1 (cl_diagonal_diagram P) f0 x).1) = f (fst x.1).
    intros i j [p [q Hq]]; destruct p;
    intros [[a [b x]] X];
    destruct q; [
    exact (ap10 (equiv_inv (IsEquiv := Q.2 (∃ y : P.1 ∧ hProduct P.1 (S j), (cl_char_hPullback' idmap (S j) y).1) (cl_char_hPullback'_is_dense P P idmap (S j)) (λ x, f (fst x.1)) (λ x, f (fst (snd x.1))))
                     (path_forall _ _ (λ u, ap f (fst u.2.1)))) ((a,(b,x));X))^ |
    reflexivity].
  Defined.
      
  Definition sep_eq_inv (P : Trunk (trunc_S n)) (Q :{T : Trunk (trunc_S n) & separated T})
  : (P .1 → (Q .1) .1) -> ((separated_Type P) → (Q .1) .1).
    intro f.
    apply (equiv_inv (IsEquiv := (separated_Type_is_colimit_cl_diagonal_diagram P Q.1.1))).
    exists (λ i, λ x, f (fst x.1)).
    apply sep_eq_inv_lemma.
  Defined.

  (* Proposition 30 *)
  Definition separated_equiv : forall (P : Trunk (trunc_S n)) (Q :{T : Trunk (trunc_S n) & separated T}),
                                 IsEquiv (fun f : separated_Type P -> pr1 (pr1 Q) =>
                                            f o (separated_unit P)).
    intros P Q.
    refine (isequiv_adjointify _ _ _ _).
    - apply sep_eq_inv.
    - intros f.
      Opaque sep_eq_inv_lemma.
      apply path_forall; intro x. 

      unfold sep_eq_inv.
      unfold equiv_inv.
      destruct (separated_Type_is_colimit_cl_diagonal_diagram P (Q.1).1) as [inv retr _ _].
      unfold Sect in retr; simpl in retr.
      simpl.
      unfold diagonal_commute in retr.
      specialize (retr (λ (i : nat)
      (x0 : ∃ y : P.1 ∧ hProduct P.1 i, (cl_char_hPullback' idmap i y).1),
                        f (fst x0.1); sep_eq_inv_lemma Q f)).
      exact (ap10 (apD10 (retr..1) 0%nat) ((x,tt);tt)).
    - intros f. unfold sep_eq_inv; simpl.
      apply moveL_equiv_V.
      apply path_sigma' with 1. simpl.
      apply path_forall; intro i.
      apply path_forall; intro j.
      apply path_forall; intros [p [q Hq]].
      apply path_forall; intro x.
      destruct p. simpl in *.
      induction q.
      { Transparent sep_eq_inv_lemma.
        Opaque cl_diagonal_projections.
        Opaque cl_char_hPullback'_is_dense.
        simpl.
        rewrite ap_V. apply VpV.
        destruct x as [[x1 [x2 x]] y]. simpl in *.
        refine (@apD10 _ _ (ap10
                              ((ap (E_to_χ_map Q.1 (cl_char_hPullback'_is_dense P P idmap j.+1)))^-1
                                                                                                 (path_forall
                                                                                                    (λ
                                                                                                       u : ∃
                                                                                                             b : ∃ y0 : P.1 ∧ P.1 ∧ hProduct P.1 j,
                                                                                                                   ((O cloture_hpullback.nj
                                                                                                                       (fst y0 = fst (snd y0);
                                                                                                                        istrunc_paths P.2 (fst y0) (fst (snd y0)))).1).1
                                                                                                                   ∧ (cl_char_hPullback' idmap j (snd y0)).1,
                                                                                                             ((cl_char_hPullback'_is_dense P P idmap j.+1) b).1,
                                                                                                       f (separated_unit P (fst (u.1).1)))
                                                                                                    (λ
                                                                                                       u : ∃
                                                                                                             b : ∃ y0 : P.1 ∧ P.1 ∧ hProduct P.1 j,
                                                                                                                   ((O cloture_hpullback.nj
                                                                                                                       (fst y0 = fst (snd y0);
                                                                                                                        istrunc_paths P.2 (fst y0) (fst (snd y0)))).1).1
                                                                                                                   ∧ (cl_char_hPullback' idmap j (snd y0)).1,
                                                                                                             ((cl_char_hPullback'_is_dense P P idmap j.+1) b).1,
                                                                                                       f (separated_unit P (fst (snd (u.1).1))))
                                                                                                    (λ
                                                                                                       u : ∃
                                                                                                             b : ∃ y0 : P.1 ∧ P.1 ∧ hProduct P.1 j,
                                                                                                                   ((O cloture_hpullback.nj
                                                                                                                       (fst y0 = fst (snd y0);
                                                                                                                        istrunc_paths P.2 (fst y0) (fst (snd y0)))).1).1
                                                                                                                   ∧ (cl_char_hPullback' idmap j (snd y0)).1,
                                                                                                             ((cl_char_hPullback'_is_dense P P idmap j.+1) b).1,
                                                                                                       ap (λ x0 : P.1, f (separated_unit P x0)) (fst (u.2).1)))))
                (λ x, ap f
     (separated_unit_paths_are_nj_paths_inv P (fst x.1) 
                                            (fst (snd x.1)) (fst x.2)))
                _
                ((x1, (x2, x)); y)).
        apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_apD10 _ _ _ _)) _).
        unfold ap10.
        rewrite eissect.
        
        apply moveL_equiv_V.
        apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
        unfold path_forall. rewrite eisretr.
        clear y. clear x. clear x1. clear x2.
        apply path_forall. intros [[[b1 [b2 b]] q] [π p]].
        simpl in *.
        
        unfold E_to_χ_map.
        destruct π as [π μ]. destruct π. simpl in *.

        pose (@apD10_ap_precompose
                (∃
              b0 : ∃ P0 : P.1 ∧ P.1 ∧ hProduct P.1 j,
                   ((O cloture_hpullback.nj
                       (fst P0 = fst (snd P0);
                       istrunc_paths P.2 (fst P0) (fst (snd P0)))).1).1
                   ∧ (cl_char_hPullback' idmap j (snd P0)).1,
              ((cl_char_hPullback'_is_dense P P idmap j.+1) b0).1)
                  (∃ y0 : P.1 ∧ P.1 ∧ hProduct P.1 j, (cl_char_hPullback' idmap j.+1 y0).1)
                  (λ _, Q.1.1)
                  pr1
                  _
                  _
                  (apD10^-1
           (λ
            x : ∃ P0 : P.1 ∧ P.1 ∧ hProduct P.1 j,
                ((O cloture_hpullback.nj
                    (fst P0 = fst (snd P0);
                    istrunc_paths P.2 (fst P0) (fst (snd P0)))).1).1
                ∧ (cl_char_hPullback' idmap j (snd P0)).1,
            ap f
              (separated_unit_paths_are_nj_paths_inv P 
                 (fst x.1) (fst (snd x.1)) (fst x.2))))
                  (((b1, (b1, b)); q); ((1, μ); p))).

        apply (transport (λ u, 1 = u) p0^). clear p0.

        rewrite eisretr. simpl.
        unfold separated_unit_paths_are_nj_paths_inv.
        simpl.
        path_via (ap f (idpath ((separated_unit P b1)))). apply ap.
        apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_eq_dep_subset _ _ _)) _).
        rewrite eissect.
        simpl.
        apply (@equiv_inj _ _ _ (isequiv_ap10 _ _)).
        unfold path_forall, ap10; rewrite eisretr.
        apply path_forall; intro x.
        simpl.
        apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_unique_subuniverse _ _)) _).
        rewrite eissect. simpl.
        apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_truncn_unique _ _)) _).
        rewrite eissect. simpl.
        match goal with
          |[|- ?X = _] => path_via (X^^)
        end.
        apply ap. 
        apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_path_universe)) _).
        rewrite eissect.

        unfold equiv_path; simpl.
        apply equal_equiv.
        unfold mu_modal_paths_func_univ_func. simpl. 
        apply (@equiv_inj  _ _ _ (O_equiv nj _ _)).
        unfold  mu_modal_paths_func_univ_inv.
        rewrite O_rec_retr.
        apply path_forall; intro y.
        unfold δ; simpl.
          
        pose (p0 := ap10 (O_rec_retr (b1 = b1; istrunc_paths P.2 b1 b1) (O nj (b1 = x; istrunc_paths P.2 b1 x)) (λ v : b1 = b1, O_unit nj (b1 = x; istrunc_paths P.2 b1 x) (v @ y))) 1).
        simpl in p0.
        rewrite concat_1p in p0.
        etransitivity; try exact p0^. clear p0.
        apply ap.
        exact (density_lemma_hPullback P P idmap j ((b1,(b1,b)) ; q) ((1,μ);p))^.
      }
      { reflexivity. }
  Qed.
      
  (* Proposition 30 *)
  Definition separation_reflective_subuniverse
  : subuniverse_struct (trunc_S n)
    := Build_subuniverse_struct
          (λ T, existT (λ T, IsHProp T) (separated T) (separated_is_HProp (T:=T)))
          separation
          separated_unit
          separated_equiv.

  Lemma density_sigma (E:Type) (χ : EnJ E) (e:E) (E' := {e':E & e = e'})
  : EnJ {e':E & e' = e}.
    refine (@Build_EnJ _ _ _ _).
    - intro x. apply χ. exact x.1.
    - intros e0.
      pose (dense_eq χ e0.1).
      etransitivity; try exact p.
      apply path_universe_uncurried.
      refine (equiv_adjointify _ _ _ _).
      + intros [e' q]. destruct q. exists e0.1. reflexivity.
      + intros [e' q]. destruct q. exists e0. reflexivity.
      + intros [e' q]. destruct q. reflexivity.
      + intros [e' q]. destruct q. reflexivity.
    - intros e' e''. simpl in *.
      unfold equiv_adjointify.


      apply path_forall; intro u. simpl.
      rewrite transport_pp.


      rewrite transport_path_universe_uncurried.
      unfold incl_Aeq_Eeq. simpl.
      destruct u as [[u11 u12] u2]. simpl in *.
      destruct u2. simpl.

      pose (dense_diag χ).
      unfold incl_Aeq_Eeq in p. simpl in p.
      specialize (p (e'.1.1;e'.2)). simpl in p.
      assert (∃ e'0 : ∃ e0 : E, (χ e0).1, (e'.1).1 = e'0.1).
      refine (exist _ _ _).
      refine (exist _ _ _).
      exact (e'.1.1).
      exact (e'.2).
      simpl. exact 1. specialize (p X). clear X.
      apply ap10 in p. simpl in p.
      specialize (p ((e'.1.1; u12);1)).
      simpl in p. exact p.
  Defined.

  (* Proposition 31 *)
  Definition separated_modality : Modality (trunc_S n).
    refine (Build_Modality _ separation_reflective_subuniverse _).
    intros A B. simpl in *.
    destruct A as [A sepA]. simpl in sepA.
    unfold separated.
    intros E χ f g. simpl in *.
    refine (isequiv_adjointify _ _ _ _).
    - unfold E_to_χ_map; simpl. intros H. simpl in H.
      apply path_forall; intro x.
      refine (path_sigma _ _ _ _ _).
      apply (ap10 (f := (pr1 o f)) (g := (pr1 o g))).
      apply (equiv_inv (IsEquiv := sepA E χ (pr1 o f) (pr1 o g))).
      apply path_forall; intro y. exact (ap10 H y)..1.
      simpl.
      pose (p := (B (g x).1).2).
      simpl in p.
      specialize (p {e':E & e' = x}).
      specialize (p (density_sigma χ x)).

      unfold equiv_inv.
      unfold IsMono in p; simpl in p.
      specialize (p (λ z, transport (λ u, (B (g u).1).1.1) z.2 (transport (λ x0 : A.1, ((B x0).1).1)
                                                                          (ap10
                                                                             ((let (equiv_inv, eisretr, eissect, _) :=
                                                                                   sepA E χ (pr1 o f) (pr1 o g) in
                                                                               equiv_inv)
                                                                                (path_forall (E_to_χ_map A χ (pr1 o f))
                                                                                             (E_to_χ_map A χ (pr1 o g))
                                                                                             (λ y : (nchar_to_sub χ).1, (ap10 H y) ..1))) z.1)
                                                                          (f z.1).2))).
      specialize (p (λ z, transport (λ u, (B (g u).1).1.1) z.2 (g z.1).2)).

      pose (X := λ X, (ap10 (equiv_inv (IsEquiv := p) X) (x;1))); simpl in X; apply X. clear X.
      unfold E_to_χ_map; simpl.
      apply path_forall; intros [[a b] c]; simpl in *.
      apply ap. clear b.

      etransitivity; try exact ((ap10 H (a;c))..2). simpl.
      apply (ap (λ u, transport _ u (f a).2)).
      unfold pr1_path.

      pose (p0 := ap10_ap_precompose (pr1 : {e:E & (χ e).1} -> E) ((let (equiv_inv, eisretr, eissect, _) :=
           sepA E χ (λ x0 : E, (f x0).1) (λ x0 : E, (g x0).1) in
       equiv_inv)
        (path_forall (λ x0 : ∃ b : E, (χ b).1, (f x0.1).1)
           (λ x0 : ∃ b : E, (χ b).1, (g x0.1).1)
           (λ y : ∃ b : E, (χ b).1, ap pr1 (ap10 H y)))) (a;c)). simpl in p0.
      apply (transport (λ u, u = _) p0); clear p0.

      pose (eisretr _ (IsEquiv := sepA E χ (λ x0 : E, (f x0).1) (λ x0 : E, (g x0).1)) (path_forall (λ x0 : ∃ b : E, (χ b).1, (f x0.1).1)
           (λ x0 : ∃ b : E, (χ b).1, (g x0.1).1)
           (λ y : ∃ b : E, (χ b).1, ap pr1 (ap10 H y)))).
      unfold Sect, equiv_inv, E_to_χ_map in p0.
      pose (p1 := ap (λ u, ap10 u (a;c)) p0). simpl in p1.
      etransitivity; [exact p1 |
      exact (apD10 (eisretr (apD10 (f:=(λ x0 : ∃ b : E, (χ b).1, (f x0.1).1)) (g:=(λ x0 : ∃ b : E, (χ b).1, (g x0.1).1))) (IsEquiv := isequiv_apD10 _ _ (λ x0 : ∃ b : E, (χ b).1, (f x0.1).1) (λ x0 : ∃ b : E, (χ b).1, (g x0.1).1)) (λ y : ∃ b : E, (χ b).1, ap pr1 (ap10 H y))) (a;c))].
      
    - intro p. unfold E_to_χ_map in *; simpl in *.
      apply (@equiv_inj _ _ _ (isequiv_ap10 _ _)).
      apply path_forall; intro e.

      rewrite ap10_ap_precompose.
      unfold ap10 at 1, path_forall at 1. rewrite eisretr.

      unfold path_sigma.
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_path_sigma))).
      apply isequiv_inverse.
      rewrite eissect. simpl.
      unfold pr1_path, pr2_path.
      (* If I don't pose the following explicitly with [Set Printing All], Coq refuses to apply [path_sigma'] later *)
      pose (help := (@exist
        _
        (fun
           p0  =>
         @paths
           _
           (@transport
              _
              (fun
                 x : @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
                       A =>
               @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
                 (@proj1_sig (Trunk (trunc_S n))
                    (fun T : Trunk (trunc_S n) =>
                     @proj1_sig Type
                       (fun T0 : Type => IsTrunc (trunc_S minus_two) T0)
                       (@subuniverse_HProp (trunc_S n)
                          separation_reflective_subuniverse T))
                    (B x)))
              (@proj1_sig
                 (@proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T) A)
                 (fun
                    x : @proj1_sig Type
                          (fun T : Type => IsTrunc (trunc_S n) T) A =>
                  @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
                    (@proj1_sig (Trunk (trunc_S n))
                       (fun T : Trunk (trunc_S n) =>
                        @proj1_sig Type
                          (fun T0 : Type => IsTrunc (trunc_S minus_two) T0)
                          (@subuniverse_HProp (trunc_S n)
                             separation_reflective_subuniverse T))
                       (B x)))
                 (f
                    (@proj1_sig E
                       (fun b : E =>
                        @proj1_sig Type
                          (fun T : Type => IsTrunc sheaf_def_and_thm.n T)
                          (@char E χ b)) e)))
              (@proj1_sig
                 (@proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T) A)
                 (fun
                    x : @proj1_sig Type
                          (fun T : Type => IsTrunc (trunc_S n) T) A =>
                  @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
                    (@proj1_sig (Trunk (trunc_S n))
                       (fun T : Trunk (trunc_S n) =>
                        @proj1_sig Type
                          (fun T0 : Type => IsTrunc (trunc_S minus_two) T0)
                          (@subuniverse_HProp (trunc_S n)
                             separation_reflective_subuniverse T))
                       (B x)))
                 (g
                    (@proj1_sig E
                       (fun b : E =>
                        @proj1_sig Type
                          (fun T : Type => IsTrunc sheaf_def_and_thm.n T)
                          (@char E χ b)) e))) p0
              (@proj2_sig
                 (@proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T) A)
                 (fun
                    x : @proj1_sig Type
                          (fun T : Type => IsTrunc (trunc_S n) T) A =>
                  @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
                    (@proj1_sig (Trunk (trunc_S n))
                       (fun T : Trunk (trunc_S n) =>
                        @proj1_sig Type
                          (fun T0 : Type => IsTrunc (trunc_S minus_two) T0)
                          (@subuniverse_HProp (trunc_S n)
                             separation_reflective_subuniverse T))
                       (B x)))
                 (f
                    (@proj1_sig E
                       (fun b : E =>
                        @proj1_sig Type
                          (fun T : Type => IsTrunc sheaf_def_and_thm.n T)
                          (@char E χ b)) e))))
           (@proj2_sig
              (@proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T) A)
              (fun
                 x : @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
                       A =>
               @proj1_sig Type (fun T : Type => IsTrunc (trunc_S n) T)
                 (@proj1_sig (Trunk (trunc_S n))
                    (fun T : Trunk (trunc_S n) =>
                     @proj1_sig Type
                       (fun T0 : Type => IsTrunc (trunc_S minus_two) T0)
                       (@subuniverse_HProp (trunc_S n)
                          separation_reflective_subuniverse T))
                    (B x)))
              (g
                 (@proj1_sig E
                    (fun b : E =>
                     @proj1_sig Type
                       (fun T : Type => IsTrunc sheaf_def_and_thm.n T)
                       (@char E χ b)) e))))
        (ap pr1 (ap10 p e))
        (pr2_path (ap10 p e)))). simpl in help.
      refine (path_sigma' _ _ _); clear help.
      { pose (ap10_ap_precompose (pr1 : {e:E & (χ e).1} -> E) ((let (equiv_inv, eisretr, eissect, _) :=
                                                                    sepA E χ (pr1 o f) (pr1 o g) in
                                                                equiv_inv)
                                                                 (path_forall (pr1 o f o pr1) (pr1 o g o pr1)
                                                                              (λ y : ∃ b : E, (χ b).1, ap pr1 (ap10 p y)))) e).
        apply (transport (λ u, u=_) p0). clear p0.

        pose (p0 := eisretr _ (IsEquiv := sepA E χ (λ x0 : E, (f x0).1) (λ x0 : E, (g x0).1)) (path_forall (λ x : ∃ b : E, (χ b).1, (f x.1).1)
           (λ x : ∃ b : E, (χ b).1, (g x.1).1)
           (λ y : ∃ b : E, (χ b).1, ap pr1 (ap10 p y)))).
        unfold Sect, equiv_inv, E_to_χ_map in p0. 
        apply (transport (λ u, ap10 u e = _) p0^).
        exact (apD10 (eisretr (apD10 (f:=(λ x0 : ∃ b : E, (χ b).1, (f x0.1).1)) (g:=(λ x0 : ∃ b : E, (χ b).1, (g x0.1).1))) (IsEquiv := isequiv_apD10 _ _ (λ x0 : ∃ b : E, (χ b).1, (f x0.1).1) (λ x0 : ∃ b : E, (χ b).1, (g x0.1).1)) (λ y : ∃ b : E, (χ b).1, ap pr1 (ap10 p y))) e). }
      { destruct e as [a c]. simpl in *.
        repeat rewrite transport_paths_FlFr; simpl.
        repeat rewrite ap_const.
        repeat rewrite ap_idmap.
        repeat rewrite concat_p1. unfold pr2_path. simpl.
        hott_simpl.
        repeat rewrite ap_V. simpl.

        match goal with
          |[ |- _ @ ap10 ?X _ = _] => set (t := X)
        end.
        
        pose (p0 := @ap10_ap_precompose {e:{e:E & e=a} & (χ e.1).1} {e:E &e=a} (((B (g a).1).1).1) pr1 _ _ t ((a;1);c)). simpl in p0.
        rewrite <- p0; clear p0.
        unfold t; clear t.
        unfold equiv_inv.
        pose (rew := eisretr _ (IsEquiv := (B (g a).1).2 (∃ e' : E, e' = a) (density_sigma χ a)
                (λ z : ∃ e' : E, e' = a,
                 transport (λ u : E, ((B (g u).1).1).1) z.2
                   (transport (λ x0 : A.1, ((B x0).1).1)
                      (ap10
                         ((let (equiv_inv, eisretr, eissect, _) :=
                               sepA E χ (λ x : E, (f x).1) (λ x : E, (g x).1) in
                           equiv_inv)
                            (path_forall (λ x : ∃ b : E, (χ b).1, (f x.1).1)
                               (λ x : ∃ b : E, (χ b).1, (g x.1).1)
                               (λ y : ∃ b : E, (χ b).1, (ap10 p y) ..1))) z.1)
                      (f z.1).2))
                (λ z : ∃ e' : E, e' = a,
                   transport (λ u : E, ((B (g u).1).1).1) z.2 (g z.1).2))).
        unfold Sect in rew. rewrite rew; clear rew.
        pose (ap10_path_forall (λ x : ∃ b : ∃ e' : E, e' = a, (χ b.1).1,
         transport (λ u : E, ((B (g u).1).1).1) (x.1).2
           (transport (λ x0 : A.1, ((B x0).1).1)
              (ap10
                 ((let (equiv_inv, eisretr, eissect, _) :=
                       sepA E χ (λ x0 : E, (f x0).1) (λ x0 : E, (g x0).1) in
                   equiv_inv)
                    (path_forall (λ x0 : ∃ b : E, (χ b).1, (f x0.1).1)
                       (λ x0 : ∃ b : E, (χ b).1, (g x0.1).1)
                       (λ y : ∃ b : E, (χ b).1, (ap10 p y) ..1))) 
                 (x.1).1) (f (x.1).1).2))
              (λ x : ∃ b : ∃ e' : E, e' = a, (χ b.1).1,
                 transport (λ u : E, ((B (g u).1).1).1) (x.1).2 (g (x.1).1).2)).
        rewrite p0. clear p0.
        simpl.
        repeat rewrite transport_paths_FlFr.
        repeat rewrite ap_const.
        repeat rewrite ap_idmap. simpl.
        unfold E_to_χ_map. simpl.
        repeat rewrite concat_p1.
        rewrite concat_p_pp.

        match goal with
          |[ |- _ = ?X] =>  path_via (1 @ X)
        end.
        apply whiskerR.
        apply moveR_Vp.
        rewrite concat_p1.
        apply ap.
        rewrite concat_p_pp.
        apply whiskerR. simpl.
        rewrite inv_V.
        reflexivity. }
    - intro p.
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_path_forall f g))). apply isequiv_inverse.
      rewrite eissect. simpl.
      apply path_forall; intro x. simpl.
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_path_sigma))). apply isequiv_inverse.
      unfold path_sigma.
      rewrite eissect. simpl.

      refine (path_sigma' _ _ _).
      { destruct p. simpl.
        refine (apD10 _ _). intro y; reflexivity.
        
        unfold equiv_inv.
        path_via (ap10 ((let (equiv_inv, eisretr, eissect, _) :=
                             sepA E χ (pr1 o f) (pr1 o f) in
                         equiv_inv)
                          1)).
        apply ap. apply ap. apply path_forall_1.
        apply (moveR_equiv_V (f := path_forall _ _) (H := isequiv_path_forall _ _)).
        etransitivity; try (symmetry; apply path_forall_1).
        apply moveR_equiv_V. reflexivity.
      }
      { simpl.
        destruct p. 
        repeat rewrite transport_paths_FlFr.
        repeat rewrite ap_const.
        repeat rewrite ap_idmap.
        unfold pr2_path.
        rewrite concat_p1.
        unfold moveR_equiv_V. simpl.
        unfold path_forall_1.
        unfold eta_path_forall. simpl.
        hott_simpl.
        apply moveR_Vp.
        transparent assert (XX : ((λ z : ∃ e' : E, e' = x,
             transport (λ u : E, ((B (f u).1).1).1) z.2
               (transport (λ x0 : A.1, ((B x0).1).1)
                  (ap10
                     ((let (equiv_inv, eisretr, eissect, _) :=
                           sepA E χ (pr1 o f) (pr1 o f) in
                       equiv_inv)
                        (path_forall (E_to_χ_map A χ (pr1 o f))
                           (E_to_χ_map A χ (pr1 o f))
                           (λ y : ∃ b : E, (χ b).1, 1))) z.1) 
                  (f z.1).2)) ==
            (λ z : ∃ e' : E, e' = x,
               transport (λ u : E, ((B (f u).1).1).1) z.2 (f z.1).2))).
        { intro u. apply ap.
          path_via (transport (λ x0 : A.1, ((B x0).1).1) 1 (f u.1).2); try auto.
          apply (ap (λ p, transport (λ x0 : A.1, ((B x0).1).1) p (f u.1).2)). simpl.
          refine (apD10 _ _). intro v. reflexivity.
          path_via (ap10 ((let (equiv_inv, eisretr, eissect, _) :=
                             sepA E χ (pr1 o f) (pr1 o f) in
                         equiv_inv)
                            1)).
          apply ap. apply ap. apply path_forall_1.
          apply (moveR_equiv_V (f := path_forall _ _) (H := isequiv_path_forall _ _)).
          etransitivity; try (symmetry; apply path_forall_1).
          apply moveR_equiv_V. reflexivity. }
        
        match goal with
          |[ |- @ap10 ?XXX ?XY ?Xf ?Xg ?XH ?Xu = ?X2 ] => 
           assert (foo := λ p, apD10 (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_ap10 Xf Xg)) (isequiv_inverse _) (ap10 XH) XX p) (x;1))
        end.
        transitivity (XX (x;1)).
        apply foo.
        { unfold XX; clear foo; clear XX.
          unfold path_forall_1, eta_path_forall.
          unfold moveR_equiv_V. simpl.
          rewrite eissect.
          apply moveR_equiv_V. simpl.
          apply (@equiv_inj _ _ _ (isequiv_ap10 _ _)).
          unfold ap10 at 2. unfold path_forall at 3. rewrite eisretr.
          apply path_forall; intros [[b p] c]. simpl in *. destruct p. simpl.
          
          unfold E_to_χ_map.
          simpl.
          match goal with
            |[|- _ = ap10 (ap _ ?X) ?Y] => 
          apply (transport (λ U, _ = U) (ap10_ap_precompose (C := ((B (f b).1).1).1) (pr1 : {e:(∃ e' : E, e' = b) & (χ e.1).1} -> (∃ e' : E, e' = b)) X Y)^) end.
          rewrite (eisretr ap10). simpl.
          hott_simpl.

          apply ap.
          repeat rewrite transport_paths_FlFr.
          hott_simpl.
          
          rewrite concat_pp_p.
          apply moveR_Vp.
          apply moveL_pM.
          symmetry.

          match goal with
            |[|- _ = _ @ (apD10 ?X _)^] => set (foo := X)
          end.

          
          pose (apD10_ap_precompose (pr1 : {e:E & (χ e).1} -> E) foo (b;c))^.
          simpl in p.
          rewrite p. clear p. unfold foo; clear foo.
          match goal with
              |[|- _ = _ @ (apD10 ?X ?Y)^] => 
          apply (transport (λ U, _ = _ @ U) (apD10_V X Y)) end.
          rewrite concat_pp_p.
          apply (transport (λ U, _ = _ @ U) (apD10_pp (eisretr apD10 (λ y : ∃ b0 : E, (χ b0).1, 1)) (ap (λ h : ∀ x : E, (f x).1 = (f x).1, h oD pr1)
         ((ap ap10
             (ap
                (let (equiv_inv, eisretr, eissect, _) :=
                     sepA E χ (λ x : E, (f x).1) (λ x : E, (f x).1) in
                 equiv_inv) (eissect apD10 1)) @
           ap apD10
             (eissect
                (ap (λ (f0 : E → A.1) (x : ∃ b0 : E, (χ b0).1), f0 x.1)) 1 @
                (eissect apD10 1)^)) @ eisretr apD10 (λ v : E, 1)))^ (b;c))).

          match goal with
            |[|- _ = _ @ apD10 ?X _] => set (foo := X)
          end. simpl in foo.
          
          set (bc := (b;c)).
          refine (apD10 (g := λ bc, ap
                                      (λ
                                         x : (λ x : ∃ b0 : E, (χ b0).1, (f x.1).1) =
                                             (λ x : ∃ b0 : E, (χ b0).1, (f x.1).1), ap10 x bc)
                                      (eisretr (ap (λ (f0 : E → A.1) (x : ∃ b0 : E, (χ b0).1), f0 x.1))
                                               (path_forall (λ x0 : ∃ b0 : E, (χ b0).1, (f x0.1).1)
                                                            (λ x0 : ∃ b0 : E, (χ b0).1, (f x0.1).1)
                                                            (λ y : ∃ b0 : E, (χ b0).1, 1))) @ apD10 foo bc) _ _).
          clear bc. clear c. clear b.
          unfold foo; clear foo.
          etransitivity; try exact (@apD _ (λ U : (λ x0 : E, (f x0).1) = (λ x0 : E, (f x0).1),
                              ∀ a : ∃ e : E, (χ e).1,
                                ap10 (ap (λ h : E → A.1, h o pr1) U) a = ap10 U a.1) (ap10_ap_precompose (pr1 : {e:E & (χ e).1} -> E)) 1
                     ((let (equiv_inv, eisretr, eissect, _) :=
                           sepA E χ (λ x0 : E, (f x0).1) (λ x0 : E, (f x0).1) in
                       equiv_inv)
                        (path_forall (λ x0 : ∃ b : E, (χ b).1, (f x0.1).1)
                                     (λ x0 : ∃ b : E, (χ b).1, (f x0.1).1) (λ y : ∃ b : E, (χ b).1, 1)))
                     (ap
                        (let (equiv_inv, eisretr, eissect, _) :=
                             sepA E χ (λ x0 : E, (f x0).1) (λ x0 : E, (f x0).1) in
                         equiv_inv) (path_forall_1 (λ x : ∃ b : E, (χ b).1, (f x.1).1)) @
                        eissect (ap (E_to_χ_map A χ)) 1)^)^.

          simpl.
          apply (moveR_transport_p (λ U : (λ x0 : E, (f x0).1) = (λ x0 : E, (f x0).1),
      ∀ a : ∃ e : E, (χ e).1,
        ap10 (ap (λ h : E → A.1, h o pr1) U) a = ap10 U a.1)).
          unfold ap10_ap_precompose, apD10_ap_precompose.
          simpl.
          apply path_forall; intro u; simpl.

          rewrite transport_forall_constant. simpl.
          rewrite transport_paths_FlFr. hott_simpl.
          unfold path_forall_1, eta_path_forall. simpl.
          rewrite <- ap_pp.
          repeat rewrite concat_pp_p.
          (* apply moveL_Vp. *)
          (* rewrite concat_p1. *)
          repeat rewrite ap_pp.
          (* repeat rewrite <- ap_compose. *)
          repeat rewrite apD10_pp.
          simpl. unfold E_to_χ_map; simpl.
          repeat rewrite concat_p_pp.
          symmetry.
          match goal with
            |[|- ?X1 @ ?X2 @ ?X3 @ ?X4 @ ?X5 @ ?X6 = _] =>
             set (P1 := X1);
               set (P2 := X2);
               set (P3 := X3);
               set (P4 := X4);
               set (P5 := X5);
               set (P6 := X6)
               (* set (P7 := X7) *)         
          end. simpl in *.
          assert (X123 : P1 @ P2 @ P3 = 1).
          { clear P4; clear P5; clear P6.
            unfold P1, P2, P3; clear P1; clear P2; clear P3.
            pose (IsEq := sepA E χ (λ x0 : E, (f x0).1) (λ x0 : E, (f x0).1)).
            rewrite concat_pp_p.
            apply moveR_Vp.

            match goal with
              |[|- ?XX = _] => set (foo := XX)
            end. simpl in foo.
            
            admit. }
          rewrite X123; clear X123.
          assert (X456 : P4 @ P5 @ P6 = 1).
          { unfold P4, P5, P6; clear P6; clear P5; clear P4; clear P3; clear P2; clear P1.
            


            admit. }
          rewrite concat_1p.
          exact X456. }
        
        { unfold XX; clear foo; clear XX. simpl.
          unfold path_forall_1, eta_path_forall.
          unfold moveR_equiv_V. simpl. hott_simpl. }
      }
  Defined.

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

    unfold nsub_to_char, hfiber in *; simpl in *.

    unfold O_rec; simpl.

    apply path_sigma' with (p := path_sigma' (λ x:E, (cloture (λ b : E, (∃ x : A, m x = b; Trm b)) x) .1) (@idpath _ b0) (rew1 @ rew2)).
    simpl in *.
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
    unfold hfiber; simpl.
                     
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
      reflexivity.
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
    unfold Y, hfiber in *.
    rewrite <- (eta_sigma (A:=E) (P:=λ x, ((χ x) .1) .1) b).
    apply foo.
  Defined.

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
    unfold closed_to_sheaf_inv, E_to_χmono_map, nsub_to_char, hfiber in *; simpl in *.
    destruct (snd B.2 E χ) as [inv_B retr_B sect_B adj_B].

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
    unfold Sect, E_to_χ_map, nsub_to_char, hfiber, O_rec in *; simpl in *.
    rewrite rew1; clear rew1.

    pose (foo := (@equalpr2_restriction_χ A B m Trm closed E χ X (pr1 b) inv_B retr_B b)).
    unfold clE_to_clY'A, E_to_Y'A, O_rec, hfiber in foo; simpl in foo.
    unfold Sect, E_to_χ_map, nsub_to_char, hfiber, O_rec in *; simpl in *.

    pose (bar := j_is_nj_unit ((χ b .1) .1) (b.2)).
    unfold Oj_unit, transport, Sect, E_to_χ_map, nsub_to_char, hfiber, O_rec in *; simpl in *.
    
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
    rewrite (eissect _ (IsEquiv := closed (inv_B (m o X) (let (proj1_sig, _) := b in proj1_sig)))).
    (* rewrite sect_closed. *)
    reflexivity.
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
    unfold E_to_χmono_map, nsub_to_char, hfiber, O_rec in *; simpl in *.
    destruct (snd B.2 E χ) as [inv_B retr_B sect_B adj_B].
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
  
    unfold E_to_χ_map, nsub_to_char, hfiber, O_rec, Y in *; simpl in *.
   
    pose (h := (λ e, (X e; inverse (foo e))) : ∀ e : E, {x : A .1 | m x = inv_B (λ t : {b : E | ((χ b) .1) .1}, m (X t .1)) e}).
    assert ((∀ (e : E) (X0 : ((χ e) .1) .1),
          (X e;
           inverse
             (ap10 
                      (retr_B (λ t : {b : E | ((χ b) .1) .1}, m (X t .1)))
                      (e; X0))) = h e)).
      intros; unfold h, foo. apply path_sigma' with (p := idpath); simpl.
      apply ap.
      clear eq. specialize (adj_B (m o X)). 
      apply (transport (λ x:((λ (f : E -> (B .1) .1) (t : {b0 : E | ((χ b0) .1) .1}), f t .1)
         (inv_B (λ t : {b0 : E | ((χ b0) .1) .1}, m (X t .1))) =
       (λ t : {b0 : E | ((χ b0) .1) .1}, m (X t .1))), ((ap10  x (e; X0)) = (ap10  (sect_B (λ t : E, m (X t))) e))) (inverse adj_B)).
      clear adj_B.

      exact (@ap10_ap_precompose {b0 : E | ((χ b0) .1) .1} E ((B .1) .1) pr1 (inv_B (λ t : {b : E | ((χ b) .1) .1}, (λ t0 : E, m (X t0)) t .1)) (λ t : E, m (X t)) (sect_B (λ t : E, m (X t))) (e;X0)).

    exact (inverse (@cloture_fun_ E χ (λ x, (hfiber m (Y x); Trm (Y x))) (λ e p, pr2 (E_to_Y'A _ _ closed _ b retr_B (e;p))) (λ b, match j_is_nj (χ b) .1 in (_ = y) return y with | 1%path => (χ b) .2 end) h X0 b)).

    rewrite (eissect _ (IsEquiv := closed
       (inv_B
          (λ x : ∃ b0 : E, (let (proj1_sig, _) := χ b0 in proj1_sig).1,
           m (X (let (proj1_sig, _) := x in proj1_sig))) b))).
    (* rewrite sect_closed. *)
    reflexivity.
  Defined.

  Lemma compose_equiv {A B C D:Type} (φ : A -> B) (u v : B -> C) (f : C -> D)
        (equiv_compose_φ : IsEquiv (ap (λ x, x o φ) (x:= f o u) (y := f o v)))
        (Monof_f : IsMonof f)
  : IsEquiv (ap (λ x, x o φ) (x:=u) (y:=v)).
    unfold IsMonof in *; simpl in *.

    pose (e1 := (Monof_f B u v)).
    pose (e2 := (equiv_compose_φ)).
    pose (e3 := @isequiv_inverse _ _ _ (Monof_f A (u o φ) (v o φ))).

    assert (((ap (λ u0 : A → C, f o u0))^-1 o (ap (λ x : B → D, x o φ) o (ap (λ u0 : B → C, f o u0) (x:=u) (y:=v)))) = (ap (λ x : B → C, x o φ))).
    apply path_forall; intro p.
    apply (@equiv_inj _ _ _ (Monof_f A (u o φ) (v o φ))). rewrite eisretr.
    destruct p; reflexivity.

    destruct X. exact (@isequiv_compose _ _ _ (@isequiv_compose _ _ _ e1 _ _ e2) _ _ e3).
  Qed.

  (* Lemma 32 *)      
  Definition closed_to_sheaf (A:Trunk (trunc_S n)) (B:SnType_j_Type) (m : {f : (pr1 A) -> (pr1 (pr1 B)) & forall b, IsTrunc n (hfiber f b)}) (Monom : IsMono m.1)
  : closed' m  -> Snsheaf_struct A.
    intro cl_m.
    split.
    - destruct m as [m Hm]. destruct B as [[B TrB] [Bsep Bsheaf]]. simpl in *. clear Bsheaf.
      unfold closed', closed, nsub_to_char in cl_m; simpl in cl_m.
      intros T χ f g. unfold E_to_χ_map in *; simpl in *.
      specialize (Bsep T χ (m o f) (m o g)).
      unfold E_to_χ_map in *; simpl in *.
      assert (Monofm := IsMono_to_IsMonof Monom).
      exact (@compose_equiv ({t:T & (χ t).1}) T A.1 B pr1 f g m Bsep Monofm).
    - exact (λ E χ, isequiv_adjointify _ (@closed_to_sheaf_inv A B m cl_m E χ) (@closed_to_sheaf_retr A B m cl_m E χ) (@closed_to_sheaf_sect A B m cl_m E χ)).
  Defined.

  Definition mono_is_hfiber (T U : Type) (m : T -> U) (Monom : IsMono m) :
    ∀ b , IsTrunc n (hfiber m b).
    intro. apply IsHProp_IsTrunc.
    apply IsEmbedding_IsMono. exact Monom.
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
      unfold IsMono_fromIm_inv, path_ishprop.
      destruct a, x as [x s]; simpl.
      rewrite (contr 1); reflexivity.
  Defined.

  Lemma Sigma_IsHProp_O (T: Type) (χ : T -> Trunk n) (H : forall x, IsHProp (χ x).1)
  : forall x, IsHProp ((O nj (χ x)).1.1).
    intro x. specialize (H x).
    assert (((O nj (χ x)).1).1 = ((O sheaf_def_and_thm.nj
                                     ((χ x).1; IsHProp_IsTrunc H sheaf_def_and_thm.n0)).1).1).
    repeat apply (ap pr1). apply ap. apply truncn_unique. exact fs. reflexivity.
    rewrite X. apply (transport IsHProp (j_is_nj ((χ x).1;H))). apply _j.
  Qed.

  Lemma transport'_1 (A : Type) (P : A → Type) (x : A) (u : P x) v (H : 1=v)
  : transport P v u = u.
    destruct H. reflexivity.
  Qed.
  
  Lemma IsMono_IsHProp_cloture (T: Type) (χ : T -> Trunk n) (Monom : IsMono (pr1 : (sigT (pr1 o χ)) -> T))
  : forall x, IsHProp ((O nj (χ x)).1.1).
    apply Sigma_IsHProp_O.
    intro x.
    apply hprop_allpath.
    intros u v.
    specialize (Monom (x;u) (x;v)).
    pose (equiv_inv (IsEquiv := Monom) 1)..2. simpl in p.
    etransitivity; try exact p.
    unfold pr1_path. rewrite eisretr. reflexivity.
  Defined.

  Lemma IsMono_cloture (T: Type) (χ : T -> Trunk n) (Monom : IsMono (pr1 : (sigT (pr1 o χ)) -> T))
  : IsMono (pr1 : (sigT (pr1 o pr1 o ((O nj) o χ))) -> T).

    intros [x px] [y py].
    simpl; refine (isequiv_adjointify _ _ _ _).
    - intro p. apply path_sigma' with p. 
      refine (path_ishprop _ _). apply IsMono_IsHProp_cloture. exact Monom.
    - intro p. simpl. destruct p. simpl.
      unfold path_ishprop.
      destruct (center (px = py)). reflexivity.
    - intro p.
      unfold path_sigma'. simpl.
      pose (IsMono_IsHProp_cloture Monom y).
      apply eta'_path_sigma. apply path_ishprop.
  Qed.

  Lemma IsMono_cloture' (T U:Type) (m : U -> T) (Monom : IsMono m)
  : IsMono (cloture' (m;mono_is_hfiber Monom)).2.1.
    unfold cloture', cloture, nsub_to_char, nchar_to_sub; simpl.
    pose (@IsMono_cloture T (λ b0 : T, (hfiber m b0; mono_is_hfiber Monom (b:=b0)))).
    refine (i _).
    apply IsEmbedding_IsMono.
    intro x. unfold Overture.hfiber. simpl.
    pose (snd (IsEmbedding_IsMono m) Monom).
    apply (hprop_allpath).
    intros [[p p'] pp] [[q q'] qq]. simpl in *.
    refine (path_sigma' _ _ _).
    apply path_sigma' with (pp @ qq^).
    refine (path_ishprop _ _).
    simpl.
    destruct pp. destruct qq. hott_simpl.
    destruct (path_ishprop (transport (λ x : T, hfiber m x) 1 p') q').
    reflexivity.
  Defined.
                                    
  Definition separated_to_sheaf (T:{T : Trunk (trunc_S n) & separated T}) (U:SnType_j_Type) m Monom :
    Snsheaf_struct (@separated_to_sheaf_Type T.1.1 U.1.1 m Monom; @separated_to_sheaf_IsTrunc_Sn _ _ m Monom).
    refine (closed_to_sheaf _ _ _ _).
    exact U.
    exact ((pr2 (cloture' (m;mono_is_hfiber Monom)))).
    exact (@IsMono_cloture' U.1.1 T.1.1 m Monom).
    apply cloture_is_closed'.
  Defined.

  (* The following has exactly the same type as separated_to_sheaf, but doesn't create universes constraints *)
  Definition separated_to_sheaf' (T:{T : Trunk (trunc_S n) & separated T}) (U:SnType_j_Type) m Monom :
    Snsheaf_struct (@separated_to_sheaf_Type T.1.1 U.1.1 m Monom; @separated_to_sheaf_IsTrunc_Sn _ _ m Monom).
  Admitted. (* Universes *)

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
  
  Definition sheafification_ (T:Trunk (trunc_S n)) : Snsheaf_struct (sheafification_trunc T)
    := separated_to_sheaf' (((existT (IsTrunc (trunc_S n)) (separated_Type T) (separated_Type_is_Trunk_Sn (T:=T)))); @separated_Type_is_separated T) (T_nType_j_Type_sheaf T) (IsMono_fromIm (f:=_)).

  (* Definition of ○_{n+1} *)
  Definition sheafification (T:Trunk (trunc_S n)) : SnType_j_Type :=
  ((sheafification_Type T ; sheafification_istrunc  (T:=T)); sheafification_ T).

  (* Definition of ○_{n+1} matching the one in the paper *)
  Definition good_sheafification_Type (T:Trunk (n.+1))
    := {u : T.1 -> subuniverse_Type nj & (Oj (Trunc -1 ({a:T.1 & (λ t' : T.1,
                                                                         (O nj (a = t'; istrunc_paths T.2 a t'))) = u}); istrunc_truncation -1 _)).1.1}.

  (* The above definitions are equal *)
  Lemma good_sheafification_Type_is_sheafification_Type (T:Trunk (trunc_S n))
  : (sheafification T).1.1 = good_sheafification_Type T.
    unfold sheafification, sheafification_Type, separated_to_sheaf, separated_to_sheaf_Type, cloture; simpl.
    unfold cloture, nsub_to_char, fromIm, hfiber, mono_is_hfiber; simpl.
    apply path_universe_uncurried.
    apply equiv_functor_sigma_id.
    intros a. simpl.
    apply equiv_path.
    transparent assert (hp : HProp).
    { exists (∃ x : separated_Type T, x.1 = a).
      exact ((snd
           (IsEmbedding_IsMono
              (λ
               im : Im
                      (λ t t' : T.1,
                       (O nj (t = t'; istrunc_paths T.2 t t'))),
               im.1))
           (IsMono_fromIm
              (f:=λ t t' : T.1,
                  (O nj (t = t'; istrunc_paths T.2 t t')))) a)). }
    pose (p := j_is_nj hp).
    unfold hp in *; simpl in *; clear hp.
    rewrite <- p. clear p.
    repeat apply ap.
    (* apply truncn_unique. exact fs. simpl. *)
    unfold separated_Type, Im, Overture.hfiber. simpl.
    apply univalence_hprop.
    - exact (snd
       (IsEmbedding_IsMono
          (λ
           im : Im
                  (λ t t' : T.1,
                   (O nj (t = t'; istrunc_paths T.2 t t'))), im.1))
       (IsMono_fromIm
          (f:=λ t t' : T.1,
              (O nj (t = t'; istrunc_paths T.2 t t')))) a).

    - exact (istrunc_truncation (-1)
       (∃ a0 : T.1,
        (λ t' : T.1,
         (O nj (a0 = t'; istrunc_paths T.2 a0 t'))) = a)).
      
    - split.
      + intros [[x y] p]. destruct p. simpl.
      revert y. apply Trunc_rec. intros [y z].
      apply tr.
      exists y.
      exact z.
      + apply Trunc_ind.
        intro x.
        exact (snd
       (IsEmbedding_IsMono
          (λ
           im : Im
                  (λ t t' : T.1,
                   (O nj (t = t'; istrunc_paths T.2 t t'))), im.1))
       (IsMono_fromIm
          (f:=λ t t' : T.1,
              (O nj (t = t'; istrunc_paths T.2 t t')))) a).
        intros [x q].
        refine (exist _ _ _).
        exists a.
        apply tr. exists x. exact q.
        reflexivity.
  Qed.

  Definition good_sheafification (T:Trunk (n.+1))
  : SnType_j_Type.
    refine (exist _ _ _).
    exists (good_sheafification_Type T).
    rewrite <- good_sheafification_Type_is_sheafification_Type.
    exact _.2.
    match goal with
      |[|- Snsheaf_struct ?X] => assert (eq : (sheafification T).1 = X)
    end.
    refine (path_sigma' _ _ _).
    apply good_sheafification_Type_is_sheafification_Type.
    apply path_ishprop.
    destruct eq.
    exact _.2.
  Defined.

  Definition good_sheafification_unit (T:Trunk (trunc_S n))
  : T.1 -> (good_sheafification T).1.1.
    intro x.
    exists (separated_unit T x).1.
    apply Oj_unit. simpl.
    apply tr.
    exists x. reflexivity.
  Defined.

  Definition density_sheafification (T:Trunk (n.+1))
  : (good_sheafification_Type T) -> J.
    intros [u x].
    unfold J, nchar_to_sub. simpl.
    exists ((Trunc -1 ({a:T.1 & (λ t' : T.1,
                                             (O nj (a = t'; istrunc_paths T.2 a t'))) = u}); istrunc_truncation -1 _)).
    exact x.
  Defined.

  Lemma density_sheafification_is_sep (T : Trunk (n.+1))
  : {e:(good_sheafification_Type T) & (density_sheafification e).1.1} <~>  separated_Type T.
    refine (equiv_adjointify _ _ _ _).
    - intros [e p].
      exists e.1.
      exact p.
    - intros [e he].
      refine (exist _ _ _).
      exists e.
      apply Oj_unit.
      exact he. exact he.
    - intros [e he].
      reflexivity.
    - intros [e p].
      refine (path_sigma' _ _ _).
      apply path_sigma' with 1.
      apply path_ishprop.
      apply path_ishprop.
  Defined.

  Definition sheafification_equiv (P:Trunk (n.+1)) (Q : Trunk (n.+1)) (modQ : (Snsheaf_struct Q))
  : IsEquiv (fun f : (good_sheafification P).1.1 -> Q.1 => f o (good_sheafification_unit P)).
    destruct modQ as [sepQ sheafQ].
    match goal with |[|- IsEquiv ?X] => set (foo := X) end.

    transparent assert (sh_to_clsep : ((((good_sheafification P).1).1 → Q.1) -> ({e:(good_sheafification_Type P) & (density_sheafification e).1.1} → Q.1))).
    { intros X Y.
      apply X.
      exact Y.1. }
    transparent assert (clsep_to_sep : (({e:(good_sheafification_Type P) & (density_sheafification e).1.1} → Q.1) -> (separated_Type P -> Q.1))).
    { apply equiv_arrow.
      apply density_sheafification_is_sep. }
    pose (sep_f := (λ (f : separated_Type P → ((Q; sepQ).1).1) 
         (x : P.1), f (separated_unit P x))).
    assert (foo = sep_f o clsep_to_sep o sh_to_clsep) by reflexivity.
    rewrite X.
    refine (isequiv_compose).
    - exact (separated_equiv P (existT (separated) Q sepQ)).
  Qed.

  (* Proposition 33 *)
  Definition sheafification_subu_sigma (A:Trunk n.+1) (modA : Snsheaf_struct A) (B: A.1 -> Trunk n.+1) (modB : forall a, (Snsheaf_struct (B a))) 
  : Snsheaf_struct (({x:A.1 & (B x).1} ; trunc_sigma (A.2) (λ x, (B x).2)): Trunk n.+1).
    destruct modA as [sepA sheafA].
    split.
    - assert (p := subu_sigma _ (separated_modality)). simpl in p.      
      exact (p (A; sepA) (λ a, (B a; fst (modB a)))). 
    - intros E χ.
      refine (isequiv_adjointify _ _ _ _).
      + simpl.
        intros φ e.
        destruct ((sheafA E χ)) as [inva retra secta _]. unfold Sect in *; simpl in *.
        pose (a := inva (pr1 o φ) e).
        exists a.
        unfold E_to_χmono_map in *; simpl in *.
        specialize (modB a).
        destruct modB as [sepB sheafB]. simpl in *.        
        specialize (sheafB {e':E & e = e'} (λ x, χ x.1)).
        refine (equiv_inv (IsEquiv := sheafB) _ (e;1)).
        intros X.
        specialize (retra (pr1 o φ)).
        apply ap10 in retra.
        specialize (retra (e; transport _ X.1.2^ X.2)). simpl in retra.
        unfold a.
        apply (transport (λ U, (B U).1) retra^).
        exact (φ (e; transport _ X.1.2^ X.2)).2.
      + intro φ; simpl in *.
        unfold E_to_χmono_map; simpl in *.
        apply path_forall; intros [e h].
        refine (path_sigma' _ _ _).
        { exact (ap10 (eisretr _ (IsEquiv := sheafA E χ) (pr1 o φ)) (e;h)). }
        { destruct ((sheafA E χ)) as [inva retra secta adja]. 
          destruct (modB (inva
             (λ x : ∃ b : E, (let (proj1_sig, _) := χ b in proj1_sig).1,
                let (proj1_sig, _) := φ x in proj1_sig) e)) as [sepB sheafB].
          destruct (sheafB (∃ e' : E, e = e') (λ x, (χ x.1))) as [invb retrb sectb adjb].
          simpl in *. clear adjb; clear adja.
          unfold Sect, E_to_χmono_map in *; simpl in *.
          refine (moveR_transport_p (pr1 o B) _ _ _ _).
          match goal with
            |[|- invb ?X _ = _ ] => specialize (retrb X)
          end.
          simpl in retrb.
          apply ap10 in retrb.
          specialize (retrb ((e;1);h)). simpl in retrb.
          exact retrb. }
      + intro φ; simpl in *.
        apply path_forall; intro e.
        refine (path_sigma' _ _ _).
        { exact (ap10 (eissect _ (IsEquiv := sheafA E χ) (pr1 o φ)) e). }
        {
          refine (moveR_transport_p (pr1 o B) _ _ _ _).
          refine (@moveR_EV2 {e':E & e=e'} {b:{e':E & e=e'} & (χ b.1).1.1}
                             _ _ _ _ _ _ (e;1) _).
          intros [X p].
          destruct p.
          apply ((transport (λ x : A.1, let (proj1_sig, _) := B x in proj1_sig)
                            (ap10
                               (eissect (IsEquiv := sheafA E χ) (E_to_χmono_map A (χ:=χ))
                                        (λ x0 : E, let (proj1_sig, _) := φ x0 in proj1_sig)) e)^)).

          unfold E_to_χmono_map. simpl.
          apply path_forall; intros [[X p] h]. destruct p. simpl in *.
          apply (ap (λ u, transport (λ x : A.1, let (proj1_sig, _) := B x in proj1_sig) u (φ e).2)).
          apply ap.
          pose (p := eisadj (IsEquiv := sheafA E χ) _ (pr1 o φ)).
          unfold eisretr, E_to_χmono_map in p. simpl in p.
          rewrite p.
          exact (ap10_ap_precompose (pr1 : (∃ x :E, (χ x).1.1) -> E)
                                   (eissect (IsEquiv := sheafA E χ) (E_to_χmono_map A (χ:=χ))
                                            (λ x : E, let (proj1_sig, _) := φ x in proj1_sig))
                                   (e;h))^. }
  Qed.

  (* Proposition 33 *)
  Definition sheafification_subU : subuniverse_struct (n.+1).
    refine (Build_subuniverse_struct _ _ _ _).
    - intro T. exists (Snsheaf_struct T). apply Snsheaf_struct_is_HProp.
    - intros T. exact (good_sheafification T).
    - intros T. apply good_sheafification_unit.
    - exact (λ P Q, sheafification_equiv P Q.2).
  Defined.

  (* Proposition 34 *)
  Definition sheafification_modality : Modality (n.+1).
    refine (Build_Modality _ _ _).
    - exact sheafification_subU.
    - exact (λ A B, sheafification_subu_sigma A.2 (pr1 o B) (λ a, (B a).2)).
  Defined.
      
  (* Proposition 35 as an axiom because of universes issues *)
  Axiom cumulativity : forall (T:Trunk n) (SnT : IsTrunc (n.+1) T.1), (O nj T).1.1 = (good_sheafification_Type (T.1;SnT)).


  Definition O_paths_is_paths_sheafification_unit_fun (T:Trunk (n.+1)) (a b:T.1) : ((good_sheafification_unit T a) = (good_sheafification_unit T b)) -> (O nj (a = b; (istrunc_paths T.2 a b))).1.1.
    intro p.
    unfold good_sheafification_unit in p. simpl in p.
    pose (p' := (ap10 p..1 a)..1..1). simpl in p'.
    transparent assert (X: (((O nj (a = b; istrunc_paths T.2 a b)) .1) .1 =
                            ((O nj (b = a; istrunc_paths T.2 b a)) .1) .1)).
    repeat apply (ap pr1); apply ap.
    apply truncn_unique. exact fs.
    apply equal_inverse.
    apply (transport  idmap X^).
    apply (transport idmap p'). apply O_unit. reflexivity.
  Defined.

  Definition O_paths_is_paths_sheafification_unit_inv T (a b:T.1) : (O nj (a = b; (istrunc_paths T.2 a b))).1.1 -> ((good_sheafification_unit T a) = (good_sheafification_unit T b)).
    intro p.
    pose (Ωj := (T.1 -> subuniverse_Type nj; T_nType_j_Type_trunc T)).
    pose (inj := pr1 : (good_sheafification_Type T) -> Ωj.1).
    transparent assert (X : (IsMono inj)).
    intros x y. apply subset_is_subobject. intro.
    exact _.2.
    assert (X0 : inj (good_sheafification_unit T a) = inj (good_sheafification_unit T b)).
    unfold inj, separated_unit. simpl.
    apply path_forall; intro t; simpl.
    apply unique_subuniverse; apply truncn_unique. exact fs.
    unfold Oj; simpl. 
    apply path_universe_uncurried.
    exists (mu_modal_paths_func_univ_func T a b p t).
    apply isequiv_adjointify with (g := mu_modal_paths_func_univ_inv T a b p t);
      [exact (fst (mu_modal_paths_func_univ_eq T a b p t)) | exact (snd (mu_modal_paths_func_univ_eq T a b p t))].
    exact (@equiv_inv _ _ _ (X _ _) X0).
  Defined.

  (* Proposition 36 *)
  Lemma O_paths_is_paths_sheafification_unit (T:Trunk (n.+1)) (a b:T.1)
  : ((good_sheafification_unit T a) = (good_sheafification_unit T b)) <~> (O nj (a = b; (istrunc_paths T.2 a b))).1.1.
    refine (equiv_adjointify _ _ _ _).
    - apply O_paths_is_paths_sheafification_unit_fun.
    - apply O_paths_is_paths_sheafification_unit_inv.
    - intro x. unfold O_paths_is_paths_sheafification_unit_fun, O_paths_is_paths_sheafification_unit_inv.
      simpl.
      apply (moveR_transport_V idmap _ _ _).
      unfold pr1_path. simpl.
      pose (foo := isequiv_eq_dep_subset (λ a0 : T.1 → subuniverse_Type nj,
                     _j
                       (Trunc (-1)
                          (∃ a1 : T.1,
                           (λ t' : T.1,
                            O nj (a1 = t'; istrunc_paths T.2 a1 t')) = a0);
                       istrunc_truncation (-1)
                         (∃ a1 : T.1,
                          (λ t' : T.1,
                           O nj (a1 = t'; istrunc_paths T.2 a1 t')) = a0)))
                                         (λ t' : T.1, O nj (a = t'; istrunc_paths T.2 a t');
                    Oj_unit
                      (Trunc (-1)
                         (∃ a0 : T.1,
                          (λ t' : T.1,
                           O nj (a0 = t'; istrunc_paths T.2 a0 t')) =
                          (λ t' : T.1, O nj (a = t'; istrunc_paths T.2 a t')));
                      istrunc_truncation (-1)
                        (∃ a0 : T.1,
                         (λ t' : T.1, O nj (a0 = t'; istrunc_paths T.2 a0 t')) =
                         (λ t' : T.1, O nj (a = t'; istrunc_paths T.2 a t'))))
                      (tr (a; 1)))
                                         (λ t' : T.1, O nj (b = t'; istrunc_paths T.2 b t');
                    Oj_unit
                      (Trunc (-1)
                         (∃ a0 : T.1,
                          (λ t' : T.1,
                           O nj (a0 = t'; istrunc_paths T.2 a0 t')) =
                          (λ t' : T.1, O nj (b = t'; istrunc_paths T.2 b t')));
                      istrunc_truncation (-1)
                        (∃ a0 : T.1,
                         (λ t' : T.1, O nj (a0 = t'; istrunc_paths T.2 a0 t')) =
                         (λ t' : T.1, O nj (b = t'; istrunc_paths T.2 b t'))))
                      (tr (b; 1)))).
      assert (bar := eissect _ (IsEquiv := foo)). simpl in bar.
      unfold Sect in bar. simpl in bar.
      rewrite bar. clear bar; clear foo.
      unfold ap10, path_forall; rewrite eisretr.
      assert (rew := eissect _ (IsEquiv := isequiv_unique_subuniverse (O nj (a = a; istrunc_paths T.2 a a)) (O nj (b = a; istrunc_paths T.2 b a)))). unfold Sect in rew; simpl in rew; unfold pr1_path in rew.
      rewrite rew; clear rew.
      assert (rew := eissect _ (IsEquiv := isequiv_truncn_unique (O nj (a = a; istrunc_paths T.2 a a)).1 (O nj (b = a; istrunc_paths T.2 b a)).1)). unfold Sect in rew; simpl in rew; unfold pr1_path in rew.
      rewrite rew; clear rew.
      rewrite transport_path_universe_uncurried.
      unfold mu_modal_paths_func_univ_func, δ. simpl.
      pose (foo := ap10 (O_rec_retr (a = a; istrunc_paths T .2 a a) (O nj (b = a; istrunc_paths T.2 b a))
                                    (λ u : a = a,
      O_rec (a = b; istrunc_paths T.2 a b)
        (O nj (b = a; istrunc_paths T.2 b a))
        (λ v : a = b, O_unit nj (b = a; istrunc_paths T.2 b a) (v^ @ u)) x)) 1).
      apply (transport (λ u, u = _) foo^); clear foo.
      apply ap10.

      pose (O_equiv nj (a = b; istrunc_paths T.2 a b) (O nj (b = a; istrunc_paths T.2 b a))).
      apply (@equiv_inj _ _ _ i).
      rewrite O_rec_retr.
      apply path_forall; intro v. simpl in v.
      rewrite concat_p1.
      pose (foo := mu_modal_paths_aux (a = b; istrunc_paths T.2 a b) (b = a; istrunc_paths T.2 b a) v (equal_inverse a b)).
      transitivity (O_unit nj (b = a; istrunc_paths T .2 b a)
                           (transport idmap (equal_inverse a b) v)); try exact foo.
      apply ap. unfold equal_inverse.
      rewrite transport_path_universe_uncurried. reflexivity.
    - intro p. unfold O_paths_is_paths_sheafification_unit_fun, O_paths_is_paths_sheafification_unit_inv.
      simpl.
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_eq_dep_subset
                                                     (λ a0 : T.1 → subuniverse_Type nj,
      _j
        (Trunc (-1)
           (∃ a1 : T.1,
            (λ t' : T.1, O nj (a1 = t'; istrunc_paths T.2 a1 t')) = a0);
        istrunc_truncation (-1)
          (∃ a1 : T.1,
             (λ t' : T.1, O nj (a1 = t'; istrunc_paths T.2 a1 t')) = a0)))
                                                     (λ t' : T.1, O nj (a = t'; istrunc_paths T.2 a t');
     Oj_unit
       (Trunc (-1)
          (∃ a0 : T.1,
           (λ t' : T.1, O nj (a0 = t'; istrunc_paths T.2 a0 t')) =
           (λ t' : T.1, O nj (a = t'; istrunc_paths T.2 a t')));
       istrunc_truncation (-1)
         (∃ a0 : T.1,
          (λ t' : T.1, O nj (a0 = t'; istrunc_paths T.2 a0 t')) =
          (λ t' : T.1, O nj (a = t'; istrunc_paths T.2 a t')))) 
       (tr (a; 1)))
                                                     (λ t' : T.1, O nj (b = t'; istrunc_paths T.2 b t');
     Oj_unit
       (Trunc (-1)
          (∃ a0 : T.1,
           (λ t' : T.1, O nj (a0 = t'; istrunc_paths T.2 a0 t')) =
           (λ t' : T.1, O nj (b = t'; istrunc_paths T.2 b t')));
       istrunc_truncation (-1)
         (∃ a0 : T.1,
          (λ t' : T.1, O nj (a0 = t'; istrunc_paths T.2 a0 t')) =
          (λ t' : T.1, O nj (b = t'; istrunc_paths T.2 b t')))) 
       (tr (b; 1))))));
        [apply isequiv_inverse | rewrite eissect].
      apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _));
        unfold path_forall; rewrite eisretr.
      apply path_forall; intro t.
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_unique_subuniverse _ _)));
        [apply isequiv_inverse | rewrite eissect].
      
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_truncn_unique _ _)));
        [apply isequiv_inverse | idtac].
      rewrite eissect.

      simpl in *.
      apply (@equiv_inj _ _ _ (isequiv_equiv_path _ _)); unfold path_universe_uncurried; rewrite eisretr.
      apply equal_equiv.
      unfold mu_modal_paths_func_univ_func, δ. simpl.

      apply path_forall; intro x.
      refine (ap10 (moveR_EV _ _ _) x).
      apply path_forall; intro u. simpl in *.

      unfold δ; simpl.
      destruct u.
      unfold ap10, pr1_path.
      transitivity (function_lift nj (a = b; istrunc_paths T.2 a b) (b = a; istrunc_paths T.2 b a) (transport idmap (equal_inverse a b)) (transport idmap (equiv_nj_inverse nj T a b)^ (transport idmap (ap pr1 (ap pr1 (apD10 (ap pr1 p) a))) (O_unit nj (a = a; istrunc_paths T.2 a a) 1)))).

      unfold function_lift, equiv_nj_inverse; simpl.
      apply (ap (λ u, O_rec (a = b; istrunc_paths T.2 a b) (O nj (b = a; istrunc_paths T.2 b a))  u (transport idmap
        (ap pr1
           (ap pr1
              (ap (O nj)
                 (truncn_unique fs (a = b; istrunc_paths T.2 a b)
                    (b = a; istrunc_paths T.2 b a) 
                    (equal_inverse a b)))))^
        (transport idmap (ap pr1 (ap pr1 (apD10 (ap pr1 p) a)))
                   (O_unit nj (a = a; istrunc_paths T.2 a a) 1))))).
      apply path_forall; intro v. apply ap. unfold equal_inverse; rewrite transport_path_universe_uncurried.
      apply concat_p1.

      transparent assert (X : ((function_lift nj (a = b; istrunc_paths T.2 a b)
                                 (b = a; istrunc_paths T.2 b a) (transport idmap (equal_inverse a b))) = transport idmap (equiv_nj_inverse nj T a b))).

      { assert (foo := function_lift_transport).
        specialize (foo n nj ua fs (a = b; istrunc_paths T.2 a b) (b = a; istrunc_paths T.2 b a)).
        unfold equiv_nj_inverse.
        specialize (foo
                      (truncn_unique fs
              (a = b; istrunc_paths T.2 a b) (b = a; istrunc_paths T.2 b a)
              (equal_inverse a b))).
        simpl in foo.

        assert (bar := equal_equiv_inv (ap (equiv_inv (IsEquiv := isequiv_path_universe)) foo)).
        unfold path_universe in bar; simpl in bar.
        rewrite transport_path_universe_uncurried in bar.
        clear foo.

        unfold equiv_nj_inverse. simpl. unfold pr1_path in *. simpl in *.
        etransitivity. Focus 2.
        exact bar^.
        
        apply ap. apply ap.
        unfold truncn_unique. unfold eq_dep_subset.

        (* unfold path_sigma'. *)
        pose (rew := @pr1_path_sigma). unfold pr1_path in rew. rewrite rew. reflexivity. }

      apply (transport (λ u, u (transport idmap (equiv_nj_inverse nj T a b) ^
                                (transport idmap (ap pr1 (ap pr1 (apD10 (ap pr1 p) a)))
                                           (O_unit nj (a = a; istrunc_paths T.2 a a) 1))) = transport idmap (ap pr1 (ap pr1 (apD10 (ap pr1 p) a)))
                                                                                                      (O_unit nj (a = a; istrunc_paths T.2 a a) 1)) X^).
      rewrite transport_pV. reflexivity.
      
  Qed.

  (* The following has exactly the same type as O_paths_is_paths_sheafification_unit, but doesn't collapse universes *)
  Lemma O_paths_is_paths_sheafification_unit' (T:Trunk (n.+1)) (a b:T.1)
  : ((good_sheafification_unit T a) = (good_sheafification_unit T b)) <~> (O nj (a = b; (istrunc_paths T.2 a b))).1.1.
  Admitted. (* Universes *)


  (* Left-exactness of sheafification *)
  Definition sheafification_left_exact
  : IsLex sheafification_modality.
    intros A x y H. simpl.
    rewrite <- (cumulativity (x = y; (istrunc_paths A.2 x y))).
    apply (@trunc_equiv' (good_sheafification_unit A x = good_sheafification_unit A y) ((O nj (x = y; istrunc_paths A.2 x y)).1).1 (O_paths_is_paths_sheafification_unit' A x y) -2).
    apply (@contr_paths_contr).
    simpl in H.
    unfold good_sheafification. simpl.
    exact H.
  Defined.
    
  Definition sheafification_hprop (T:Trunk n.+1) (HT : IsHProp T.1)
  : (Oj (T.1;HT)).1.1 = (good_sheafification_Type T).
    apply univalence_hprop.
    exact _.2.
    pose @hprop_stability.
    (* specialize (i ua fs  (trunc_S n) (sheafification_modality)). *)
    (* Should work. *) admit.
    split.
    - intros x.
      unfold good_sheafification_Type.
      (* We want here to give (λ x, x = Oj_unit (T.1;HP) t), then revert x, apply O_rec_dep, then tr and reflexivity. *)
      (* refine (exist _ _ _). *)
      (* intro t. *)
      (* refine (exist _ _ _). *)
      (* refine (exist _ _ _). *)
      (* exact (x = Oj_unit (exist IsHProp T.1 HT) t). *)
      (* apply istrunc_paths *)
      (* Should work *) admit. 
    - intros [u p]. 
      revert p.
      apply Oj_equiv.
      apply Trunc_rec.
      intros [a p]. destruct p.
      apply Oj_unit.
      exact a.
  Qed.
      
End Sheafification.
