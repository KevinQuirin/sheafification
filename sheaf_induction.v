(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type" "-bt") -*- *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import PathGroupoid_ Forall_ Equivalences_ epi_mono reflective_subuniverse modalities.
Require Import nat_lemmas.
Require Import kernel_pair.
(* Require Import colimit. *)
(* Require Import VD_truncation gpd. *)
Require Import sheaf_base_case.
Require Import sheaf_def_and_thm.
Require Import OPaths.


Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
(* Local Open Scope equiv_scope. *)
Local Open Scope type_scope.

(* Readability *)
Arguments trunc_arrow {H} {A} {B} {n} {H0}: simpl never.
Arguments trunc_sigma {A} {P} {n} {H H0}: simpl never.
Arguments trunc_forall {H} {A} {P} {n} {H0}: simpl never. 
Arguments istrunc_paths {A} {n} {H} x y: simpl never.
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

  Definition BTT (T:Type) `{Tr: IsTrunc n T} := @BuildTruncType n T Tr.
  
  (* Definition of □T *)
  Definition separated_Type (T:TruncType (trunc_S n)) : Type :=
    Im (λ t : T, λ t', O nj (BTT (t = t'))).

  Definition sheaf_is_separated (T : SnType_j_Type) : separated T.1 := fst (T.2).
 
  Definition separated_Type_is_TruncType_Sn (T:TruncType (trunc_S n)) : IsTrunc (trunc_S n) (separated_Type T).
    unfold separated_Type; simpl.
    (* destruct T as [T TrT]; simpl in *. *)
    refine trunc_sigma.
    refine trunc_forall. intro t.
    exact (@subuniverse_Type_is_TruncTypeSn _ nj ua).
  Defined.

  Definition E_to_χ_map_ap (T U:TruncType (trunc_S n)) {E} (χ : EnJ E) (f : E -> T)
             (g : T -> U) {x y} (e : x = y) : 
    ap (fun u => g o u) (ap (E_to_χ_map T χ) e) = ap (E_to_χ_map U χ) (ap (fun u => g o u) e).
    destruct e; reflexivity.
  Defined.

  (* TODO (low): move this declarations into the section itself, once weird bug is sorted out. *)
Arguments BuildEquiv [A B f] _ : rename.

(* TODO (high): move to library. *)
Global Arguments equiv_inv [A B] f {_} x.

(* TODO (low): consider; possibly move to library. *)
Global Arguments equiv_fun [A B] _ _.
Global Arguments equiv_isequiv [A B] e.
Global Arguments isequiv_adjointify [A B f] _ _ _.

(* TODO (med): Unnecessary here; but probably move to library. *)
Global Arguments isequiv_ap [A B] f {_} x y.

(* TODO (high): move to library. *)
Global Arguments isequiv_postcompose {_} A [B C] f {_}.
Global Arguments isequiv_precompose {_} [A B] C f {_}.


  Instance separated_mono_is_separated_ {T U:TruncType (trunc_S n)} {E} χ g h (f: T -> U)
        (H:IsEquiv (ap (E_to_χ_map U (E:=E) χ) (x:=f o g) (y:=f o h))) (fMono : IsMonof f) : 
    IsEquiv (ap (E_to_χ_map T (E:=E) χ) (x:=g) (y:=h)).
  
  refine (isequiv_adjointify (fun X => @equiv_inv _ _ _ (fMono E g h) (@equiv_inv _ _ _ H (ap (fun u => f o u) X))) _ _).
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
    rewrite p. rewrite ((@eissect _ _ _ H (ap (fun u => f o u) e))).
    apply eissect.
  Defined.

  (* Lemma 28 *)
  Definition separated_mono_is_separated (T U:TruncType (trunc_S n)) (H:separated U) (f: T -> U) (fMono : IsMonof f) : separated T.
    intros E χ x y.
    refine (separated_mono_is_separated_ _ _ _ _ (H E χ (f o x) (f o y)) fMono).
  Defined.

  Definition T_nType_j_Type_trunc (T:Type) : IsTrunc (trunc_S n) (T -> subuniverse_Type nj).
  Proof.
    refine trunc_forall. intro t.
    exact (@subuniverse_Type_is_TruncTypeSn _ nj ua).
  Defined.

  Definition T_nType_j_Type_isSheaf
    : forall T, Snsheaf_struct (@BuildTruncType _ (T -> subuniverse_Type nj) (T_nType_j_Type_trunc T)).
  Proof.
    intro T.
    refine (dep_prod_SnType_j_Type T (λ _, ((BuildTruncType _ (subuniverse_Type nj)); nType_j_Type_is_SnType_j_Type))).
  Defined.

  (* For any type [T], [T -> subuniverse_Type] is modal *)
  Definition T_nType_j_Type_sheaf T : SnType_j_Type :=  ((BuildTruncType _ (T -> subuniverse_Type nj); T_nType_j_Type_isSheaf _)).


  Global Arguments path_forall {_} [_ _ _ _] _.
  
  (* Proposition 27 *)
  Definition separated_Type_is_separated (T:TruncType (trunc_S n)) : separated (@BuildTruncType _ (separated_Type T) (separated_Type_is_TruncType_Sn T)).
    apply (@separated_mono_is_separated
              (@BuildTruncType _ (separated_Type T) (separated_Type_is_TruncType_Sn T))
              (BuildTruncType _ (T -> subuniverse_Type nj))
              (sheaf_is_separated (T_nType_j_Type_sheaf T))
              (pr1 )).
    intros X f g. simpl in *.
    apply (isequiv_adjointify (λ H, (path_forall (λ x, path_sigma _ _ _ (ap10 H x) (path_ishprop _ _))))).
    - intro p.
      apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
      apply path_forall; intro x.
      apply (transport (λ U, U = ap10 p x) (ap10_ap_postcompose pr1 _ x)^).
      unfold ap10 at 1, path_forall at 1. rewrite eisretr.
      apply pr1_path_sigma.
    - intro x. destruct x. simpl.
      etransitivity; [idtac | apply path_forall_1].
      apply ap.
      apply path_forall; intro x.
      unfold path_ishprop.
      rewrite (@contr ((f x) .2 = (f x) .2) _ 1). reflexivity.
  Defined.

  Definition separation (T:TruncType (trunc_S n)) : {T : TruncType (trunc_S n) & separated T} :=
    (@BuildTruncType _ (separated_Type T) (separated_Type_is_TruncType_Sn T);separated_Type_is_separated T).

  Definition separated_unit (T:TruncType (n.+1)) :  T -> separated_Type T := toIm _.

  
  Definition mu_modal_paths_func_univ_func
             (T : TruncType (trunc_S n))
             (a : T)
             (b : T)
             (p : ((clδ T) (a, b)))
             (t : T)
  : O nj (BTT (a = t)) -> O nj (BTT (b = t)).
    apply O_rec; intro u.
    generalize dependent p; apply O_rec; intro v. apply (O_unit nj).
    exact (v^@u).
  Defined.

  Definition mu_modal_paths_func_univ_inv
             (T : TruncType (trunc_S n))
             (a : T)
             (b : T)
             (p : ((clδ T) (a, b)))
             (t : T)
  : O nj (BTT (b = t)) -> O nj (BTT (a = t)).
    apply O_rec; intro u.
    generalize dependent p; apply O_rec; intro v; apply (O_unit nj).
    exact (v@u).
  Defined.

  Lemma mu_modal_paths_func_univ_eq
        (T : TruncType (trunc_S n))
        (a : T)
        (b : T)
        (p : (clδ T (a, b)))
        (t : T)
  : (Sect (mu_modal_paths_func_univ_inv T a b p t) (mu_modal_paths_func_univ_func T a b p t))
    /\ (Sect (mu_modal_paths_func_univ_func T a b p t) (mu_modal_paths_func_univ_inv T a b p t)).
    split.
    - intro x.
      unfold mu_modal_paths_func_univ_inv, mu_modal_paths_func_univ_func, δ; simpl. unfold clδ, δ in p; simpl in p.
      refine (ap10 (f:= (O_rec n nj (BTT (a = t))
                               (O nj (BTT (b = t)))
                               (λ u : a = t,
                                      O_rec n nj (BTT (a = b))
                                            (O nj (BTT (b = t)))
                                            (λ v : a = b, O_unit nj (BTT (b = t)) (v ^ @ u))
                                            p)) 
                          o (O_rec n nj (BTT (b = t))
                                   (O nj (BTT (a = t)))
                                   (λ u : b = t,
                                          O_rec n nj (BTT (a = b))
                                                (O nj (BTT (a = t)))
                                                (λ v : a = b, O_unit nj (BTT (a = t)) (v @ u))
                                                p))) (g:=idmap) _ x).
      apply O_rec_O_rec. exact fs.
      intros q q'. destruct q.
      rewrite concat_p1.
      apply concat_Vp.
    - intro x. unfold mu_modal_paths_func_univ_inv, mu_modal_paths_func_univ_func, δ. simpl.
      (* pose (foo := O_rec_O_rec nj *)
      (*                (b = t; istrunc_paths T.2 b t) *)
      (*                (a = t; istrunc_paths T.2 a t) *)
      (*                (a = b; istrunc_paths T.2 a b) *)
      (*                (λ u v, v @ u) *)
      (*                (λ u v, v^ @ u) *)
      (*                p *)
      (*            ); simpl in foo. *)

      refine (ap10 (f:= (O_rec n nj (BTT (b = t))
                               (O nj (BTT (a = t)))
                               (λ u : b = t,
                                      O_rec n nj (BTT (a = b))
                                            (O nj (BTT (a = t)))
                                            (λ v : a = b, O_unit nj (BTT (a = t)) (v @ u))
                                            p)) 
                          o (O_rec n nj (BTT (a = t))
                                   (O nj (BTT (b = t)))
                                   (λ u : a = t,
                                          O_rec n nj (BTT (a = b))
                                                (O nj (BTT (b = t)))
                                                (λ v : a = b, O_unit nj (BTT (b = t)) (v^ @ u))
                                                p))) (g:=idmap) _ x).
      apply O_rec_O_rec. exact fs.
      intros q q'. destruct q'.
      rewrite concat_1p.
      apply concat_1p.
  Qed.

  Arguments mu_modal_paths_func_univ_eq : default implicits, simpl never.


  Definition separated_unit_paths_are_nj_paths_fun (T:(n.+1)-Type) (a b:T) : (separated_unit T a = separated_unit T b) -> (O nj (BTT (a=b))).
    intro p.
    unfold separated_unit, toIm in p. simpl in p.
    pose (p' := ap trunctype_type (ap (@st n nj) (ap10 p..1 b))). simpl in p'.
    apply (transport idmap p'^). apply O_unit. reflexivity.
  Defined.

  Definition separated_unit_paths_are_nj_paths_inv (T:(n.+1)-Type) (a b:T) : (O nj (BTT (a=b))) -> (separated_unit T a = separated_unit T b).
    intro p.
    pose (Ωj := @BuildTruncType _ (T -> subuniverse_Type nj) (T_nType_j_Type_trunc T)).
    pose (inj := pr1 : (separated_Type T) -> Ωj).
    transparent assert (X : (IsMono inj)).
    intros x y. 
    exact (isequiv_inverse (path_sigma_hprop x y)).
    
    assert (inj (separated_unit T a) = inj (separated_unit T b)).
    unfold inj, separated_unit. simpl.
    apply path_forall; intro t; simpl.
    apply unique_subuniverse; apply path_trunctype.
    symmetry.
    exists (mu_modal_paths_func_univ_inv T a b p t).
    apply isequiv_adjointify with (g := mu_modal_paths_func_univ_func T a b p t);
      [exact (snd (@mu_modal_paths_func_univ_eq T a b p t)) | exact (fst (@mu_modal_paths_func_univ_eq T a b p t))].
    exact (@equiv_inv _ _ _ (X (separated_unit T a) (separated_unit T b)) X0).
  Defined.

  Lemma mu_modal_paths_aux (A B:TruncType n) (v:A) (eq : A = B :> Type)
    : O_unit nj B (transport idmap eq v)
      = transport idmap
                  (ap trunctype_type
                      (ap (@st n nj)
                          (ap (O nj)
                              (path_trunctype (equiv_path _ _ eq))))) (O_unit nj A v).
        destruct A as [A TrA], B as [B Trb]; simpl in *.
        destruct eq.
        simpl.
        assert (p := (center (TrA = Trb))). destruct p.
        unfold path_trunctype. cbn.
        rewrite eta_path_universe_uncurried.
        unfold path_sigma_hprop, path_sigma_uncurried. 
        cbn. hott_simpl.
        match goal with
        |[|- _ = transport idmap (ap _ (ap _ (ap _ (ap _
                                                       match ?foo in (_ = v2) return _ with |_ => _ end)))) _] => assert (r: 1 = foo) by apply path_ishprop; destruct r
        end.
        reflexivity.
  Defined.

  Lemma separated_unit_paths_are_nj_paths_retr (T:TruncType (n.+1)) (a b:T)
  : Sect (separated_unit_paths_are_nj_paths_inv T a b) (separated_unit_paths_are_nj_paths_fun T a b).
    unfold separated_unit_paths_are_nj_paths_fun, separated_unit_paths_are_nj_paths_inv.
    intro x.
    apply (moveR_transport_V idmap _ _ x).
    unfold pr1_path. simpl.

    pose (s := eissect (path_sigma_hprop (separated_unit T a) (separated_unit T b))).
    unfold Sect in s; cbn in s; unfold pr1_path in s; cbn in s.
    rewrite s; clear s.
    unfold ap10, path_forall; rewrite eisretr.

    assert (rew := eissect _ (IsEquiv := isequiv_unique_subuniverse n nj (O nj (BTT (a = b))) (O nj (BTT (b = b))))). unfold Sect in rew; simpl in rew; unfold pr1_path in rew.
    rewrite rew; clear rew.

    pose (eisretr _ (IsEquiv := isequiv_ap_trunctype (O nj (BTT (a = b))) (O nj (BTT (b = b))))).
    unfold Sect in s; cbn in *; rewrite s; clear s.
    rewrite transport_idmap_path_universe_uncurried.
     
    unfold mu_modal_paths_func_univ_func, δ. simpl.

    revert x.
    transparent assert (sh : ((O nj (BTT (a = b))) -> subuniverse_Type nj)).
    { intro x.
      refine (Build_subuniverse_Type _ nj (BTT (O_unit nj (BTT (b = b)) 1 =
   O_rec sheaf_def_and_thm.n nj (BTT (a = b)) (O nj (BTT (b = b)))
     (λ u : a = b,
      O_rec sheaf_def_and_thm.n nj
        {|
        trunctype_type := a = b;
        istrunc_trunctype_type := istrunc_paths a b |} 
        (O nj (BTT (b = b))) (λ v : a = b, O_unit nj (BTT (b = b)) (v^ @ u))
        x) x)) _).
      admit.
      admit.
    }
      refine (O_rec_dep _ sh _).1.
      unfold sh; clear sh; intro x; simpl.
              
      pose (foo := λ P Q f, ap10 (O_rec_retr n nj P Q f)).
      simpl in foo.
      rewrite foo. rewrite foo. apply ap. hott_simpl.
  Admitted.
  
  Lemma separated_unit_paths_are_nj_paths_sect (T:(n.+1)-Type) (a b:T)
  : Sect (separated_unit_paths_are_nj_paths_fun T a b) (separated_unit_paths_are_nj_paths_inv T a b).
    unfold separated_unit_paths_are_nj_paths_fun, separated_unit_paths_are_nj_paths_inv.
    intro p.
    simpl.
    unfold separated_unit, toIm in p. simpl in p.

    apply (@equiv_inj _ _ (equiv_inv ((path_sigma_hprop (separated_unit T a) (separated_unit T b))))).
    apply isequiv_inverse.
    rewrite eissect.
    apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _));
      unfold path_forall; rewrite eisretr.
    apply path_forall; intro t.

    apply (@equiv_inj _ _ (equiv_inv _ (IsEquiv := isequiv_unique_subuniverse _ _ _ _)));
      [apply isequiv_inverse | rewrite eissect].
      
    apply (@equiv_inj _ _ _ (isequiv_ap_trunctype _ _)).
    pose (s := λ A B, eisretr _ (IsEquiv := isequiv_ap_trunctype (n := n) A B)).
    unfold Sect in s; cbn in *. rewrite s; clear s.
    unfold symmetric_equiv.

    path_via (ap trunctype_type (ap (@st sheaf_def_and_thm.n nj) (apD10 p ..1 t)))^^.
    rewrite path_universe_V_uncurried.
    apply ap.
    apply (@equiv_inj _ _ _ (isequiv_equiv_path _ _)); unfold path_universe_uncurried; rewrite eisretr. 
    
    apply path_equiv.
    unfold mu_modal_paths_func_univ_inv, mu_modal_paths_func_univ_func, δ. simpl.

    apply (@equiv_inj _ _ _ (O_equiv n nj (BTT (b = t)) (O nj (BTT (a = t))))).
    rewrite O_rec_retr.
    apply path_forall; intro u. simpl in *.
      
    destruct u.
    unfold ap10, pr1_path; cbn.

    apply (ap10 (g:=idmap)).
    etransitivity; [idtac | exact (O_rec_sect n nj (BTT (a=b)) (O nj (BTT (a=b))) idmap)].
    apply ap. apply path_forall; intro v. apply ap. apply concat_p1.
  Defined.


  (* For any [x,y:T], [(μ x = μ y) = ○ (x = y)] : in proof of Lemma 29 *)
  (* Theorem separated_unit_paths_are_nj_paths (T:(n.+1)-Type) (a b:T) : (separated_unit T a = separated_unit T b) <~> (O nj (BTT (a=b))). *)
  (* Proof. *)
  (*   refine (equiv_adjointify _ _ _ _). *)
  (*   - apply separated_unit_paths_are_nj_paths_fun. *)
  (*   - apply separated_unit_paths_are_nj_paths_inv. *)
  (*   - apply separated_unit_paths_are_nj_paths_retr. *)
  (*   - apply separated_unit_paths_are_nj_paths_sect. *)
  (* Qed. *)

  Theorem separated_unit_paths_are_nj_paths (T:(n.+1)-Type) (a b:T)
    : IsEquiv (separated_unit_paths_are_nj_paths_inv T a b).
  Proof.
      refine (isequiv_adjointify _ _ _).
    - apply separated_unit_paths_are_nj_paths_fun.
    - apply separated_unit_paths_are_nj_paths_sect.
    - apply separated_unit_paths_are_nj_paths_retr.
  Defined.

  Definition sep_eq_inv (P : TruncType (trunc_S n)) (Q :{T : TruncType (trunc_S n) & separated T})
  : (P → Q.1) -> ((separated_Type P) → Q .1).
    intro f.
    apply (equiv_inv _ (IsEquiv := (Epi_coeq_KP _ (@BuildTruncType _  _ (@separated_Type_is_TruncType_Sn P)) (separated_unit P) (@IsSurjection_toIm _ _ _) Q.1))).
    exists f.
    pose (Q.2 (clΔ P) (dense_into_cloture _ (δ P)) (λ X, f (fst X.1)) (λ X, f (snd X.1))).
    destruct i as [inv _ _ _].
    specialize (inv (path_forall (λ x, ap f x.2.1))).
    apply ap10 in inv.
    apply path_forall; intros [x [y p]].
    unfold KP1, KP2.
    transparent assert (z : ((clΔ P))).
    unfold clΔ. simpl. exists (x,y). simpl.
    apply separated_unit_paths_are_nj_paths. exact p.
    exact (inv z). 
   Defined.

  (* Proposition 30 *)
  Definition separated_equiv : forall (P : TruncType (trunc_S n)) (Q :{T : TruncType (trunc_S n) & separated T}),
                                 IsEquiv (fun f : separated_Type P -> pr1 (Q) =>
                                            f o (separated_unit P)).
    intros P Q.
    refine (isequiv_adjointify _ _ _).
    - apply sep_eq_inv.
    - intros f. apply path_forall; intro x. unfold sep_eq_inv.
      match goal with
        |[|- ?ff^-1 ?gg _ = _] => exact (ap10 (eisretr ff (IsEquiv := (Epi_coeq_KP _ (@BuildTruncType _  _ (@separated_Type_is_TruncType_Sn P)) (separated_unit P) (@IsSurjection_toIm _ _ _) Q.1)) gg)..1 x)
      end.
    - intros f.
      unfold sep_eq_inv. apply moveR_equiv_V. simpl.
      refine (path_sigma' _ idpath _).
      refine (@path_ishprop _ _ _ _).
  Defined.
  
  (* Proposition 30 *)
  Definition separation_reflective_subuniverse
  : subuniverse_struct (trunc_S n)
    := Build_subuniverse_struct (n.+1)
          (λ T, (@BuildTruncType _ (separated T) (separated_is_HProp T)))
          separation
          separated_unit
          separated_equiv.

  Lemma density_sigma (E:Type) (χ : EnJ E) (e:E) (E' := {e':E & e = e'})
  : EnJ {e':E & e' = e}.
    refine (Build_EnJ _ _ _).
    - intro x. apply χ. exact x.1.
    - intros e0.
      pose (dense_eq _ χ e0.1).
      etransitivity; try exact p.
      apply path_universe_uncurried.
      refine (equiv_adjointify _ _ _ _).
      + intros [e' q]. destruct q. exists e0.1. reflexivity.
      + intros [e' q]. destruct q. exists e0. reflexivity.
      + intros [e' q]. destruct q. reflexivity.
      + intros [e' q]. destruct q. reflexivity.
  Defined.

  Axiom proof_admitted : forall X, X.
  Ltac admit := apply proof_admitted.
  (* Proposition 31 *)
  Definition separated_modality : Modality (trunc_S n).
    refine (Build_Modality _ separation_reflective_subuniverse _).
    admit.
  Defined.

  (**** From separated to sheaf ****)

  Definition closed_to_sheaf (P:SnType_j_Type) (χ: P.1 -> TruncType n)
             (Monoχ: IsMono (pr1 : {e:P.1 & χ e} -> _))
    : closed χ -> Snsheaf_struct (BuildTruncType _ {e:P.1 & χ e}).
  Proof.
    intro clχ; destruct P as [P [SepP ShP]]; cbn in *; split.
    - intros T φ f g.
      specialize (SepP T φ (pr1 o f) (pr1 o g)).
      unfold E_to_χ_map in *; cbn in *.
      exact (@compose_equiv _ (∃ x : T, φ x) T (∃ e : P, χ e) P pr1 f g pr1 SepP Monoχ).
    - intros E φ.
      refine (isequiv_adjointify _ _ _).
      + intros f e. cbn.
        refine (exist _ _ _). apply (equiv_inv _ (IsEquiv := ShP E φ) (pr1 o f) e). 
        apply (equiv_inv _ (IsEquiv := clχ (equiv_inv _ (IsEquiv := ShP E φ) (pr1 o f) e))).
        generalize (equiv_path _ _ (j_is_nj (φ e).1) (φ e).2).
        apply O_rec; intro p; apply O_unit.
        apply (transport (λ u, χ u) (ap10 (eisretr (E_to_χmono_map P φ) (pr1 o f)) (e;p))^).
        exact (f (e;p)).2.
      + intros f. apply path_forall; intros [e p].
        unfold E_to_χmono_map.
        refine (path_sigma' _ _ _).
        exact (ap10 (eisretr (E_to_χmono_map P φ) (pr1 o f)) (e;p)). simpl.
        apply (moveR_transport_p (λ u:P, χ u)).
        apply moveR_equiv_V.
        (* pose (j_is_nj_unit (φ e).1). *)
        assert (X: (φ e).2 = (Oj_unit (φ e).1 p)) by apply path_ishprop.
        rewrite X; clear X.
        (* rewrite (j_is_nj_unit (φ e).1). *)
        match goal with
        |[|- O_rec _ _ ?PP ?QQ ?ff _ = _] =>
         assert (r := ap10 (O_rec_retr n nj PP QQ ff) p)
        end.
        rewrite r; clear r. reflexivity.
      + intros f. apply path_forall; intro e.
        refine (path_sigma' _ _ _).
        pose (eissect (E_to_χmono_map P φ)). unfold Sect, E_to_χmono_map in s.
        apply (ap10 (g:= pr1 o f)). 
        apply moveR_equiv_V. reflexivity.
        apply (moveR_transport_p (λ u:P, χ u)).
        apply moveR_equiv_V. simpl.
        match goal with
        |[|- ?XX = ?YY] =>
         set (X := XX); set (Y := YY);
         assert (Subug: IsSubu n nj (BuildTruncType _ (X = Y)))
        end.
        refine (subuniverse_paths _ _ _ X Y).
        subst X Y. 
        generalize (transport idmap (j_is_nj (φ e).1) (φ e).2).
        apply (O_rec n nj _ (Build_subuniverse_Type n nj _ Subug)); intro pp; simpl. clear Subug.
        (* pose (j_is_nj_unit (φ e).1 pp). *)
        assert (r: (φ e).2 = Oj_unit (φ e).1 pp) by apply path_ishprop.
        rewrite r; clear r.
        (* rewrite (j_is_nj_unit (φ e).1 pp). *)
        match goal with
        |[|- O_rec _ _ ?PP ?QQ ?ff _ = _] =>
         assert (r := ap10 (O_rec_retr n nj PP QQ ff) pp)
        end.
        rewrite r; clear r. simpl.
        unfold E_to_χmono_map. apply ap. apply (ap (λ U, transport (λ u : P, χ u) U (f e).2)).
        apply ap.
        unfold moveR_equiv_V.
        simpl.
        pose (p0:=eisadj (E_to_χmono_map P φ) (pr1 o f)).
        rewrite p0.
        unfold E_to_χmono_map.
        rewrite (@ap10_ap_precompose (∃ x : E, (φ x).1) E P pr1 _ _ (eissect (E_to_χmono_map P φ) (λ x : E, (f x).1))). rewrite concat_1p. reflexivity.
  Defined.
        

  Definition mono_is_hfiber (T U : Type) (m : T -> U) (Monom : IsMono m) :
    ∀ b , IsTrunc n (hfiber m b).
  Proof.
    intro. apply (@trunc_leq -1 n tt).
    apply IsEmbedding_IsMono. exact Monom.
  Defined.

  Definition separated_to_sheaf_Type (U: Type) (χ: U -> TruncType n) (Monom : IsMono (pr1: {u:U & χ u} -> _)) : Type :=
    {e:U & cloture χ e}.
  
  Definition separated_to_sheaf_IsTrunc_Sn (U : TruncType (trunc_S n)) χ Monom :
    IsTrunc (trunc_S n) (@separated_to_sheaf_Type U χ Monom).
  Proof.
    refine (trunc_sigma).
  Defined.

  Definition IsMono_fromIm_inv {A B} (f : A -> B) (x y : Im f): x.1 = y.1 -> x=y.
    intro X.
    apply path_sigma with (p := X).
    apply path_ishprop.
  Defined.
  
  Definition IsMono_fromIm {A B} (f : A -> B) : IsMono (fromIm f). 
    intros x y; apply (isequiv_adjointify (IsMono_fromIm_inv f x y)).
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

  Lemma Sigma_IsHProp_O (T: Type) (χ : T -> TruncType n) (H : forall x, IsHProp (χ x))
    : forall x, IsHProp (O nj (χ x)).
  Proof.
    intro x. specialize (H x).
    assert (X: (χ x) = {|
        trunctype_type := BuildhProp (χ x);
        istrunc_trunctype_type := @trunc_leq -1 n tt _ _|}).
    apply path_trunctype. apply equiv_idmap.
    rewrite X; clear X.
    pose (p:= (j_is_nj (BuildTruncType -1 (χ x)))).
    rewrite <- p. apply istrunc_trunctype_type.
  Defined.
  
  Lemma IsMono_IsHProp_cloture (T: Type) (χ : T -> TruncType n) (Monom : IsMono (pr1 : {t:T & χ t} -> T))
    : forall x, IsHProp (O nj (χ x)).
  Proof.
    apply Sigma_IsHProp_O.
    intro x.
    apply hprop_allpath.
    intros u v.
    specialize (Monom (x;u) (x;v)).
    pose (equiv_inv _ (IsEquiv := Monom) 1)..2. simpl in p.
    etransitivity; try exact p.
    unfold pr1_path. rewrite eisretr. reflexivity.
  Defined.

  Lemma IsMono_cloture (T: Type) (χ : T -> TruncType n) (Monom : IsMono (pr1 : {t:T & χ t} -> T))
    : IsMono (pr1 : {t:T & O nj (χ t)} -> T).
  Proof.
    intros [x px] [y py].
    simpl; refine (isequiv_adjointify _ _ _).
    - intro p. apply path_sigma' with p. 
      refine (path_ishprop _ _). 
    - intro p. simpl. destruct p. simpl.
      unfold path_ishprop.
      destruct (center (px = py)). reflexivity.
    - intro p.
      unfold path_sigma'. simpl.
      pose (IsMono_IsHProp_cloture T χ Monom y).
      match goal with
      |[|- path_sigma _ _ _ _ ?pp = _] =>
       assert (r: p..2 = pp) by apply path_ishprop
      end. destruct r.
      apply eta_path_sigma. 
  Defined.

  Definition separated_to_sheaf (U:SnType_j_Type) (χ:U.1 -> TruncType n) (sep: separated (BuildTruncType _ {u:U.1 & χ u})) Monom :
    Snsheaf_struct (BuildTruncType _ (@separated_to_sheaf_Type U.1 χ Monom)).
  Proof.
    refine (closed_to_sheaf _ _ _ _).
    exact (IsMono_cloture _ _ Monom).
    apply cloture_is_closed.
  Defined.
  
  Definition sheafification_Type (T:TruncType (trunc_S n)) 
    :=
    @separated_to_sheaf_Type (T -> subuniverse_Type nj)
                             (λ b, @BuildTruncType _ (Trunc (-1) (hfiber (λ t t' : T, O nj (BTT (t = t'))) b)) (@trunc_leq -1 n tt _ _))
                             (IsMono_fromIm _).

  Definition sheafification_istrunc (T:TruncType (trunc_S n)) : 
    IsTrunc (trunc_S n) (sheafification_Type T).
  Proof.
    refine trunc_sigma.
    apply T_nType_j_Type_trunc.
  Defined.

  Definition sheafification_trunc (T:TruncType (trunc_S n)) : TruncType (trunc_S n) :=
    @BuildTruncType _ (sheafification_Type T) (sheafification_istrunc T).
  
  Definition sheafification_ (T:TruncType (trunc_S n)) : Snsheaf_struct (sheafification_trunc T)
    := separated_to_sheaf (T_nType_j_Type_sheaf T)
                           (λ b, @BuildTruncType _ (Trunc (-1) (hfiber (λ t t' : T, O nj (BTT (t = t'))) b)) (@trunc_leq -1 n tt _ _))
                           (@separated_Type_is_separated T)
                           (IsMono_fromIm _).

  (* Definition of ○_{n+1} *)
  Definition sheafification (T:TruncType (trunc_S n)) : SnType_j_Type :=
  (@BuildTruncType _ (sheafification_Type T) (sheafification_istrunc T); sheafification_ T).

  (* Definition of ○_{n+1} matching the one in the paper *)
  Definition good_sheafification_Type (T:TruncType (n.+1))
    := {u : T -> subuniverse_Type nj &
                   (O subuniverse_Prop (BuildTruncType -1 (Trunc -1 ({a:T & (λ t' : T, (O nj (BTT (a = t')))) = u}))))}.

  (* The above definitions are equal *)
  Lemma good_sheafification_Type_is_sheafification_Type (T:TruncType (trunc_S n))
  : (sheafification T).1 <~> good_sheafification_Type T.
    unfold sheafification, sheafification_Type, separated_to_sheaf, separated_to_sheaf_Type, cloture; simpl.
    unfold cloture, fromIm, hfiber, mono_is_hfiber; simpl.
    apply equiv_functor_sigma_id.
    intros a. simpl.
    apply equiv_path.
    pose (p := j_is_nj (BuildTruncType _ (Trunc (-1)
                                                (∃ x : T, (λ t' : T, O nj (BTT (x = t'))) = a)))).
    exact p^.
  Defined.

  Lemma equiv_Snheaf_struct (T U:TruncType (n.+1)) (e: T <~> U) (ST: Snsheaf_struct T)
    : Snsheaf_struct U.
  Proof.
    destruct ST as [sepT shT].
    split.
    intros E χ φ ψ.
    specialize (sepT E χ (e^-1 o φ) (e^-1 o ψ)).

    match goal with |[sepT: IsEquiv ?gg|- IsEquiv ?ff] => pose (p:= gg); pose (p0 := ff) end.
    cbn in p, p0.
    unfold E_to_χ_map in *.

    assert (((ap (λ x, e^-1 o x))^-1 o p o (ap (λ x, e^-1 o x))) == p0).
    unfold p0, p.
    intro x.
    apply moveR_equiv_V.
    destruct x; reflexivity.

    refine (@isequiv_homotopic _ _ ((ap (λ x, e^-1 o x))^-1 o p o (ap (λ x, e^-1 o x))) p0 _ X).
    refine isequiv_compose. refine isequiv_compose.


    intros E χ; specialize (shT E χ).
    match goal with |[shT: IsEquiv ?gg|- IsEquiv ?ff] => pose (p:= gg); pose (p0 := ff) end.
    cbn in p, p0.
    unfold E_to_χmono_map in *.
    pose ((λ x, e^-1 o x)^-1 o p o (λ x, e^-1 o x)).
    assert (((λ x, e^-1 o x)^-1 o p o (λ x, e^-1 o x)) == p0).
    intro x. cbn. unfold functor_forall. cbn.
    subst p; subst p0. cbn.
    apply path_forall; intro b; cbn.
    apply eisretr.

    refine (@isequiv_homotopic _ _ ((λ x, e^-1 o x)^-1 o p o (λ x, e^-1 o x)) p0 _ X).
    refine isequiv_compose. refine isequiv_compose.
    exact shT.
  Defined.
  
  Definition good_sheafification (T:TruncType (n.+1))
  : SnType_j_Type.
    refine (exist _ _ _).
    exists (good_sheafification_Type T).
    refine trunc_sigma. apply T_nType_j_Type_trunc.
    match goal with
      |[|- Snsheaf_struct ?X] => assert (eq : (sheafification T).1 <~> X)
    end.
    apply good_sheafification_Type_is_sheafification_Type.
    apply (equiv_Snheaf_struct _ _ eq).
    exact _.2.
  Defined.

  Definition good_sheafification_unit (T:TruncType (trunc_S n))
  : T -> (good_sheafification T).1.
    intro x.
    exists (separated_unit T x).1.
    apply Oj_unit. simpl.
    apply tr.
    exists x. reflexivity.
  Defined.

  Definition density_sheafification (T:TruncType (n.+1))
  : (good_sheafification_Type T) -> J.
    intros [u x].
    unfold J. simpl.
    exists ((BuildhProp
            (Trunc (-1) (∃ a : T, (λ t' : T, O nj (BTT (a = t'))) = u)))).
    exact x.
  Defined.

  Lemma density_sheafification_is_sep (T : TruncType (n.+1))
  : {e:(good_sheafification_Type T) & (density_sheafification T e).1} <~> separated_Type T.
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

  Definition sheafification_equiv (P:TruncType (n.+1)) (Q : TruncType (n.+1)) (modQ : (Snsheaf_struct Q))
  : IsEquiv (fun f : (good_sheafification P).1 -> Q => f o (good_sheafification_unit P)).
    destruct modQ as [sepQ sheafQ].
    match goal with |[|- IsEquiv ?X] => set (foo := X) end.

    transparent assert (sh_to_clsep : ((((good_sheafification P)).1 → Q) -> ({e:(good_sheafification_Type P) & (density_sheafification P e).1} → Q))).
    { intros X Y.
      apply X.
      exact Y.1. }
    transparent assert (clsep_to_sep : (({e:(good_sheafification_Type P) & (density_sheafification P e).1} → Q) -> (separated_Type P -> Q))).
    { apply equiv_functor_arrow'. symmetry;
        apply density_sheafification_is_sep.
    apply equiv_idmap. }
    pose (sep_f := (λ (f : separated_Type P → Q) 
         (x : P), f (separated_unit P x))).
    assert (foo = sep_f o clsep_to_sep o sh_to_clsep) by reflexivity.
    rewrite X.
    refine (isequiv_compose).
    - exact (separated_equiv P (existT (separated) Q sepQ)).
  Defined.

  (* Proposition 33 *)
  Definition sheafification_subu_sigma (A:TruncType n.+1) (modA : Snsheaf_struct A) (B: A -> TruncType n.+1) (modB : forall a, (Snsheaf_struct (B a))) 
  : Snsheaf_struct (BuildTruncType (n.+1) {x:A & (B x)}).
    destruct modA as [sepA sheafA].
    split.
    - assert (p := subu_sigma _ (separated_modality)). simpl in p.      
      exact (p (Build_subuniverse_Type _ separation_reflective_subuniverse A sepA) (λ a, Build_subuniverse_Type _ separation_reflective_subuniverse (B a) (fst (modB a)))). 
    - intros E χ.
      refine (isequiv_adjointify _ _ _).
      + simpl.
        intros φ e.
        destruct ((sheafA E χ)) as [inva retra secta _]. unfold Sect in *; simpl in *.
        pose (a := inva (pr1 o φ) e).
        exists a.
        unfold E_to_χmono_map in *; simpl in *.
        specialize (modB a).
        destruct modB as [sepB sheafB]. simpl in *.        
        specialize (sheafB {e':E & e = e'} (λ x, χ x.1)).
        refine (equiv_inv _ (IsEquiv := sheafB) _ (e;1)).
        intros X.
        specialize (retra (pr1 o φ)).
        apply ap10 in retra.
        specialize (retra (e; transport _ X.1.2^ X.2)). simpl in retra.
        unfold a.
        apply (transport (λ U, (B U)) retra^).
        exact (φ (e; transport _ X.1.2^ X.2)).2.
      + intro φ; simpl in *.
        unfold E_to_χmono_map; simpl in *.
        apply path_forall; intros [e h].
        refine (path_sigma' _ _ _).
        { exact (ap10 (eisretr _ (IsEquiv := sheafA E χ) (pr1 o φ)) (e;h)). }
        { destruct ((sheafA E χ)) as [inva retra secta adja]. 
          destruct (modB (inva
               (λ x : ∃ x : E, (χ x).1,
                let (proj1_sig, _) := φ x in proj1_sig) e)) as [sepB sheafB].
          destruct (sheafB (∃ e' : E, e = e') (λ x, (χ x.1))) as [invb retrb sectb adjb].
          simpl in *. clear adjb; clear adja.
          unfold Sect, E_to_χmono_map in *; simpl in *.
          refine (moveR_transport_p B _ _ _ _).
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
          refine (moveR_transport_p B _ _ _ _).

          assert (moveR_EV2 : forall (X Y:Type) (Z:X -> Type) (T:Y -> Type)
                                     (f:(forall x, Z x) -> (forall x, T x))
                                     (H:IsEquiv f)
                                     (g:forall x, Z x)
                                     (h:forall x, T x)
                                     (x:X),
                     (f g = h) -> (f^-1 h x = g x)).
          { intros X Y Z T f H g h x X0. destruct X0. rewrite eissect. reflexivity. }
          refine (@moveR_EV2 {e':E & e=e'} {b:{e':E & e=e'} & (χ b.1).1}
                             _ _ _ _ _ _ (e;1) _); clear moveR_EV2.
          intros [X p].
          destruct p.
          apply ((transport (λ x : A, let (proj1_sig, _) := B x in proj1_sig)
                            (ap10
                               (eissect (IsEquiv := sheafA E χ) (E_to_χmono_map A χ)
                                        (λ x0 : E, let (proj1_sig, _) := φ x0 in proj1_sig)) e)^)).

          unfold E_to_χmono_map. simpl.
          apply path_forall; intros [[X p] h]. destruct p. simpl in *.
          apply (ap (λ u, transport (λ x : A, let (proj1_sig, _) := B x in proj1_sig) u (φ e).2)).
          apply ap.
          pose (p := eisadj (IsEquiv := sheafA E χ) _ (pr1 o φ)).
          unfold eisretr, E_to_χmono_map in p. simpl in p.
          rewrite p.
          exact (ap10_ap_precompose (pr1 : (∃ x :E, (χ x).1) -> E)
                                   (eissect (IsEquiv := sheafA E χ) (E_to_χmono_map A χ)
                                            (λ x : E, let (proj1_sig, _) := φ x in proj1_sig))
                                   (e;h))^. }
  Qed.

  (* Proposition 33 *)
  Definition sheafification_subU : subuniverse_struct (n.+1).
    refine (Build_subuniverse_struct _ _ _ _ _).
    - intro T. exists (Snsheaf_struct T). apply Snsheaf_struct_is_HProp.
    - intros T. exact (good_sheafification T).
    - intros T. apply good_sheafification_unit.
    - exact (λ P Q, sheafification_equiv P Q.1 Q.2).
  Defined.

  (* Proposition 34 *)
  Definition sheafification_modality : Modality (n.+1).
    refine (Build_Modality _ _ _).
    - exact sheafification_subU.
    - exact (λ A B, sheafification_subu_sigma A (@subu_struct _ _ _) B (λ a, @subu_struct _ _ (B a))).
  Defined.
      
  (* Proposition 35 as an axiom because of universes issues *)
  Axiom cumulativity : forall (T:TruncType n) (SnT : IsTrunc (n.+1) T), (O nj T) <~> (good_sheafification_Type (@BuildTruncType _ T SnT)).

  Definition good_sheafification_unit_paths_are_nj_paths_fun (T:(n.+1)-Type) (a b:T) : (good_sheafification_unit T a = good_sheafification_unit T b) -> (O nj (BTT (a=b))).
    intro p.
    unfold good_sheafification_unit, toIm in p. simpl in p.
    pose (p' := ap trunctype_type (ap (@st n nj) (ap10 p..1 b))). simpl in p'.
    apply (transport idmap p'^). apply O_unit. reflexivity.
  Defined.

  Definition good_sheafification_unit_paths_are_nj_paths_inv (T:(n.+1)-Type) (a b:T) : (O nj (BTT (a=b))) -> (good_sheafification_unit T a = good_sheafification_unit T b).
    intro p.
    pose (Ωj := @BuildTruncType _ (T -> subuniverse_Type nj) (T_nType_j_Type_trunc T)).
    pose (inj := pr1 : (good_sheafification_Type T) -> Ωj).
    transparent assert (X : (IsMono inj)).
    intros x y. 
    exact (isequiv_inverse (path_sigma_hprop x y)).
    
    assert (inj (good_sheafification_unit T a) = inj (good_sheafification_unit T b)).
    unfold inj, good_sheafification_unit. simpl.
    apply path_forall; intro t; simpl.
    apply unique_subuniverse; apply path_trunctype.
    symmetry.
    exists (mu_modal_paths_func_univ_inv T a b p t).
    apply isequiv_adjointify with (g := mu_modal_paths_func_univ_func T a b p t);
      [exact (snd (mu_modal_paths_func_univ_eq p t)) | exact (fst (mu_modal_paths_func_univ_eq  p t))].
    exact (@equiv_inv _ _ _ (X (good_sheafification_unit T a) (good_sheafification_unit T b)) X0).
  Defined.

  Lemma good_sheafification_unit_paths_are_nj_paths_retr (T:TruncType (n.+1)) (a b:T)
  : Sect (good_sheafification_unit_paths_are_nj_paths_inv T a b) (good_sheafification_unit_paths_are_nj_paths_fun T a b).
    unfold good_sheafification_unit_paths_are_nj_paths_fun, good_sheafification_unit_paths_are_nj_paths_inv.
    intro x.
    apply (moveR_transport_V idmap _ _ x).
    unfold pr1_path. simpl.

    pose (s := eissect (path_sigma_hprop (good_sheafification_unit T a) (good_sheafification_unit T b))).
    unfold Sect in s; cbn in s; unfold pr1_path in s; cbn in s.
    rewrite s; clear s.
    unfold ap10, path_forall; rewrite eisretr.

    assert (rew := eissect _ (IsEquiv := isequiv_unique_subuniverse n nj (O nj (BTT (a = b))) (O nj (BTT (b = b))))). unfold Sect in rew; simpl in rew; unfold pr1_path in rew.
    rewrite rew; clear rew.

    pose (eisretr _ (IsEquiv := isequiv_ap_trunctype (O nj (BTT (a = b))) (O nj (BTT (b = b))))).
    unfold Sect in s; cbn in *; rewrite s; clear s.
    rewrite transport_idmap_path_universe_uncurried.
     
    unfold mu_modal_paths_func_univ_func, δ. simpl.

    revert x.
    transparent assert (sh : ((O nj (BTT (a = b))) -> subuniverse_Type nj)).
    { intro x.
      refine (Build_subuniverse_Type _ nj (BTT (O_unit nj (BTT (b = b)) 1 =
   O_rec sheaf_def_and_thm.n nj (BTT (a = b)) (O nj (BTT (b = b)))
     (λ u : a = b,
      O_rec sheaf_def_and_thm.n nj
        {|
        trunctype_type := a = b;
        istrunc_trunctype_type := istrunc_paths a b |} 
        (O nj (BTT (b = b))) (λ v : a = b, O_unit nj (BTT (b = b)) (v^ @ u))
        x) x)) _).
    admit. admit. }
      refine (O_rec_dep _ sh _).1.
      unfold sh; clear sh; intro x; simpl.
              
      pose (foo := λ P Q f, ap10 (O_rec_retr n nj P Q f)).
      simpl in foo.
      rewrite foo. rewrite foo. apply ap. hott_simpl.
  Qed.
  
  Lemma good_sheafification_unit_paths_are_nj_paths_sect (T:(n.+1)-Type) (a b:T)
  : Sect (good_sheafification_unit_paths_are_nj_paths_fun T a b) (good_sheafification_unit_paths_are_nj_paths_inv T a b).
    unfold good_sheafification_unit_paths_are_nj_paths_fun, good_sheafification_unit_paths_are_nj_paths_inv.
    intro p.
    simpl.
    unfold good_sheafification_unit, toIm in p. simpl in p.

    apply (@equiv_inj _ _ (equiv_inv ((path_sigma_hprop (good_sheafification_unit T a) (good_sheafification_unit T b))))).
    apply isequiv_inverse.
    rewrite eissect.
    apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _));
      unfold path_forall; rewrite eisretr.
    apply path_forall; intro t.

    apply (@equiv_inj _ _ (equiv_inv _ (IsEquiv := isequiv_unique_subuniverse _ _ _ _)));
      [apply isequiv_inverse | rewrite eissect].
      
    apply (@equiv_inj _ _ _ (isequiv_ap_trunctype _ _)).
    
    pose (s := λ A B, eisretr _ (IsEquiv := isequiv_ap_trunctype (n := n) A B)).
    unfold Sect in s; cbn in *. rewrite s; clear s.
    unfold symmetric_equiv.

    path_via (ap trunctype_type (ap (@st sheaf_def_and_thm.n nj) (apD10 p ..1 t)))^^.
    rewrite path_universe_V_uncurried.
    apply ap.
    apply (@equiv_inj _ _ _ (isequiv_equiv_path _ _)); unfold path_universe_uncurried; rewrite eisretr. 
    
    apply path_equiv.
    unfold mu_modal_paths_func_univ_inv, mu_modal_paths_func_univ_func, δ. simpl.

    apply (@equiv_inj _ _ _ (O_equiv n nj (BTT (b = t)) (O nj (BTT (a = t))))).
    rewrite O_rec_retr.
    apply path_forall; intro u. simpl in *.
      
    destruct u.
    unfold ap10, pr1_path; cbn.

    apply (ap10 (g:=idmap)).
    etransitivity; [idtac | exact (O_rec_sect n nj (BTT (a=b)) (O nj (BTT (a=b))) idmap)].
    apply ap. apply path_forall; intro v. apply ap. apply concat_p1.
  Defined.


  (* Proposition 36 *)
  Theorem good_sheafification_unit_paths_are_nj_paths (T:(n.+1)-Type) (a b:T) : (good_sheafification_unit T a = good_sheafification_unit T b) <~> (O nj (BTT (a=b))).
  Proof.
    refine (equiv_adjointify _ _ _ _).
    - apply good_sheafification_unit_paths_are_nj_paths_fun.
    - apply good_sheafification_unit_paths_are_nj_paths_inv.
    - apply good_sheafification_unit_paths_are_nj_paths_retr.
    - apply good_sheafification_unit_paths_are_nj_paths_sect.
  Qed.

  (* Left-exactness of sheafification *)
  Definition sheafification_left_exact
    : IsLex sheafification_modality.
  Proof.
    intros A x y H. simpl.
    Transparent O. cbn. Opaque O.
    refine (contr_equiv' _ (cumulativity (BTT (x=y)) _)).
    apply (@trunc_equiv' (good_sheafification_unit A x = good_sheafification_unit A y) ((O nj (BTT (x=y)))) (good_sheafification_unit_paths_are_nj_paths A x y) -2).
    apply (@contr_paths_contr).
    simpl in H.
    unfold good_sheafification. simpl.
    exact H.
  Defined.
    
  Definition sheafification_hprop (T:TruncType n.+1) (HT : IsHProp T)
    : ((Oj (BuildTruncType -1 T)).1 : Type) = (good_sheafification_Type T).
  Proof.
    assert (IsHProp (good_sheafification_Type T)).
    {
      pose (@hprop_stability ua fs (n.+1)). 
      (* pose (@hprop_stability ua fs (n.+1) (sheafification_modality)). *)
      admit.
    }

    refine (ap (trunctype_type) (path_iff_hprop (A:=pr1 (Oj (BuildhProp T))) (B:=@BuildTruncType -1 _ X) _ _)).
    - intro x.
      cbn. unfold good_sheafification_Type.
      refine (exist _ _ _).
      intro t.
      refine (Build_subuniverse_Type n nj _ _).
      revert x.

      cut ((O subuniverse_Prop (BuildhProp T)) -> (O subuniverse_Prop
          (@BuildhProp
             (Trunc (-1)
                (∃ a : T,
                 (λ t' : T, O nj (BTT (a = t'))) =
                 (λ _ : T,
                  {|
                  st := {|
                        trunctype_type := Unit;
                        istrunc_trunctype_type := istrunc_inO_tr Unit |};
                  subu_struct := subuniverse_unit n nj |}))) (istrunc_truncation _ _)))).

      exact idmap.
      apply O_rec.
      intro x; cbn in x.
      apply (O_unit subuniverse_Prop). apply tr.
      exists x. cbn. apply path_forall; intro t.
      apply unique_subuniverse. apply path_trunctype.
      cbn. equiv_via (O nj (BTT Unit)).
      apply function_lift_equiv'. exact fs.
      refine (equiv_adjointify _ _ _ _).
      intro p; exact tt.
      intro tt; apply path_ishprop.
      intro y; apply path_ishprop.
      intro y; apply path_ishprop.
      apply equiv_path.
      apply OUnit_is_Unit. exact ua. exact fs.
    - intros [u p]. 
      revert p.
      apply Oj_equiv.
      apply Trunc_rec.
      intros [a p]. destruct p.
      apply Oj_unit.
      exact a.

      (* Another proof, using [cumulativity] *)
      
      (* apply path_universe_uncurried. *)
      (* pose (e:= cumulativity (@BuildTruncType n T (@trunc_leq -1 n tt _ _)) _). *)
      (* match goal with *)
      (* |[e: _ <~> ?XX |- _] => equiv_via XX *)
      (* end. *)
      (* Focus 2. apply equiv_path. apply ap. apply path_trunctype. apply equiv_idmap. *)
      (* etransitivity; try exact e; clear e. *)
      (* pose (j_is_nj (BuildhProp T)). *)
      (* apply equiv_path; exact p. *)
  Admitted.

  
  Lemma Trunc_Trunc_S_fun:
    ∀ (X : Type) (i : trunc_index), Trunc i X → Trunc i (Trunc i.+1 X).
  Proof.
    intros X i.
    refine (Trunc_rec _).
    exact (tr o tr).
  Defined.

  Lemma Trunc_Trunc_S (X:Type) (i:trunc_index)
    : Trunc i X <~> Trunc i (Trunc i.+1 X).
  Proof.
    refine (equiv_adjointify _ _ _ _).
    - apply Trunc_Trunc_S_fun.
    - refine (Trunc_rec _). refine (Trunc_rec _).
      exact tr.
    - refine (Trunc_ind _ _). refine (Trunc_ind _ _).
      intro a; reflexivity.
    - refine (Trunc_ind _ _).
      intro a; reflexivity.
  Defined.

End Sheafification.
