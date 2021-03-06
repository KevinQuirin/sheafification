
Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import PathGroupoid_ Forall_ Equivalences_ epi_mono reflective_subuniverse modalities.
Require Import nat_lemmas.
Require Import sheaf_base_case.
Require Import sheaf_def_and_thm.
Require Import OPaths T T_telescope Tf_Omono_sep OT OT_Tf.
Require Import Limit.


Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
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
    simple refine trunc_sigma.
    simple refine trunc_forall. intro t.
    exact (@subuniverse_Type_is_TruncTypeSn _ nj ua).
  Defined.

  Definition E_to_χ_map_ap (T U:TruncType (trunc_S n)) {E} (χ : EnJ E) (f : E -> T)
             (g : T -> U) {x y} (e : x = y) : 
    ap (fun u => g o u) (ap (E_to_χ_map T χ) e) = ap (E_to_χ_map U χ) (ap (fun u => g o u) e).
    destruct e; reflexivity.
  Defined.

  Instance separated_mono_is_separated_ {T U:TruncType (trunc_S n)} {E} χ g h (f: T -> U)
        (H:IsEquiv (ap (E_to_χ_map U (E:=E) χ) (x:=f o g) (y:=f o h))) (fMono : IsMonof f) : 
           IsEquiv (ap (E_to_χ_map T (E:=E) χ) (x:=g) (y:=h)).
  apply (isequiv_adjointify (fun X => @equiv_inv _ _ _ (fMono E g h) (@equiv_inv _ _ _ H (ap (fun u => f o u) X)))).
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
    simple refine (separated_mono_is_separated_ _ _ _ _ (H E χ (f o x) (f o y)) fMono).
  Defined.

  Definition T_nType_j_Type_trunc (T:Type) : IsTrunc (trunc_S n) (T -> subuniverse_Type nj).
  Proof.
    simple refine trunc_forall. intro t.
    exact (@subuniverse_Type_is_TruncTypeSn _ nj ua).
  Defined.

  Definition T_nType_j_Type_isSheaf
    : forall T, Snsheaf_struct (@BuildTruncType _ (T -> subuniverse_Type nj) (T_nType_j_Type_trunc T)).
  Proof.
    intro T.
    simple refine (dep_prod_SnType_j_Type T (λ _, ((BuildTruncType _ (subuniverse_Type nj)); nType_j_Type_is_SnType_j_Type))).
  Defined.

  (* For any type [T], [T -> subuniverse_Type] is modal *)
  Definition T_nType_j_Type_sheaf T : SnType_j_Type :=  ((BuildTruncType _ (T -> subuniverse_Type nj); T_nType_j_Type_isSheaf _)).

  (* Proposition 27 *)
  Definition separated_Type_is_separated (T:TruncType (trunc_S n)) : separated (@BuildTruncType _ (separated_Type T) (separated_Type_is_TruncType_Sn T)).
    apply (@separated_mono_is_separated
              (@BuildTruncType _ (separated_Type T) (separated_Type_is_TruncType_Sn T))
              (BuildTruncType _ (T -> subuniverse_Type nj))
              (sheaf_is_separated (T_nType_j_Type_sheaf T))
              (pr1 )).
    intros X f g. simpl in *.
    apply @isequiv_adjointify with (g := λ H, (path_forall (λ x, path_sigma _ _ _ (ap10 H x) (path_ishprop _ _)))).
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
      simple refine (ap10 (f:= (O_rec n nj (BTT (a = t))
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

      simple refine (ap10 (f:= (O_rec n nj (BTT (b = t))
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
      [exact (snd (mu_modal_paths_func_univ_eq T a b p t)) | exact (fst (mu_modal_paths_func_univ_eq T a b p t))].
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
      simple refine (Build_subuniverse_Type _ nj (BTT (O_unit nj (BTT (b = b)) 1 =
   O_rec sheaf_def_and_thm.n nj (BTT (a = b)) (O nj (BTT (b = b)))
     (λ u : a = b,
      O_rec sheaf_def_and_thm.n nj
        {|
        trunctype_type := a = b;
        istrunc_trunctype_type := istrunc_paths a b |} 
        (O nj (BTT (b = b))) (λ v : a = b, O_unit nj (BTT (b = b)) (v^ @ u))
        x) x)) _). }
      simple refine (O_rec_dep _ sh _).1.
      unfold sh; clear sh; intro x; simpl.
              
      pose (foo := λ P Q f, ap10 (O_rec_retr n nj P Q f)).
      simpl in foo.
      rewrite foo. rewrite foo. apply ap. hott_simpl.
  Qed.
  
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
  (*   simple refine (equiv_adjointify _ _ _ _). *)
  (*   - apply separated_unit_paths_are_nj_paths_fun. *)
  (*   - apply separated_unit_paths_are_nj_paths_inv. *)
  (*   - apply separated_unit_paths_are_nj_paths_retr. *)
  (*   - apply separated_unit_paths_are_nj_paths_sect. *)
  (* Qed. *)

  Theorem separated_unit_paths_are_nj_paths (T:(n.+1)-Type) (a b:T)
    : IsEquiv (separated_unit_paths_are_nj_paths_inv T a b).
  Proof.
      simple refine (isequiv_adjointify _ _ _).
    - apply separated_unit_paths_are_nj_paths_fun.
    - apply separated_unit_paths_are_nj_paths_sect.
    - apply separated_unit_paths_are_nj_paths_retr.
  Defined.
    

  Lemma Omono_sep_separated_unit (T:TruncType (n.+1))
    : Omono_sep T _ (separated_Type_is_separated T) (separated_unit T).
  Proof.
    intros x y.
    simple refine (isequiv_homotopic (separated_unit_paths_are_nj_paths_inv T x y) _).
    apply separated_unit_paths_are_nj_paths.
    
    intro p. unfold separated_unit_paths_are_nj_paths_inv.
    apply (@equiv_inj _ _ (equiv_inv ((path_sigma_hprop (separated_unit T x) (separated_unit T y))))). apply isequiv_inverse. rewrite eissect.
    apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)). unfold path_forall; rewrite eisretr.
    apply path_forall; intro t.
    apply (@equiv_inj _ _ (equiv_inv _ (IsEquiv := isequiv_unique_subuniverse _ _ _ _)));
      [apply isequiv_inverse | rewrite eissect].
    apply (@equiv_inj _ _ _ (isequiv_ap_trunctype _ _)).
    pose (s := λ A B, eisretr _ (IsEquiv := isequiv_ap_trunctype (n := n) A B)).
    unfold Sect in s; cbn in *. rewrite s; clear s.
    unfold symmetric_equiv.

    match goal with
    |[|- _ = ?xx] => path_via (xx^^)
    end.
    rewrite path_universe_V_uncurried.
    apply ap.
    apply (@equiv_inj _ _ _ (isequiv_equiv_path _ _)); unfold path_universe_uncurried; rewrite eisretr. 
    
    apply path_equiv.
    unfold mu_modal_paths_func_univ_inv, mu_modal_paths_func_univ_func, δ. simpl.
    
    apply (@equiv_inj _ _ _ (O_equiv n nj (BTT (y = t)) (O nj (BTT (x = t))))).
    rewrite O_rec_retr.
    apply path_forall; intro u. simpl in *.
    
    destruct u.
    unfold ap10, pr1_path; cbn.
    match goal with
    |[|- ?ff p = transport idmap (ap trunctype_type
                                     (ap (@st sheaf_def_and_thm.n nj)
                                         (apD10 (ap pr1 (?gg p)) y)))^
                 (O_unit nj (BTT (y = y)) 1)]
     => set (F := ff);
       set (G := λ p, transport idmap (ap trunctype_type
                                          (ap (@st sheaf_def_and_thm.n nj)
                                              (apD10 (ap pr1 (gg p)) y)))^
                      (O_unit nj (BTT (y = y)) 1))
    end.
    path_via (G p).
    revert p.
    simple refine (O_rec_dep _ (λ p, Build_subuniverse_Type n nj (BuildTruncType _ (F p = G p)) _) _).1.
    intro p; cbn. unfold F; clear F; unfold G; clear G.
    repeat rewrite (λ P Q f, ap10 (O_rec_retr n nj P Q f)).
    destruct p; cbn. reflexivity.
  Qed.
  
  Lemma OT_to_sep (E S:TruncType (n.+1)) (sepS: separated S) (f:E -> S)
        (oT := Trunc (n.+1) (OTid E)) 
  : oT -> S.
  Proof.
    simple refine (Trunc_rec _).
    simple refine (OTid_rec _ _ _ _ _).
    exact f.
    intros a b. simple refine (O_rec n nj _ (Build_subuniverse_Type n nj _ (separated_nj_paths S sepS (f a) (f b))) _).
    exact (ap f).
    intro a; cbn.
    exact (ap10 (O_rec_retr n nj
                            {|
                              trunctype_type := a = a;
                              istrunc_trunctype_type := istrunc_paths a a |}
                            {|
                              st := {|
                                     trunctype_type := f a = f a;
                                     istrunc_trunctype_type := istrunc_paths (f a) (f a) |};
                              subu_struct := separated_nj_paths S sepS (f a) (f a) |} 
                            (ap f)) 1).
  Defined.

  Lemma OT_to_sep_eq (E S:TruncType (n.+1)) (sepS: separated S) (f g:E -> S)
        (oT := Trunc (n.+1) (OTid E)) (g1: oT -> S)
        (c: g1 o (tr o (@Ot E)) = g)
        (f1 := OT_to_sep E S sepS f)
        (eq: f = g)
    : f1 = g1.
  Proof.
    unfold f1, OT_to_sep. clear f1.
    apply path_forall.
    simple refine (Trunc_ind _ _); cbn.
    simple refine (path_OT _ _ _ _ _ _ _); cbn.
    
    intro x.
    path_via (g x). exact (ap10 eq x).    
    exact (ap10 c^ x).
    
    intros a b; cbn.
    match  goal with
    |[|- forall p:?XX, ?P1 @ ap ?f1 (?P2 p) = ap ?f2 (?P3 p) @ ?P4] => 
     pose (shf:= λ p:XX, Build_subuniverse_Type n nj _ (subuniverse_paths n nj
                                                                    (Build_subuniverse_Type n nj _ (separated_nj_paths S sepS (f a) (g1 (tr (Ot b)))))
                                                                    (P1 @ ap f1 (P2 p)) (ap f2 (P3 p) @ P4)))
    end.

    simple refine (O_rec_dep _ shf _).1.
    unfold shf; clear shf; cbn.
    intro p. destruct p.
    simple refine (_ @ ((OT_rec_beta_Otp E S f _ _ a a °1)^ @@ 1)).
    cbn.
    match goal with
    |[|- _ = O_rec n nj ?PP ?QQ ?ff _ @ _] =>
     simple refine (_ @ ((ap10 (O_rec_retr n nj PP QQ ff) 1)^ @@ 1))
    end.
    cbn.
    match goal with |[|- _ = 1 @ ?xx] => path_via (xx @ 1) end.
    apply whiskerL.
    
    match goal with |[|- ap ?ff _ = _] => path_via (ap (x:= Ot a) ff 1) end.
    apply ap.
    apply Otp_1.

    simple refine (concat_p1 _ @ _). symmetry; apply concat_1p.
    
    Opaque O_rec_dep.
    abstract (
        intro a; cbn;
        match goal with |[|- (pr1 ?ff) °1 = _ ]
                         => pose (pp := pr2 ff 1)
        end;
        cbn in pp; rewrite pp; clear pp;
        rewrite transport_paths_FlFr; cbn;
        rewrite (concat_p1 (ap (ap (λ x : OTid E, g1 (tr x))) (Otp_1 a)));
        rewrite ap_V; rewrite inv_V;
        rewrite concat_ap_pFq;
        match goal with
        |[|- (?P1 @ ?P2) @ ?P3 = ?P4 @ _ ] 
         => rewrite (concat_pp_p (p:=P1))
        end;
        apply whiskerL; rewrite concat_concat2;
        cbn;
        rewrite concat_ap_Fpq; unfold whiskerR;
        rewrite ap_V;

        match goal with
        |[|- ?P1 @@ 1 = ?P2 @@ 1] => assert (rr: P1 = P2)
        end;
        [idtac | destruct rr; reflexivity];
        rewrite <- inv_pp;
        apply ap;
        match goal with
        |[|- _ = ap (ap ?ff) ?rr] => 
         rewrite <- (ap02_is_ap _ _ ff _ _ _ _ rr)
        end;
        rewrite OT_rec_beta_Otp_1;
        reflexivity ).
  Defined.

  Lemma ap10_OT_to_sep_eq (E S:TruncType (n.+1)) (sepS: separated S) (f g:E -> S)
        (oT := Trunc (n.+1) (OTid E)) (g1: oT -> S)
        (c: g1 o (tr o (@Ot E)) = g)
        (f1 := OT_to_sep E S sepS f)
        (eq: f = g) x
    : ap10 (OT_to_sep_eq E S sepS f g g1 c eq) (tr (Ot x)) = ap10 eq x @ ap10 c^ x.
  Proof.
    unfold ap10 at 1. unfold OT_to_sep_eq at 1.
    unfold path_forall. rewrite eisretr. cbn.
    reflexivity.
  Defined.
  
  Lemma OT_to_sep_coh (E S:TruncType (n.+1)) (sepS: separated S) (f g:E -> S)
        (oT := Trunc (n.+1) (OTid E)) (g1: oT -> S)
        (c: g1 o (tr o (@Ot E)) = g)
        (f1 := OT_to_sep E S sepS f)
        (eq: f = g)
    : ap (λ u, u o (tr o (@Ot E))) (OT_to_sep_eq E S sepS f g g1 c eq) @ c @ eq^ = 1.
  Proof.
    apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
    apply path_forall; intro x. simpl.
    pose (p:=@ap10_ap_precompose). unfold ap10 in p.
    cbn in p.
    do 2 rewrite apD10_pp.
    rewrite (p _ _ _ (λ x0, (tr (Ot x0))) _ _ (OT_to_sep_eq E S sepS f g g1 c eq) x).
    unfold OT_to_sep_eq. unfold path_forall; rewrite eisretr.
    simpl. 
    unfold ap10.
    do 2 rewrite apD10_V.
    apply moveR_pV.
    rewrite concat_pV_p.
    rewrite concat_1p. reflexivity.
  Defined.

  Definition separation_colimit_OTtelescope_cocone (U V:TruncType (n.+1)) (sepV:separated V)
          (f:U -> V)
    : cocone (OTtelescope U) V.
  Proof.
    transparent assert (F : (forall i, (OTtelescope U) i → V)).
    { intro i; cbn. induction i.
      exact f.
      apply OT_to_sep. exact sepV. exact IHi. }
    simple refine (Build_cocone _ _).    
    - exact F.
    - intros i j q; destruct q.
      induction i.
      + intro x; reflexivity.
      + intro x; cbn.
        reflexivity.
  Defined.

  Theorem isequiv_separation_colimit_OTtelescope_cocone (U V:TruncType (n.+1)) (sepV:separated V)
    : IsEquiv (separation_colimit_OTtelescope_cocone U V sepV).
  Proof.
    simple refine (isequiv_adjointify _ _ _).
    - intro C. exact (C 0).
    - intro C.
      simple refine (path_cocone _ _).
      + intro i. apply ap10.
        induction i.
        reflexivity.
        cbn.
        match goal with
        |[|- OT_to_sep ?X1 ?X2 ?X3 ?X4 = _]
         => apply (OT_to_sep_eq X1 X2 X3 X4 (C i) (C (i.+1)))
        end.
        exact (path_forall (qq C i (i.+1) 1)).
        exact IHi.
      + intros i j g x. destruct g; simpl.
        induction i.
        
        cbn.
        unfold OT_to_sep_eq; cbn.
        unfold ap10 at 1, path_forall at 1. rewrite eisretr. cbn.
        unfold ap10, path_forall.
        rewrite apD10_V. rewrite eisretr. rewrite concat_1p.
        symmetry; apply concat_Vp.
        
        cbn. rewrite concat_1p.
        rewrite ap10_OT_to_sep_eq.
        rewrite concat_pp_p.
        match goal with |[|- ?XX = _ ] => path_via (XX @ 1) end.
        apply whiskerL.
        unfold ap10, path_forall. rewrite apD10_V. rewrite (eisretr apD10).
        symmetry; apply concat_Vp.
    - intro f; reflexivity.
  Defined.
  
  Theorem separation_colimit_OTtelescope (U:TruncType (n.+1))
    : is_m_universal (n.+1)
                     (separation_colimit_OTtelescope_cocone
                        U
                        (@BuildTruncType _ (separated_Type U) (separated_Type_is_TruncType_Sn U))
                        (separated_Type_is_separated U)
                        (separated_unit U)).
  Proof.
    pose (@is_colimit_Im_OTtelescope ua fs U (@BuildTruncType _ (separated_Type U) (separated_Type_is_TruncType_Sn U)) (separated_unit U) (separated_Type_is_separated U) (Omono_sep_separated_unit U) (IsSurjection_toIm _ _ _)).

    assert (is_m_colimit_C (n.+1) _ _ i = ((separation_colimit_OTtelescope_cocone U
        {|
        trunctype_type := separated_Type U;
        istrunc_trunctype_type := separated_Type_is_TruncType_Sn U |}
        (separated_Type_is_separated U) (separated_unit U)))).
    { apply (@equiv_inj _ _ (equiv_inv _ (IsEquiv := isequiv_separation_colimit_OTtelescope_cocone U _ (separated_Type_is_separated U)))).
      apply isequiv_inverse. 
      reflexivity. }
    exact (X # is_m_colimit_H _ _ _ i).
  Qed.    

  Definition separated_equiv : forall (P : TruncType (trunc_S n)) (Q :{T : TruncType (trunc_S n) & separated T}),
                                 IsEquiv (fun f : separated_Type P -> Q.1 =>
                                            f o (separated_unit P)).
  Proof.
    intros P [Q sepQ].
    pose (G := separation_colimit_OTtelescope P Q).
    match goal with |[G:IsEquiv ?ff |- _] => pose (F := ff) end.
    simple refine (isequiv_compose' F _ (λ C, C 0) _).
    - exact (isequiv_inverse _ (feq := isequiv_separation_colimit_OTtelescope_cocone P Q sepQ)).
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
    simple refine (@Build_EnJ _ _ _).
    - intro x. apply χ. exact x.1.
    - intros e0.
      pose (dense_eq _ χ e0.1).
      etransitivity; try exact p.
      apply path_universe_uncurried.
      simple refine (equiv_adjointify _ _ _ _).
      + intros [e' q]. destruct q. exists e0.1. reflexivity.
      + intros [e' q]. destruct q. exists e0. reflexivity.
      + intros [e' q]. destruct q. reflexivity.
      + intros [e' q]. destruct q. reflexivity.
  Defined.

  (* Proposition 31 *)
  Definition separated_modality : Modality (trunc_S n).
    simple refine (Build_Modality _ separation_reflective_subuniverse _).
    intros A B. simpl in *.
    destruct A as [A sepA]. simpl in sepA.
    unfold separated.
    intros E χ f g. simpl in *.
    simple refine (isequiv_adjointify _ _ _).
    - unfold E_to_χ_map; simpl. intros H. simpl in H.
      apply path_forall; intro x.
      simple refine (path_sigma _ _ _ _ _).
      apply (ap10 (f := (pr1 o f)) (g := (pr1 o g))).
      apply (equiv_inv _ (IsEquiv := sepA E χ (pr1 o f) (pr1 o g))).
      apply path_forall; intro y. exact (ap10 H y)..1.
      simpl.
      pose (p := @subu_struct _ _ (B (g x).1)).
      simpl in p.
      specialize (p {e':E & e' = x}).
      specialize (p (density_sigma _ χ x)).
      unfold equiv_inv.
      unfold IsMono in p; simpl in p.
      specialize (p (λ z, transport (λ u, B (g u).1) z.2 (transport (λ x0 : A, B x0)
     (ap10
        ((let
          (equiv_inv, eisretr, eissect, _) :=
          sepA E χ (λ x0 : E, let (proj1_sig, _) := f x0 in proj1_sig)
            (λ x0 : E, let (proj1_sig, _) := g x0 in proj1_sig) in
          equiv_inv)
           (path_forall
              
              
              (λ y : ∃ x0 : E, χ x0, (ap10 H y) ..1))) z.1) 
     (f z.1).2))).
      specialize (p (λ z, transport (λ u, B (g u).1) z.2 (g z.1).2)).

      pose (X := λ X, (ap10 (equiv_inv _ (IsEquiv := p) X) (x;1)));
        simpl in X; apply X; clear X.
      unfold E_to_χ_map; simpl.
      apply path_forall; intros [[a b] c]; simpl in *.
      apply ap. clear b.

      etransitivity; try exact ((ap10 H (a;c))..2). simpl.
      apply (ap (λ u, transport _ u (f a).2)).
      unfold pr1_path.
      pose (p0 := ap10_ap_precompose (pr1 : {e:E & (χ e)} -> E) ((let (equiv_inv, eisretr, eissect, _) :=
           sepA E χ (λ x0 : E, (f x0).1) (λ x0 : E, (g x0).1) in
       equiv_inv)
        (path_forall 
           (λ y : ∃ b : E, (χ b), ap pr1 (ap10 H y)))) (a;c)). simpl in p0.
      apply (transport (λ u, u = _) p0); clear p0.

      pose (eisretr _ (IsEquiv := sepA E χ (λ x0 : E, (f x0).1) (λ x0 : E, (g x0).1)) (path_forall
           (λ y : ∃ b : E, (χ b), ap pr1 (ap10 H y)))).
      unfold Sect, equiv_inv, E_to_χ_map in p0.
      pose (p1 := ap (λ u, ap10 u (a;c)) p0). simpl in p1.
      etransitivity; [exact p1 |
      exact (apD10 (eisretr (apD10 (f:=(λ x0 : ∃ b : E, (χ b), (f x0.1).1)) (g:=(λ x0 : ∃ b : E, (χ b), (g x0.1).1))) (IsEquiv := isequiv_apD10 _ _ (λ x0 : ∃ b : E, (χ b), (f x0.1).1) (λ x0 : ∃ b : E, (χ b), (g x0.1).1)) (λ y : ∃ b : E, (χ b), ap pr1 (ap10 H y))) (a;c))].
      
    - intro p. unfold E_to_χ_map in *; simpl in *.
      apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
      apply path_forall; intro e.

      pose (s:= @ap10_ap_precompose); unfold ap10 in s; rewrite s; clear s.
      unfold path_forall at 1. rewrite eisretr.

      unfold path_sigma.
      apply (@equiv_inj _ _ (equiv_inv _ (IsEquiv := isequiv_path_sigma))).
      apply isequiv_inverse.
      rewrite eissect. simpl.
      unfold pr1_path, pr2_path.
      simple refine (path_sigma' _ _ _).
      { pose (p0 := ap10_ap_precompose (pr1 : {e:E & χ e} -> E) ((let (equiv_inv, eisretr, eissect, _) :=
                                                                    sepA E χ (pr1 o f) (pr1 o g) in
                                                                equiv_inv)
                                                                 (path_forall 
                                                                              (λ y : ∃ b : E, χ b, ap pr1 (ap10 p y)))) e).
        apply (transport (λ u, u=_) p0). clear p0.

        pose (p0 := eisretr _ (IsEquiv := sepA E χ (λ x0 : E, (f x0).1) (λ x0 : E, (g x0).1)) (path_forall (λ y : ∃ b : E, χ b, ap pr1 (ap10 p y)))).
        unfold Sect, equiv_inv, E_to_χ_map in p0. 
        apply (transport (λ u, ap10 u e = _) p0^). clear p0.
        exact (apD10 (eisretr (apD10 (f:=(λ x0 : ∃ b : E, χ b, (f x0.1).1)) (g:=(λ x0 : ∃ b : E, χ b, (g x0.1).1))) (IsEquiv := isequiv_apD10 _ _ (λ x0 : ∃ b : E, χ b, (f x0.1).1) (λ x0 : ∃ b : E, χ b, (g x0.1).1)) (λ y : ∃ b : E, χ b, ap pr1 (ap10 p y))) e). 
}
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
        
        pose (p0 := @ap10_ap_precompose {e:{e:E & e=a} & χ e.1} {e:E &e=a} (B (g a).1) pr1 _ _ t ((a;1);c)). simpl in p0.
        rewrite <- p0; clear p0.
        unfold t; clear t.
        unfold equiv_inv.
        pose (rew := eisretr _ (IsEquiv := (@subu_struct _ _ (B (g a).1)) (∃ e' : E, e' = a) (density_sigma _ χ a)
                (λ z : ∃ e' : E, e' = a,
                 transport (λ u : E, B (g u).1) z.2
                   (transport (λ x0 : A, B x0)
                      (ap10
                         ((let (equiv_inv, eisretr, eissect, _) :=
                               sepA E χ (λ x : E, (f x).1) (λ x : E, (g x).1) in
                           equiv_inv)
                            (path_forall 
                               (λ y : ∃ b : E, χ b, (ap10 p y) ..1))) z.1)
                      (f z.1).2))
                (λ z : ∃ e' : E, e' = a,
                   transport (λ u : E, B (g u).1) z.2 (g z.1).2))).
        unfold Sect in rew. rewrite rew; clear rew.
        pose (ap10_path_forall (λ x : ∃ b : ∃ e' : E, e' = a, χ b.1,
         transport (λ u : E, B (g u).1) (x.1).2
           (transport (λ x0 : A, B x0)
              (ap10
                 ((let (equiv_inv, eisretr, eissect, _) :=
                       sepA E χ (λ x0 : E, (f x0).1) (λ x0 : E, (g x0).1) in
                   equiv_inv)
                    (path_forall 
                       (λ y : ∃ b : E, χ b, (ap10 p y) ..1))) 
                 (x.1).1) (f (x.1).1).2))
              (λ x : ∃ b : ∃ e' : E, e' = a, χ b.1,
                 transport (λ u : E, B (g u).1) (x.1).2 (g (x.1).1).2)).
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
      apply (@equiv_inj _ _ (equiv_inv _ (IsEquiv := isequiv_path_forall f g))). apply isequiv_inverse.
      rewrite eissect. simpl.
      apply path_forall; intro x. simpl.
      apply (@equiv_inj _ _ (equiv_inv _ (IsEquiv := isequiv_path_sigma))). apply isequiv_inverse.
      unfold path_sigma.
      rewrite eissect. simpl.

      simple refine (path_sigma' _ _ _).
      { destruct p. simpl.
        simple refine (apD10 _ _). intro y; reflexivity.
        
        unfold equiv_inv.
        path_via (ap10 ((let (equiv_inv, eisretr, eissect, _) :=
                             sepA E χ (pr1 o f) (pr1 o f) in
                         equiv_inv)
                          1)).
        apply ap. apply ap. apply path_forall_1.
        apply (moveR_equiv_V (f := path_forall (f:=_) (g:=_)) (H := isequiv_path_forall _ _)).
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
             transport (λ u : E, B (f u).1) z.2
               (transport (λ x0 : A, B x0)
                  (ap10
                     ((let (equiv_inv, eisretr, eissect, _) :=
                           sepA E χ (pr1 o f) (pr1 o f) in
                       equiv_inv)
                        (path_forall 
                           (λ y : ∃ b : E, χ b, 1))) z.1) 
                  (f z.1).2)) ==
            (λ z : ∃ e' : E, e' = x,
               transport (λ u : E, B (f u).1) z.2 (f z.1).2))).
        { intro u. apply ap.
          path_via (transport (λ x0 : A, B x0) 1 (f u.1).2); try auto.
          apply (ap (λ p, transport (λ x0 : A, B x0) p (f u.1).2)). simpl.
          simple refine (apD10 _ _). intro v. reflexivity.
          path_via (ap10 ((let (equiv_inv, eisretr, eissect, _) :=
                             sepA E χ (pr1 o f) (pr1 o f) in
                         equiv_inv)
                            1)).
          apply ap. apply ap. apply path_forall_1.
          apply (moveR_equiv_V (f := path_forall (f:=_) (g:=_)) (H := isequiv_path_forall _ _)).
          etransitivity; try (symmetry; apply path_forall_1).
          apply moveR_equiv_V. reflexivity. }
        
        match goal with
          |[ |- @ap10 ?XXX ?XY ?Xf ?Xg ?XH ?Xu = ?X2 ] => 
           assert (foo := λ p, apD10 (@equiv_inj _ _ (equiv_inv _ (IsEquiv := isequiv_apD10 _ _ Xf Xg)) (isequiv_inverse _) (ap10 XH) XX p) (x;1))
        end.
        transitivity (XX (x;1)).
        apply foo.
        { unfold XX; clear foo; clear XX.
          unfold path_forall_1, eta_path_forall.
          unfold moveR_equiv_V. simpl.
          rewrite eissect.
          apply moveR_equiv_V. simpl.
          apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
          unfold path_forall at 3. rewrite eisretr.
          apply path_forall; intros [[b p] c]. simpl in *. destruct p. simpl.
          unfold E_to_χ_map.
          simpl.
          match goal with
            |[|- _ = apD10 (ap _ ?X) ?Y] => 
          apply (transport (λ U, _ = U) (ap10_ap_precompose (C := B (f b).1) (pr1 : {e:(∃ e' : E, e' = b) & χ e.1} -> (∃ e' : E, e' = b)) X Y)^) end.
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

          
          pose (apD10_ap_precompose (pr1 : {e:E & χ e} -> E) foo (b;c))^.
          simpl in p.
          rewrite p. clear p. unfold foo; clear foo.
          match goal with
              |[|- _ = _ @ (apD10 ?X ?Y)^] => 
          apply (transport (λ U, _ = _ @ U) (apD10_V X Y)) end.
          rewrite concat_pp_p.
          apply (transport (λ U, _ = _ @ U) (apD10_pp (eisretr apD10 (λ y : ∃ b0 : E, χ b0, 1)) (ap (λ h : ∀ x : E, (f x).1 = (f x).1, h oD pr1)
         ((ap ap10
             (ap
                (let (equiv_inv, eisretr, eissect, _) :=
                     sepA E χ (λ x : E, (f x).1) (λ x : E, (f x).1) in
                 equiv_inv) (eissect apD10 1)) @
           ap apD10
             (eissect
                (ap (λ (f0 : E → A) (x : ∃ b0 : E, χ b0), f0 x.1)) 1 @
                (eissect apD10 1)^)) @ eisretr apD10 (λ v : E, 1)))^ (b;c))).

          match goal with
            |[|- _ = _ @ apD10 ?X _] => set (foo := X)
          end. simpl in foo.
          
          set (bc := (b;c)).
          match goal with
          |[|- _ = ap _ (eisretr _ (IsEquiv := ?HEL) _) @ _] => pose (HELP := HEL)
          end.
          simple refine (apD10 (g := λ bc, ap
                                      (λ
                                         x : (λ x : ∃ b0 : E, χ b0, (f x.1).1) =
                                             (λ x : ∃ b0 : E, χ b0, (f x.1).1), ap10 x bc)
                                      (eisretr (IsEquiv := HELP) (ap (λ (f0 : E → A) (x : ∃ b0 : E, χ b0), f0 x.1))
                                               (path_forall (λ y : ∃ b0 : E, χ b0, 1))) @ apD10 foo bc) _ _).
          clear bc. clear c. clear b. 
          unfold foo; clear foo.
          etransitivity; [exact (@apD _ (λ U : (λ x0 : E, (f x0).1) = (λ x0 : E, (f x0).1),
                              ∀ a : ∃ e : E, χ e,
                                ap10 (ap (λ h : E → A, h o pr1) U) a = ap10 U a.1) (ap10_ap_precompose (pr1 : {e:E & χ e} -> E)) 1
                     ((let (equiv_inv, eisretr, eissect, _) :=
                           sepA E χ (λ x0 : E, (f x0).1) (λ x0 : E, (f x0).1) in
                       equiv_inv)
                        (path_forall (λ y : ∃ b : E, χ b, 1)))
                     (ap
                        (let (equiv_inv, eisretr, eissect, _) :=
                             sepA E χ (λ x0 : E, (f x0).1) (λ x0 : E, (f x0).1) in
                         equiv_inv) (path_forall_1 (λ x : ∃ b : E, χ b, (f x.1).1)) @
                        eissect (ap (E_to_χ_map A χ)) 1)^)^ |].

          simpl.
          apply (moveR_transport_p (λ U : (λ x0 : E, (f x0).1) = (λ x0 : E, (f x0).1),
      ∀ a : ∃ e : E, χ e,
        ap10 (ap (λ h : E → A, h o pr1) U) a = ap10 U a.1)).
          unfold ap10_ap_precompose, apD10_ap_precompose.
          simpl.
          apply path_forall; intro u; simpl.

          rewrite transport_forall_constant. simpl.
          rewrite transport_paths_FlFr. hott_simpl.
          unfold path_forall_1, eta_path_forall. simpl.
          rewrite <- ap_pp.
          repeat rewrite concat_pp_p.
          repeat rewrite ap_pp.
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
            apply moveR_Vp. rewrite concat_p1.
           
            pose (apD (λ U, (eisretr (IsEquiv := IsEq) (ap (E_to_χ_map A χ))
                                     U)) (path_forall_1 (λ x0 : ∃ b0 : E, χ b0, (f x0.1).1))^).
            simpl in p.
            rewrite <- p; clear p.
            rewrite transport_paths_FlFr. unfold path_forall_1, eta_path_forall.
            rewrite ap_idmap.
            rewrite ap_V; rewrite inv_V.

            repeat rewrite ap_pp.
            repeat rewrite <- ap_compose.
            pose (ap_compose (λ x : E_to_χ_map A χ (λ x0 : E, (f x0).1) =
                E_to_χ_map A χ (λ x0 : E, (f x0).1),
          ap (E_to_χ_map A χ) ((ap (E_to_χ_map A χ))^-1 x)) (λ x : (λ x : ∃ b0 : E, χ b0, (f x.1).1) =
            (λ x : ∃ b0 : E, χ b0, (f x.1).1), 
                                                                   ap10 x u) (eissect apD10 1)). rewrite <- p.  clear p.
            unfold E_to_χ_map.
            repeat rewrite concat_pp_p. apply whiskerL.

            pose (p := ap_compose (ap (λ (h : E → A) (x0 : ∃ e : E, χ e), h (let (proj1_sig, _) := x0 in proj1_sig)))
                             (λ x, ap10 x u)
                             (eissect (IsEquiv:=IsEq) (ap (E_to_χ_map A χ)) 1)). simpl in p.
            rewrite p; clear p.
            rewrite concat_p_pp. rewrite <- (ap_pp (λ x : (λ x : ∃ b0 : E, χ b0, (f x.1).1) =
             (λ x : ∃ b0 : E, χ b0, (f x.1).1), 
                                                          ap10 x u)).
            apply moveR_Mp.
            rewrite <- (ap_V (λ x : (λ x : ∃ b0 : E, χ b0, (f x.1).1) =
             (λ x : ∃ b0 : E, χ b0, (f x.1).1), 
                                    ap10 x u)).
            match goal with
              |[|- _ = ap ?ff ?pp @ ap ?gg ?qq] => rewrite <- (ap_pp ff pp qq); set (foo := pp@qq)
            end.
            simpl in foo.
            assert (X : foo = path_forall_1 (λ x0 : ∃ b0 : E, χ b0, (f x0.1).1)).
            { unfold foo, path_forall_1, eta_path_forall.
              rewrite inv_pp. rewrite inv_V.
              pose (eisadj _ (IsEquiv := IsEq) 1). simpl in p. rewrite <- p.
              rewrite concat_pp_p. rewrite concat_Vp. rewrite concat_p1. reflexivity. }
            rewrite X; clear X; clear foo.
            unfold path_forall_1, eta_path_forall. simpl.
            unfold ap10.

            pose (p := ap_compose (λ p:(λ x : ∃ b0 : E, χ b0, (f x.1).1) =
            (λ x : ∃ b0 : E, χ b0, (f x.1).1), apD10 p) (λ f:(λ x : ∃ b0 : E, χ b0, (f x.1).1) ==
                                                                 (λ x : ∃ b0 : E, χ b0, (f x.1).1), f u) (eissect apD10 1)). simpl in p.
            rewrite p; clear p.
            
            rewrite <- (eisadj _ (IsEquiv := isequiv_apD10 (∃ b0 : E, χ b0) (λ _ : ∃ b0 : E, χ b0, A)
         (λ x0 : ∃ b0 : E, χ b0, (f x0.1).1)
         (λ x0 : ∃ b0 : E, χ b0, (f x0.1).1))). 
            reflexivity. }
          
          rewrite X123; clear X123.
          assert (X456 : P4 @ P5 @ P6 = 1).
          { unfold P4, P5, P6; clear P6; clear P5; clear P4; clear P3; clear P2; clear P1.
            rewrite apD10_V.
            rewrite concat_pp_p. apply moveR_Vp; rewrite concat_p1.
            repeat rewrite <- (ap_pp (λ h : ∀ x : E, (f x).1 = (f x).1, h oD pr1)).
            match goal with
              |[|- _ = apD10 (ap (λ h : ∀ x : E, (f x).1 = (f x).1, h oD ?ff) ?pp) ?aa] => rewrite (apD10_ap_precompose (C := λ x:E, (f x).1 = (f x).1) ff pp aa)
            end.
            rewrite concat_pp_p.
            rewrite (eisadj (apD10 (f := λ x : E, let (proj1_sig, _) := f x in proj1_sig)
                                   (g := λ x : E, let (proj1_sig, _) := f x in proj1_sig)) 1).
            rewrite ap_V. rewrite concat_Vp. rewrite concat_p1.
            match goal with
              |[|- ap ?ff ?pp @ ap ?gg ?qq = _ ] => rewrite <- (ap_pp ff pp qq)
            end.
            pose (ap_compose
                    (λ x : (λ x0 : E, (f x0).1) = (λ x0 : E, (f x0).1), ap10 x)
                    (λ x : (λ x0 : E, (f x0).1) == (λ x0 : E, (f x0).1), x u.1)
                    (ap
                       (let
                           (equiv_inv, eisretr, eissect, _) :=
                           sepA E χ (λ x0 : E, (f x0).1) (λ x0 : E, (f x0).1) in
                         equiv_inv) (eissect apD10 1) @ eissect (ap (E_to_χ_map A χ)) 1)).
            simpl in p; rewrite p; clear p.
            rewrite <- ap_pp.
            reflexivity. }
          rewrite concat_1p.
          exact X456. }
        
        { unfold XX; clear foo; clear XX. simpl.
          unfold path_forall_1, eta_path_forall.
          unfold moveR_equiv_V. simpl. hott_simpl. }
      }
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
      simple refine (isequiv_adjointify _ _ _).
      + intros f e. cbn.
        simple refine (exist _ _ _). apply (equiv_inv _ (IsEquiv := ShP E φ) (pr1 o f) e). 
        apply (equiv_inv _ (IsEquiv := clχ (equiv_inv _ (IsEquiv := ShP E φ) (pr1 o f) e))).
        generalize (equiv_path _ _ (j_is_nj (φ e).1) (φ e).2).
        apply O_rec; intro p; apply O_unit.
        apply (transport (λ u, χ u) (ap10 (eisretr (E_to_χmono_map P φ) (pr1 o f)) (e;p))^).
        exact (f (e;p)).2.
      + intros f. apply path_forall; intros [e p].
        unfold E_to_χmono_map.
        simple refine (path_sigma' _ _ _).
        exact (ap10 (eisretr (E_to_χmono_map P φ) (pr1 o f)) (e;p)). simpl.
        apply (moveR_transport_p (λ u:P, χ u)).
        apply moveR_equiv_V.
        pose (j_is_nj_unit (φ e).1).
        assert (X: (φ e).2 = (Oj_unit (φ e).1 p)) by apply path_ishprop.
        rewrite X; clear X. rewrite (j_is_nj_unit (φ e).1).
        match goal with
        |[|- O_rec _ _ ?PP ?QQ ?ff _ = _] =>
         assert (r := ap10 (O_rec_retr n nj PP QQ ff) p)
        end.
        rewrite r; clear r. reflexivity.
      + intros f. apply path_forall; intro e.
        simple refine (path_sigma' _ _ _).
        pose (eissect (E_to_χmono_map P φ)). unfold Sect, E_to_χmono_map in s.
        apply (ap10 (g:= pr1 o f)). 
        apply moveR_equiv_V. reflexivity.
        apply (moveR_transport_p (λ u:P, χ u)).
        apply moveR_equiv_V. simpl.
        match goal with
        |[|- ?XX] => assert (Subug: IsSubu n nj (BuildTruncType _ XX))
        end.
        apply subuniverse_paths. exact ua. exact fs.
        generalize (transport idmap (j_is_nj (φ e).1) (φ e).2).
        apply (O_rec n nj _ (Build_subuniverse_Type n nj _ Subug)); intro pp; simpl. clear Subug.
        pose (j_is_nj_unit (φ e).1 pp).
        assert (r: (φ e).2 = Oj_unit (φ e).1 pp) by apply path_ishprop.
        rewrite r; clear r.
        rewrite (j_is_nj_unit (φ e).1 pp).
        match goal with
        |[|- O_rec _ _ ?PP ?QQ ?ff _ = _] =>
         assert (r := ap10 (O_rec_retr n nj PP QQ ff) pp)
        end.
        rewrite r; clear r. simpl.
        unfold E_to_χmono_map. apply ap. apply (ap (λ U, transport (λ u : P, χ u) U (f e).2)).
        apply ap.
        unfold moveR_equiv_V.
        simpl.
        pose (eisadj (E_to_χmono_map P φ) (pr1 o f)).
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
    simple refine (trunc_sigma).
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
  Qed.
  
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
    simpl; simple refine (isequiv_adjointify _ _ _).
    - intro p. apply path_sigma' with p. 
      simple refine (path_ishprop _ _). apply IsMono_IsHProp_cloture. exact Monom.
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
  Qed.

  Definition separated_to_sheaf (U:SnType_j_Type) (χ:U.1 -> TruncType n) (sep: separated (BuildTruncType _ {u:U.1 & χ u})) Monom :
    Snsheaf_struct (BuildTruncType _ (@separated_to_sheaf_Type U.1 χ Monom)).
  Proof.
    simple refine (closed_to_sheaf _ _ _ _).
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
    simple refine trunc_sigma.
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
                   (Oj (BuildTruncType -1 (Trunc -1 ({a:T & (λ t' : T, (O nj (BTT (a = t')))) = u})))).1}.

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
    rewrite <- p. reflexivity.
  Qed.

  Definition good_sheafification (T:TruncType (n.+1))
  : SnType_j_Type.
    simple refine (exist _ _ _).
    exists (good_sheafification_Type T).
    simple refine trunc_sigma. apply T_nType_j_Type_trunc.
    cbn.
    match goal with
      |[|- Snsheaf_struct ?X] => assert (eq : (sheafification T).1 = X)
    end.
    apply path_trunctype.
    apply good_sheafification_Type_is_sheafification_Type.
    destruct eq.
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
    simple refine (equiv_adjointify _ _ _ _).
    - intros [e p].
      exists e.1.
      exact p.
    - intros [e he].
      simple refine (exist _ _ _).
      exists e.
      apply Oj_unit.
      exact he. exact he.
    - intros [e he].
      reflexivity.
    - intros [e p].
      simple refine (path_sigma' _ _ _).
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
    simple refine (isequiv_compose).
    - exact (separated_equiv P (existT (separated) Q sepQ)).
  Qed.

  (* Proposition 33 *)
  Definition sheafification_subu_sigma (A:TruncType n.+1) (modA : Snsheaf_struct A) (B: A -> TruncType n.+1) (modB : forall a, (Snsheaf_struct (B a))) 
  : Snsheaf_struct (BuildTruncType (n.+1) {x:A & (B x)}).
    destruct modA as [sepA sheafA].
    split.
    - assert (p := subu_sigma _ (separated_modality)). simpl in p.      
      exact (p (Build_subuniverse_Type _ separation_reflective_subuniverse A sepA) (λ a, Build_subuniverse_Type _ separation_reflective_subuniverse (B a) (fst (modB a)))). 
    - intros E χ.
      simple refine (isequiv_adjointify _ _ _).
      + simpl.
        intros φ e.
        destruct ((sheafA E χ)) as [inva retra secta _]. unfold Sect in *; simpl in *.
        pose (a := inva (pr1 o φ) e).
        exists a.
        unfold E_to_χmono_map in *; simpl in *.
        specialize (modB a).
        destruct modB as [sepB sheafB]. simpl in *.        
        specialize (sheafB {e':E & e = e'} (λ x, χ x.1)).
        simple refine (equiv_inv _ (IsEquiv := sheafB) _ (e;1)).
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
        simple refine (path_sigma' _ _ _).
        { exact (ap10 (eisretr _ (IsEquiv := sheafA E χ) (pr1 o φ)) (e;h)). }
        { destruct ((sheafA E χ)) as [inva retra secta adja]. 
          destruct (modB (inva
               (λ x : ∃ x : E, (χ x).1,
                let (proj1_sig, _) := φ x in proj1_sig) e)) as [sepB sheafB].
          destruct (sheafB (∃ e' : E, e = e') (λ x, (χ x.1))) as [invb retrb sectb adjb].
          simpl in *. clear adjb; clear adja.
          unfold Sect, E_to_χmono_map in *; simpl in *.
          simple refine (moveR_transport_p B _ _ _ _).
          match goal with
            |[|- invb ?X _ = _ ] => specialize (retrb X)
          end.
          simpl in retrb.
          apply ap10 in retrb.
          specialize (retrb ((e;1);h)). simpl in retrb.
          exact retrb. }
      + intro φ; simpl in *.
        apply path_forall; intro e.
        simple refine (path_sigma' _ _ _).
        { exact (ap10 (eissect _ (IsEquiv := sheafA E χ) (pr1 o φ)) e). }
        {
          simple refine (moveR_transport_p B _ _ _ _).

          assert (moveR_EV2 : forall (X Y:Type) (Z:X -> Type) (T:Y -> Type)
                                     (f:(forall x, Z x) -> (forall x, T x))
                                     (H:IsEquiv f)
                                     (g:forall x, Z x)
                                     (h:forall x, T x)
                                     (x:X),
                     (f g = h) -> (f^-1 h x = g x)).
          { intros X Y Z T f H g h x X0. destruct X0. rewrite eissect. reflexivity. }
          simple refine (@moveR_EV2 {e':E & e=e'} {b:{e':E & e=e'} & (χ b.1).1}
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
    simple refine (Build_subuniverse_struct _ _ _ _ _).
    - intro T. exists (Snsheaf_struct T). apply Snsheaf_struct_is_HProp.
    - intros T. exact (good_sheafification T).
    - intros T. apply good_sheafification_unit.
    - exact (λ P Q, sheafification_equiv P Q.1 Q.2).
  Defined.

  (* Proposition 34 *)
  Definition sheafification_modality : Modality (n.+1).
    simple refine (Build_Modality _ _ _).
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
      [exact (snd (mu_modal_paths_func_univ_eq T a b p t)) | exact (fst (mu_modal_paths_func_univ_eq T a b p t))].
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
      simple refine (Build_subuniverse_Type _ nj (BTT (O_unit nj (BTT (b = b)) 1 =
   O_rec sheaf_def_and_thm.n nj (BTT (a = b)) (O nj (BTT (b = b)))
     (λ u : a = b,
      O_rec sheaf_def_and_thm.n nj
        {|
        trunctype_type := a = b;
        istrunc_trunctype_type := istrunc_paths a b |} 
        (O nj (BTT (b = b))) (λ v : a = b, O_unit nj (BTT (b = b)) (v^ @ u))
        x) x)) _). }
      simple refine (O_rec_dep _ sh _).1.
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
    simple refine (equiv_adjointify _ _ _ _).
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
    simple refine (contr_equiv' _ (cumulativity (BTT (x=y)) _)).
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

    simple refine (ap (trunctype_type) (path_iff_hprop (A:=pr1 (Oj (BuildhProp T))) (B:=@BuildTruncType -1 _ X) _ _)).
    - intro x.
      cbn. unfold good_sheafification_Type.
      simple refine (exist _ _ _).
      intro t.
      simple refine (Build_subuniverse_Type n nj _ _).
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
      simple refine (equiv_adjointify _ _ _ _).
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
    simple refine (Trunc_rec _).
    exact (tr o tr).
  Defined.

  Lemma Trunc_Trunc_S (X:Type) (i:trunc_index)
    : Trunc i X <~> Trunc i (Trunc i.+1 X).
  Proof.
    simple refine (equiv_adjointify _ _ _ _).
    - apply Trunc_Trunc_S_fun.
    - simple refine (Trunc_rec _). simple refine (Trunc_rec _).
      exact tr.
    - simple refine (Trunc_ind _ _). simple refine (Trunc_ind _ _).
      intro a; reflexivity.
    - simple refine (Trunc_ind _ _).
      intro a; reflexivity.
  Defined.
End Sheafification.
