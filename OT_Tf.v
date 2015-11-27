(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import Limit.
Require Import T T_telescope.
Require Import PathGroupoid_ Forall_ Equivalences_ epi_mono reflective_subuniverse modalities OPaths.
Require Import sheaf_base_case.
Require Import sheaf_def_and_thm.
Require Import OT.
Require Import Tf_Omono_sep.
(* Require Import sheaf_induction. *)


Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
Local Open Scope type_scope.

  
Section OT_Tf.

  
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

  
Local Open Scope Opath_scope.

Lemma OTid_Tf_fun (A B:TruncType (n.+1)) (f:A -> B) (H: forall x y:A, O nj (BuildTruncType _ (x=y)) <~> (f x = f y))
      (H1: forall x:A, H x x °1 = 1) 
  : (OTid A) -> (T f).
Proof.
refine (OTid_rec _ _ _ _ _); cbn.
    + intro x. apply (@t A B f x). 
    + intros a b p. cbn.
      exact (tp a b (H a b p)).
    + intro a. cbn.
      match goal with |[|- ?XX _ = _] => path_via (XX 1) end.
      apply ap. apply H1.
      apply tp_1.
Defined.

Lemma OTid_Tf (A B:TruncType (n.+1)) (f:A -> B) (H: forall x y:A, O nj (BuildTruncType _ (x=y)) <~> (f x = f y))
      (H1: forall x:A, H x x °1 = 1) 
  : (OTid A) <~> (T f).
Proof.
  pose (H1':= (λ a : A, ap (H a a)^-1 (H1 a)^ @ eissect (H a a) °1)).
  (** See R.v for general case *)
  refine (equiv_adjointify _ _ _ _).
  - 
    refine (OTid_rec _ _ _ _ _); cbn.
    + intro x. apply (@t A B f x). 
    + intros a b p. cbn.
      exact (tp a b (H a b p)).
    + intro a. cbn.
      match goal with |[|- ?XX _ = _] => path_via (XX 1) end.
      apply ap. apply H1.
      apply tp_1.
  - 
    refine (T_rec _ _ _ _); cbn.
    intro a. apply Ot. exact a.
    intros a b p. 
    apply (Otp a b ((H a b)^-1 p)).
    intro a; cbn.
    match goal with |[|- ?XX _ = _] => path_via (XX °1) end.
    apply ap.
    apply H1'.
    apply Otp_1.
  - refine (path_T _ _ _ _ _ _).
    intro; reflexivity.
    intros a b p; cbn.
    refine (concat_1p _ @ _ @ (concat_p1 _)^).
    refine (ap_idmap _ @ _).
    match goal with
    |[|- _ = ap (λ x, ?G (?F x)) ?P] =>
     refine (_ @ (ap_compose F G P)^);
       refine (_ @ (ap02 G (T_rec_beta_tp _ _ _ _ _ _ _)^))            
    end.
    refine (_ @ (OT_rec_beta_Otp _ _ _ _ _ _ _ _)^).
    apply ap. symmetry; apply eisretr.
    intro a; cbn.
    rewrite transport_paths_FlFr.
    rewrite concat_ap_pFq, concat_ap_Fpq.
    apply moveR_pV. rewrite !concat_pp_p.
    match goal with
    |[|- _ = _ @ (1 @ (whiskerR ?hh 1 @ _))] =>
     pose (rew := whiskerR_p1 hh);
       rewrite concat_pp_p in rew;
       apply moveL_Vp in rew;
       rewrite rew; clear rew
    end.
    apply moveL_Vp. rewrite concat_p_pp.
    pose (rew:= whiskerL_1p (ap (ap idmap) (tp_1 (f:=f) a)^)).
    rewrite concat_pp_p in rew; apply moveL_Vp in rew;
    rewrite rew; clear rew.
    rewrite !ap_V.
    match goal with
    |[|- _ = 1 @ (_ @ (ap (ap (λ x, ?G (?F x))) ?pp)^)] =>
     rewrite <- (ap02_is_ap _ _ (G o F) _ _ _ _ pp);
       rewrite (ap02_compose _ _ _ F G _ _ _ _ pp)
    end.
    rewrite T_rec_beta_tp_1. rewrite !inv_pp.
    rewrite !concat_p_pp. apply whiskerR.
    rewrite !ap02_pp. rewrite !inv_pp.
    rewrite !concat_p_pp. rewrite !ap02_V. apply whiskerR. cbn.
    rewrite (OT_rec_beta_Otp_1 A (T f)). rewrite !concat_1p. rewrite inv_pp.
    rewrite <- (apD (λ U, ap_idmap U) (tp_1 a)^). rewrite transport_paths_FlFr.
    cbn. rewrite concat_p1. rewrite ap_V. rewrite concat_p_Vp.
    rewrite ap_idmap. rewrite inv_pp. rewrite !concat_pp_p.
    apply whiskerL.
    apply moveL_Vp. rewrite !concat_p_pp. rewrite <- ap_V.
    rewrite <- ap_pp.
    apply moveL_Vp. rewrite !concat_p_pp.
    apply moveR_pV. apply moveL_Vp.
    rewrite <- (apD (OT_rec_beta_Otp A (T f) (λ x : A, t x)
     (λ (a0 b : A)
      (p : O OT.nj
             {|
             trunctype_type := a0 = b;
             istrunc_trunctype_type := istrunc_paths
                                         (istrunc_trunctype_type A) a0 b |}),
      tp a0 b ((H a0 b) p)) (λ a0 : A, ap (tp a0 a0) (H1 a0) @ tp_1 a0) a a) (H1' a)^).
    rewrite transport_paths_FlFr. cbn.
    rewrite (ap_compose (H a a) (tp a a)).
    assert (r: (H1 a @ (eisretr (H a a) 1)^) = (ap (H a a) (H1' a)^)).
    { unfold H1'. rewrite inv_pp. rewrite ap_pp.
      rewrite ap_V. rewrite <- eisadj.
      rewrite <- (apD (eisretr (H a a)) (H1 a)^). rewrite transport_paths_FlFr.
      cbn. rewrite ap_idmap. rewrite !ap_V. rewrite !inv_pp.
      rewrite !inv_V. rewrite !concat_pp_p. apply whiskerL.
      apply moveL_Vp. rewrite concat_pV.
      apply moveL_Vp. rewrite concat_p1. apply ap_compose. }
    rewrite r.
    rewrite !concat_p_pp. do 2 apply whiskerR.
    rewrite ap02_is_ap.
    rewrite (ap_compose (Otp a a) _ _).
    rewrite !ap_V; rewrite inv_V.
    reflexivity.
  - refine (path_OT _ _ _ _ _ _ _).
    intro; reflexivity.
    intros a b p; cbn.
    refine (concat_1p _ @ _ @ (concat_p1 _)^).
    refine (ap_idmap _ @ _).
    match goal with
    |[|- _ = ap (λ x, ?G (?F x)) ?P] =>
     refine (_ @ (ap_compose F G P)^);
       refine (_ @ (ap02 G (OT_rec_beta_Otp _ _ _ _ _ _ _ _)^))            
    end.
    refine (_ @ (T_rec_beta_tp _ _ _ _ _ _ _)^).
    apply ap. symmetry; apply eissect.
    intro a; cbn.
    rewrite transport_paths_FlFr.
    rewrite concat_ap_pFq, concat_ap_Fpq.
    apply moveR_pV. rewrite !concat_pp_p.
    match goal with
    |[|- _ = _ @ (1 @ (whiskerR ?hh 1 @ _))] =>
     pose (rew := whiskerR_p1 hh);
       rewrite concat_pp_p in rew;
       apply moveL_Vp in rew;
       rewrite rew; clear rew
    end.
    apply moveL_Vp. rewrite concat_p_pp.
    pose (rew:= whiskerL_1p (ap (ap idmap) (Otp_1 a)^)).
    rewrite concat_pp_p in rew; apply moveL_Vp in rew;
    rewrite rew; clear rew.
    rewrite !ap_V.
    match goal with
    |[|- _ = 1 @ (_ @ (ap (ap (λ x, ?G (?F x))) ?pp)^)] =>
     rewrite <- (ap02_is_ap _ _ (G o F) _ _ _ _ pp);
       rewrite (ap02_compose _ _ _ F G _ _ _ _ pp)
    end.
    rewrite OT_rec_beta_Otp_1. rewrite !inv_pp.
    rewrite !concat_p_pp. apply whiskerR.
    rewrite !ap02_pp. rewrite !inv_pp.
    rewrite !concat_p_pp. rewrite !ap02_V. apply whiskerR. cbn.
    rewrite (T_rec_beta_tp_1). rewrite !concat_1p. rewrite inv_pp.
    rewrite <- (apD (λ U, ap_idmap U) (Otp_1 a)^). rewrite transport_paths_FlFr.
    cbn. rewrite concat_p1. rewrite ap_V. rewrite concat_p_Vp.
    rewrite ap_idmap. rewrite inv_pp. rewrite !concat_pp_p.
    apply whiskerL.
    apply moveL_Vp. rewrite !concat_p_pp. rewrite <- ap_V.
    rewrite <- ap_pp.
    apply moveL_Vp. rewrite !concat_p_pp.
    apply moveR_pV. apply moveL_Vp.
    rewrite <- (apD (T_rec_beta_tp (OTid A) (λ a0 : A, Ot a0)
      (λ (a0 b : A) (p : f a0 = f b), Otp a0 b ((H a0 b)^-1 p))
      (λ a0 : A, ap (Otp a0 a0) (H1' a0) @ Otp_1 a0) a a 
      ) (H1 a)^).
    rewrite transport_paths_FlFr. cbn.
    rewrite (ap_compose (H a a)^-1 (Otp a a)).
    assert (r: (H1' a @ (eissect (H a a) °1)^) = (ap (H a a)^-1 (H1 a)^)).
    { unfold H1'. apply moveR_pV. reflexivity. }
    rewrite r.
    rewrite !concat_p_pp. do 2 apply whiskerR.
    rewrite ap02_is_ap.
    rewrite (ap_compose (tp a a) _ _).
    rewrite !ap_V; rewrite inv_V.
    reflexivity.
Defined.

Lemma OTid_Tf_Tr (A:Type) (B:TruncType (n.+1)) (f:A -> B) (H: forall x y:A, O nj (BuildTruncType _ (tr x= tr y)) <~> (f x = f y))
        (H1: forall x:A, H x x °1 = 1) 
    : Trunc (n.+1) (OTid (BuildTruncType _ (Trunc (n.+1) A))) <~> Trunc (n.+1) (T f).
  Proof.
    pose (e := BuildEquiv (isequiv_Trunc_functor
                             (n.+1) 
                             (OTid_Tf (BuildTruncType _ (Trunc (n.+1) A)) B (Trunc_rec f)
                                      (Trunc_ind _ (λ x : A, Trunc_ind _ (λ y : A, H x y)))
                                      (Trunc_ind _ H1))
          )). 

    pose (e' := equiv_inverse (T_trunc (n.+1) A B f)).
    exact (equiv_compose' e' e). 
  Defined.
    
End OT_Tf.

Section TrTtelescope.
  
  Context `{ua : Univalence}.
  Context `{fs : Funext}.

  Definition TrTtelescope_to_TrOTtelescope_equiv {X Y:TruncType (n.+1)} (f: X -> Y) (sepY: separated Y)
              (Omono_f : Omono_sep X Y sepY f)
    : ∀ x : mappingtelescope_graph, (TrTtelescope f) x <~> (OTtelescope X) x.
  Proof.
    intro i; induction i.
    symmetry; apply equiv_tr. apply (istrunc_trunctype_type X).
    etransitivity; [exact (T_trunc (n.+1) _ _ ( Ttelescope_aux f i).2) |].
    
    assert (e := λ e e',  (equiv_inverse (OTid_Tf_Tr _ _ (Trunc_rec (n:=n.+1) (pr2 (Ttelescope_aux f i))) e e'))).
    etransitivity; try refine (e _ _); clear e.
    + intros x y.
      assert (eh:= BuildEquiv (Ttelescope_Omono_sep _ _ sepY f Omono_f i x y)).
      etransitivity; [clear eh | exact eh].
      apply function_lift_equiv'.
      cbn. exact fs. etransitivity; try (symmetry; apply equiv_path_Tr).
      symmetry. apply equiv_tr. refine (istrunc_paths _ _ _).
    + intro x; cbn. unfold function_lift, Oidpath. cbn.
      do 2 rewrite (λ P Q f, ap10 (O_rec_retr n nj P Q f)). cbn.
      reflexivity.
    + simpl. refine (BuildEquiv (isequiv_Trunc_functor (n.+1) _)). simpl in IHi. apply equiv_ap_OTid.
      cbn. etransitivity; [| exact IHi].
      symmetry; apply equiv_tr. apply istrunc_truncation.
      apply equiv_isequiv.
  Defined.

  Definition TrTtelescope_to_TrOTtelescope {X Y:TruncType (n.+1)} (f: X -> Y) (sepY: separated Y)
             (Omono_f : Omono_sep X Y sepY f)
    : diagram_equiv (TrTtelescope f) (OTtelescope X).
  Proof.
    apply diagram_equiv'.
    refine (exist _ _ _).
    - exact (TrTtelescope_to_TrOTtelescope_equiv f sepY Omono_f).
    - intros i j x; destruct x. refine (Trunc_ind _ _). intro x; reflexivity.
  Defined.

  Lemma transport_is_m_colimit (m:trunc_index) (G:graph) (D1 D2:diagram G) (e:diagram_equiv D1 D2) (Q:TruncType m)
        (cQ: is_m_colimit m D2 Q)
    : is_m_colimit m D1 Q.
  Proof.
    destruct cQ as [C U]. destruct e as [φ α].
    refine (Build_is_m_colimit _ _ _ _ _ _).
    exact (precompose_cocone φ C).

    intro Y.
    rewrite (path_forall (λ f, precompose_postcompose_cocone (Build_diagram_equiv φ α) f C)).
    refine isequiv_compose.
    unfold is_m_universal in U. apply U.
    apply precompose_cocone_equiv.
  Defined.    
    
  Lemma is_colimit_Im_OTtelescope {X Y:TruncType (n.+1)} (f: X -> Y) (sepY: separated Y)
        (Omono_f : Omono_sep X Y sepY f) (sf: IsSurjection f)
    : is_m_colimit (n.+1) (OTtelescope X) Y.
  Proof.
    pose (tr_colimit _ (Ttelescope f) (n.+1) Y (Build_is_colimit (Ttelescope_cocone f) (Colimit_Ttelescope f sf))).
    apply (transport_is_m_colimit (n.+1) _ _ _ (symmetric_diagram_equiv _ _ (TrTtelescope_to_TrOTtelescope f sepY Omono_f)) Y).
    exact i.
  Defined.
     
End TrTtelescope.