(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import Limit.
Require Import PathGroupoid_ Forall_ Equivalences_ epi_mono reflective_subuniverse modalities OPaths.
Require Import sheaf_base_case.
Require Import sheaf_def_and_thm.


Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
Local Open Scope type_scope.

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

Module Export OTid.

  Private Inductive OTid (A:TruncType (n.+1)) : Type :=
    | Ot : A -> (OTid A).

  Arguments Ot {A} a.

  Axiom Otp : forall {A:TruncType (n.+1)} (a b:A), O nj (BuildTruncType _ (a = b)) -> Ot a = Ot b.

  Axiom Otp_1 : forall {A:TruncType (n.+1)} (a:A), Otp a a °1 = 1.

  Definition OTid_ind (A:TruncType (n.+1)) (P : OTid A -> Type)
             (Ot' : forall a, P (Ot a))
             (Otp' : forall a b p, transport P (Otp a b p) (Ot' a) = Ot' b)
             (Otp_1' : forall a, transport2 P (Otp_1 a) (Ot' a) = Otp' a a °1)
    : forall w, P w
    := fun w => match w with
                |Ot a => fun _ => Ot' a
                end Otp_1'.

  Axiom OTid_ind_beta_Otp : forall (A:TruncType (n.+1)) (P : OTid A -> Type)
             (Ot' : forall a, P (Ot a))
             (Otp' : forall a b p, transport P (Otp a b p) (Ot' a) = Ot' b)
             (Otp_1' : forall a, transport2 P (Otp_1 a) (Ot' a) = Otp' a a °1)
             a b p,
      apD (OTid_ind A P Ot' Otp' Otp_1') (Otp a b p) = Otp' a b p.

  Axiom OTid_ind_beta_Otp_1 : forall (A:TruncType (n.+1)) (P : OTid A -> Type)
             (Ot' : forall a, P (Ot a))
             (Otp' : forall a b p, transport P (Otp a b p) (Ot' a) = Ot' b)
             (Otp_1' : forall a, transport2 P (Otp_1 a) (Ot' a) = Otp' a a °1)
             a,
      apD02 (OTid_ind A P Ot' Otp' Otp_1') (Otp_1 a) @ (concat_p1 _) @ (Otp_1' a) = OTid_ind_beta_Otp A P Ot' Otp' Otp_1' a a °1.
        
        
End OTid.

Definition OTid_rec (A:TruncType (n.+1)) (P:Type)
           (Ot': A -> P)
           (Otp' : forall (a b:A) (p:O nj (BuildTruncType _ (a=b))), Ot' a = Ot' b)
           (Otp_1' : forall a, Otp' a a °1 = 1)
  : OTid A -> P.
Proof.
  refine (OTid_ind _ _ Ot' (fun a b p => transport_const _ _ @ Otp' a b p)  _).
  intro a.
  pose (p:=whiskerR (transport2_const (A:=OTid A) (B:= P) (Otp_1 a) (Ot' a) @ concat_p1 _)^ (Otp' a a °1)). cbn in p.
  pose (p1:=(whiskerL (transport2 (λ _ : OTid A, P) (Otp_1 a) (Ot' a)) (Otp_1' a) @ concat_p1 _)^).
  exact (p1 @ p).
Defined.

Definition OT_rec_beta_Otp (A:TruncType (n.+1)) (P:Type)
           (Ot': A -> P)
           (Otp' : forall (a b:A) (p:O nj (BuildTruncType _ (a=b))), Ot' a = Ot' b)
           (Otp_1' : forall a, Otp' a a °1 = 1)
           a b p
  : ap (OTid_rec A P Ot' Otp' Otp_1') (Otp a b p) = Otp' a b p.
Proof.
  refine (cancelL (transport_const (Otp a b p) (Ot' a)) _ _ _).
  pose (e1:= OTid_ind_beta_Otp A (λ _ : OTid A, P) Ot'
        (λ (a0 b0 : A) (p1 : O nj (BuildTruncType _ (a0 = b0))),
         transport_const (Otp a0 b0 p1) (Ot' a0) @ Otp' a0 b0 p1)
        (λ a0 : A,
         (whiskerL (transport2 (λ _ : OTid A, P) (Otp_1 a0) (Ot' a0))
            (Otp_1' a0) @
          concat_p1 (transport2 (λ _ : OTid A, P) (Otp_1 a0) (Ot' a0)))^ @
         whiskerR
           (transport2_const (Otp_1 a0) (Ot' a0) @
            concat_p1 (transport2 (λ _ : OTid A, P) (Otp_1 a0) (Ot' a0)))^
         (Otp' a0 a0 °1)) a b p). 

  pose (e2:= apD_const (OTid_ind A (λ _ : OTid A, P) Ot'
        (λ (a0 b0 : A) (p2 : O nj (BuildTruncType _ (a0 = b0))),
         transport_const (Otp a0 b0 p2) (Ot' a0) @ Otp' a0 b0 p2)
        (λ a0 : A,
         (whiskerL (transport2 (λ _ : OTid A, P) (Otp_1 a0) (Ot' a0))
            (Otp_1' a0) @
          concat_p1 (transport2 (λ _ : OTid A, P) (Otp_1 a0) (Ot' a0)))^ @
         whiskerR
           (transport2_const (Otp_1 a0) (Ot' a0) @
            concat_p1 (transport2 (λ _ : OTid A, P) (Otp_1 a0) (Ot' a0)))^
         (Otp' a0 a0 °1))) (Otp a b p)).
  exact (e2^@ e1).
Defined.

Definition OT_rec_beta_Otp_1 (A:TruncType (n.+1)) (P:Type)
           (Ot': A -> P)
           (Otp' : forall (a b:A) (p:O nj (BuildTruncType _ (a=b))), Ot' a = Ot' b)
           (Otp_1' : forall a, Otp' a a °1 = 1)
           a
  : ap02 (OTid_rec A P Ot' Otp' Otp_1') (Otp_1 a) = OT_rec_beta_Otp A P Ot' Otp' Otp_1' a a °1 @ (Otp_1' a).
Proof.
  apply (cancel2L (transport2_const (Otp_1 a) (Ot' a))).
  apply (cancelL (apD_const (OTid_rec A P Ot' Otp' Otp_1') (Otp a a °1))).
  apply (cancelR _ _ (concat_p_pp (q:=transport_const _ _))^).
  apply (cancelR _ _ (whiskerL (transport2 _ (Otp_1 a) (Ot' a)) (apD_const (OTid_rec A P Ot' Otp' Otp_1') 1)^)).
  refine ((apD02_const (OTid_rec A P Ot' Otp' Otp_1') (Otp_1 a) )^ @ _).
  apply (cancelR _ _ (concat_p1 (transport2 (λ _ : OTid A, P) (Otp_1 a) (Ot' a)))).
  apply (cancelR _ _ ((whiskerL (transport2 (λ _ : OTid A, P) (Otp_1 a) (Ot' a)) (Otp_1' a) @
                                concat_p1 (transport2 (λ _ : OTid A, P) (Otp_1 a) (Ot' a)))^ @
                                                                                             whiskerR
                                                                                             (transport2_const (Otp_1 a) (Ot' a) @
                                                                                                               concat_p1 (transport2 (λ _ : OTid A, P) (Otp_1 a) (Ot' a)))^
                      (Otp' a a °1))).
  Opaque concat_p_pp.
  refine (OTid_ind_beta_Otp_1 _ _ _ _ _ _ @ _); cbn.
  apply (cancelL (apD_const
                    (OTid_ind A (λ _ : OTid A, P) Ot'
                           (λ (a0 b0 : A) (p2 : O nj (BuildTruncType _ (a0 = b0))),
                            transport_const (Otp a0 b0 p2) (Ot' a0) @ Otp' a0 b0 p2)
                           (λ a0 : A,
                                   (whiskerL (transport2 (λ _ : OTid A, P) (Otp_1 a0) (Ot' a0))
                                             (Otp_1' a0) @
                                             concat_p1
                                             (transport2 (λ _ : OTid A, P) (Otp_1 a0) (Ot' a0)))^ @
                                                                                                  whiskerR
                                                                                                  (transport2_const (Otp_1 a0) (Ot' a0) @
                                                                                                                    concat_p1
                                                                                                                    (transport2 (λ _ : OTid A, P) (Otp_1 a0) (Ot' a0)))^
                                   (Otp' a0 a0 °1))) (Otp a a °1))^).

  apply (@equiv_inj _ _ _ (isequiv_cancelL (transport_const (Otp a a °1) (Ot' a))
                                           (ap (OTid_rec A P Ot' Otp' Otp_1') (Otp a a °1))
                                           (Otp' a a °1))).

  path_via (OT_rec_beta_Otp A P Ot' Otp' Otp_1' a a °1).
  apply (@equiv_inj _ _ _ (isequiv_inverse _ (feq:= isequiv_cancelL (transport_const (Otp a a °1) (Ot' a))
                                                                    (ap (OTid_rec A P Ot' Otp' Otp_1') (Otp a a °1))
                                                                    (Otp' a a °1)))).
  rewrite eissect. cbn. repeat rewrite concat_pp_p.
  rewrite concat_V_pp.
  rewrite !inv_pp. repeat rewrite concat_p_pp. rewrite concat_pp_V.

  rewrite whiskerR_pp. 
  rewrite whiskerR_RV.
  rewrite <- (apD (λ u, (whiskerR (concat_p1 (transport2 (λ _ : OTid A, P) (Otp_1 a) (Ot' a)))
                                  u)) (Otp_1' a)^).
  cbn. rewrite transport_paths_FlFr. cbn. rewrite !ap_V; rewrite !inv_V.
  rewrite !concat_ap_pFq. rewrite ap_idmap. rewrite !inv_pp; rewrite !inv_V.
  rewrite !concat_p_pp. rewrite concat_pV_p. rewrite (concat_p1 ((transport2_const (Otp_1 a) (Ot' a) @@
                                                                                   (OT_rec_beta_Otp A P Ot' Otp' Otp_1' a a °1 @ Otp_1' a)) @
                                                                                                                                             (concat_p_pp )^)).
  rewrite whiskerR_RV.
  apply moveL_pV.
  unfold whiskerR at 1, whiskerL at 1.
  rewrite concat_concat2. cbn.
  rewrite (concat_1p (transport2_const (Otp_1 a) (Ot' a))).
  rewrite (concat_p1 (OT_rec_beta_Otp A P Ot' Otp' Otp_1' a a °1)).
  refine ((concat_p1 _)^ @ _). rewrite !concat_pp_p.
  match goal with
  |[|- _ = (?P @@ ?Q) @ ?R] => path_via (((P @ 1) @@ Q) @ R)
  end.
  2: rewrite (concat_p1 (transport2_const (Otp_1 a) (Ot' a))); reflexivity.
  rewrite <- concat_concat2.
  rewrite !concat_pp_p. apply whiskerL.
  rewrite !concat_p_pp. apply moveL_pV. rewrite concat_1p.
  rewrite !concat_pp_p. refine ((concat_p1 _)^@ _).
  apply whiskerL. cbn.
  pose (rew:= @triangulator _ _ _ _ (transport2 (λ _ : OTid A, P) (Otp_1 a) (Ot' a)) 1).
  apply moveL_Vp in rew. rewrite rew; clear rew. cbn.
  rewrite inv_pp. cbn. rewrite concat_1p. symmetry; apply concat_pV.
Qed.


Lemma path_OT_lemma (A:(n.+1)-Type) (B:Type)
      (α β :OTid A -> B)
      (eq1: α o Ot == β o Ot)
      (eq2: forall a b p, eq1 a @ ap β (Otp a b p) = ap α (Otp a b p) @ eq1 b)
      (eq3: forall a,  (eq2 a a °1)
                      = transport (λ U, eq1 a @ ap β U = ap α U @ eq1 a) (Otp_1 a)^ (concat_p1 (eq1 a) @ (concat_1p (eq1 a))^))
  : ∀ a : A,
    transport2 (λ w : OTid A, α w = β w) (Otp_1 a) (eq1 a) =
    transport_paths_FlFr (Otp a a °1) (eq1 a) @
                         (concat_pp_p (p:=(ap α (Otp a a °1))^)
                          (q:=eq1 a)
                            (r:=ap β (Otp a a °1))
                            @ cancelL (ap α (Otp a a °1))
                            ((ap α (Otp a a °1))^ @ (eq1 a @ ap β (Otp a a °1))) 
                            (eq1 a)
                            (concat_p_Vp (ap α (Otp a a °1)) (eq1 a @ ap β (Otp a a °1)) @ eq2 a a °1)).
Proof.
  intro a; cbn.
  rewrite eq3; clear eq3. clear eq2. generalize (eq1 a). intro p. clear eq1.
  unfold cancelL.
  pose (rew :=@transport_paths_FlFr _ _ (λ U:Ot a = Ot a, p @ ap β U) (λ U:Ot a = Ot a, ap α U @ p)).
  rewrite rew; clear rew.
  cbn.
  repeat rewrite concat_pp_p.
  rewrite ap_V. rewrite inv_V.
  repeat rewrite whiskerL_pp.
  symmetry.
  
  match goal with
  |[|- ?PP1 @ (?PP2 @ ((?PP3 @ (?PP4 @ ((?PP5 @ (?PP6 @ ?PP7)) @ ?PP8)) @ ?PP9))) = ?PP10] =>
   set (P1 := PP1);
     set (P2 := PP2);
     set (P3 := PP3);
     set (P4 := PP4);
     set (P5 := PP5);
     set (P6 := PP6);
     set (P7 := PP7);
     set (P8 := PP8);       
     set (P9 := PP9);
     set (P10 := PP10)
  end.
  rewrite (@concat_pp_p _ _ _ _ _ P3 (P4 @ ((P5 @ (P6 @ P7)) @ P8)) P9).
  rewrite (@concat_pp_p _ _ _ _ _ P4 ((P5 @ (P6 @ P7)) @ P8) P9).
  repeat rewrite (@concat_pp_p _ _ _ _ _ P5 _ _).
  repeat rewrite (@concat_pp_p _ _ _ _ _ P6 _ _).
  repeat rewrite (@concat_pp_p _ _ _ _ _ P7 _ _).

  unfold P1; clear P1.
  match goal with
  |[|- ?ff _ p @ _ = _]
   => rewrite <- (apD (λ U, ff U p) (Otp_1 a)^)
  end.
  cbn.
  rewrite (transport_paths_FlFr (f:= λ U, transport (λ x : OTid A, α x = β x) U p)
                                (g:= λ U, ((ap α U)^ @ p) @ ap β U)).
  rewrite ap_V. rewrite inv_V.

  unfold P10. rewrite transport2_is_ap.
  repeat rewrite concat_pp_p.
  match goal with
  |[|- _ = ?XX] => path_via (XX @ 1)
  end.
  apply whiskerL.
  rewrite ap_V.
  do 3 apply moveR_Vp.
  match goal with
  |[|- _ = ?PP11 @ (?PP12 @ ?PP13)]
   => set (P11 := PP11); set (P12 := PP12); set (P13 := PP13); cbn in *
  end.

  unfold P3; clear P3.

  rewrite <- (apD (λ U, (concat_V_pp (ap α U)
                                     ((ap α U)^ @ (p @ ap β U)))^) (Otp_1 a)^).
  cbn.
  rewrite (transport_paths_FlFr (f:=(λ U : Ot a = Ot a, (ap α U)^ @ (p @ ap β U)))
                                (g:=λ U : Ot a = Ot a, (ap α U)^ @ (ap α U @ ((ap α U)^ @ (p @ ap β U))))).
  rewrite ap_V. rewrite inv_V.
  match goal with
  |[|- _ @ (((?PP31 @ ?PP32) @ ?PP33) @ _) = _] =>
   set (P31 := PP31); set (P32 := PP32); set (P33 := PP33); cbn in *
  end.
  repeat rewrite (@concat_pp_p _ _ _ _ _ P31).
  repeat rewrite (@concat_pp_p _ _ _ _ _ P32).
  rewrite (@concat_p_pp _ _ _ _ _ P2 P31 _).

  assert (rr: P11 @ (concat_pp_p) = (P2 @ P31)).
  { unfold P2, P31, P11.
    rewrite concat_ap_FpFq_pp_p. rewrite concat_ap_FpFq_p_pp.
    unfold whiskerR, whiskerL. 
    repeat rewrite concat_p_pp. apply whiskerR.
    reflexivity. }
  destruct rr.
  rewrite (@concat_pp_p _ _ _ _ _ P11).
  apply whiskerL.
  match goal with |[|- ?PP1 @ _ = _] => set (P1 := PP1) end.
  clear P10; clear P11.
  
  do 2 apply moveR_Mp.
  repeat rewrite (concat_p_pp (r:=P9)). apply moveR_pM.
  unfold P9.
  rewrite <- (apD (λ U, (concat_V_pp (ap α U) p)^) (Otp_1 a)^). simpl.
  rewrite (transport_paths_Fr (g:= λ U, (ap α U)^ @ (ap α U @ p))).
  clear P2.
  repeat rewrite (concat_p_pp (r:=P8)).
  apply moveR_pM.
  set (P2 := ap (λ U : Ot a = Ot a, (ap α U)^ @ (ap α U @ p)) (Otp_1 a)^).
  
  unfold P8.
  rewrite <- (apD (λ U, whiskerL (z:=β (Ot a)) (q:= 1 @ p) (r := ap α (Otp a a °1) @ p) (ap α U)^) (Otp_1 a)^).
  rewrite transport_arrow.
  simpl.
  rewrite transport_const.
  rewrite transport_paths_FlFr.
  do 2 rewrite inv_pp. 
  repeat rewrite ap_V. rewrite whiskerL_LV. repeat rewrite inv_V.
  match goal with
  |[|- _ = _ @ (?PP16 @ (?PP15 @ ?PP14)) ] =>
   set (P14 := PP14); set (P15 := PP15); set (P16 := PP16); simpl in P14, P15, P16
  end.
  unfold P4.
  rewrite <- (apD (λ U, (whiskerL (ap α U)^
                         (concat_p_Vp (ap α U) (p @ ap β U)))) (Otp_1 a)^).
  simpl.
  rewrite transport_paths_FlFr. simpl.
  rewrite ap_V. rewrite inv_V.
  match goal with
  |[|- _ @ (((?PP17 @ ?PP18) @ ?PP19) @ _) = _]
   => set (P17:=PP17); set (P18 := PP18); set (P19 := PP19)
  end.
  clear P4. clear P8. clear P9. clear P31.
  unfold P6, P7; clear P6; clear P7.
  rewrite <- (apD (λ U, (whiskerL (ap α U)^ (concat_p1 p) @
                                                          whiskerL (ap α U)^ (concat_1p p)^)) (Otp_1 a)^).
  simpl.
  rewrite transport_paths_FlFr.
  rewrite ap_V. rewrite inv_V.
  match goal with
  |[|- _ @ (_ @ (_ @ ((?PP6 @ ?PP7) @ ?PP8))) = _]
   => set (P6:=PP6); set (P7:=PP7); set (P8:=PP8)
  end.
  
  unfold P5; clear P5.
  rewrite <- (apD (λ U, whiskerL (q:=p @ ap β (Otp a a °1)) (r:=p@1) (ap α U)^) (Otp_1 a)^).
  rewrite transport_arrow.
  rewrite transport_const. rewrite transport_paths_FlFr.
  simpl.
  rewrite ap_V. rewrite inv_V.
  repeat rewrite (concat_p_pp (r:=P8)).
  repeat rewrite (concat_p_pp (r:=P14)).

  unfold P8, P14. repeat rewrite ap_V. apply whiskerR. clear P8; clear P14.
  repeat rewrite (concat_pp_p (p:=P17)).
  rewrite <- (concat_pp_p (p:=P33) (q:=P17)).
  unfold P33, P17; clear P33; clear P17.
  rewrite ap_V. rewrite concat_Vp.
  match goal with |[|- 1 @ ?XX = _] => rewrite (concat_1p XX) end.
  pose (p1 := whiskerL_1p (concat_p_Vp 1 (p @ 1))). simpl in p1.
  apply moveL_pV in p1.
  apply moveL_Mp in p1.
  unfold P18; clear P18; rewrite p1; clear p1.
  unfold P15; clear P15.
  pose (p1 := whiskerL_1p (ap (λ U : Ot a = Ot a, ap α U @ p) (Otp_1 a))). simpl in p1.
  apply moveL_pV in p1.
  apply moveL_Mp in p1.
  rewrite p1; clear p1.
  unfold P7; clear P7.
  pose (p1 := whiskerL_1p (concat_p1 p)). simpl in p1.
  apply moveL_pV in p1.
  apply moveL_Mp in p1.
  rewrite p1; clear p1.
  pose (p1 := whiskerL_1p (concat_1p p)^). simpl in p1.
  apply moveL_pV in p1.
  apply moveL_Mp in p1.
  rewrite p1; clear p1.
  pose (p1 := whiskerL_1p (ap (λ U : Ot a = Ot a, p @ ap β U) (Otp_1 a))). simpl in p1.
  apply moveL_pV in p1.
  apply moveL_Mp in p1.
  rewrite p1; clear p1.
  repeat rewrite concat_pp_p.
  unfold  P19, P6, P32, P1, P12, P13, P2, P16.
  clear P19; clear P6; clear P32; clear P1; clear P12; clear P13; clear P2; clear P16.
  rewrite inv_V.
  rewrite (concat_p1 (concat_1p p)).
  match goal with
  |[|- ?PP1 @ (?PP2 @ (?PP3 @ (?PP4 @ (?PP5 @ (?PP6 @ (?PP7 @ (?PP8 @ (?PP9 @ (?PP10 @ (?PP11 @ (?PP12 @ (?PP13 @ (?PP14 @ (?PP15 @ (?PP16)))))))))))))))
       =
       ?PP17 @ (?PP18 @ ((?PP19 @ ?PP20) @ ((?PP21 @ ?PP22) @ (?PP23 @ (?PP24 @ (?PP25 @ ?PP26))))))] =>
   set (P1 := PP1);
     set (P2 := PP2);
     set (P3 := PP3);
     set (P4 := PP4);
     set (P5 := PP5);
     set (P6 := PP6);
     set (P7 := PP7);
     set (P8 := PP8);       
     set (P9 := PP9);
     set (P10 := PP10);
     set (P11 := PP11);
     set (P12 := PP12);
     set (P13 := PP13);
     set (P14 := PP14);
     set (P15 := PP15);
     set (P16 := PP16);
     set (P17 := PP17);
     set (P18 := PP18);
     set (P19 := PP19);
     set (P20 := PP20);
     set (P21 := PP21);
     set (P22 := PP22);
     set (P23 := PP23);
     set (P24 := PP24);
     set (P25 := PP25);
     set (P26 := PP26)
  end.
  repeat rewrite (concat_p_pp (r:=P16)).
  apply whiskerR. clear P16.
  assert (rr : 1 = P14 @ P13).
  symmetry. unfold P13, P14. apply concat_pV.
  destruct rr. rewrite (concat_p1 P13).
  clear P15. clear P20. simpl in *.
  assert (rr: P1 @ (P2 @ P3) = P17).
  { unfold P1, P2, P3, P17.
    clear P1; clear P2; clear P17;
    clear P3; clear P4; clear P5; clear P6; clear P7; clear P8; clear P9
    ; clear P10; clear P11; clear P12; clear P13; clear P14; clear P18; clear P19
    ; clear P21; clear P22; clear P23; clear P24; clear P25; clear P26.
    destruct p. reflexivity. }
  destruct rr.
  repeat rewrite concat_pp_p.
  do 3 apply whiskerL. 
  clear P1; clear P2; clear P26.

  assert (rr: P18 @ (P19 @ P14) = P11 @ P12).
  { unfold P18, P19, P14, P11, P12. cbn.
    clear P3; clear P4; clear P5; clear P6; clear P7; clear P8; clear P9
    ; clear P10; clear P11; clear P12; clear P13; clear P14; clear P18; clear P19
    ; clear P21; clear P22; clear P23; clear P24; clear P25.
    destruct p; reflexivity. }
  rewrite (concat_p_pp  (q:= (P19 @ P14))).
  rewrite rr; clear rr.
  rewrite (concat_p_pp (p:=P9)).
  unfold P9, P10. rewrite concat_Vp. rewrite (concat_1p (P11 @ (P12 @ P13))).
  clear P9; clear P10.
  rewrite (concat_p_pp (p:=P3)).
  unfold P3 at 1, P11 at 1. rewrite concat_Vp.
  rewrite (concat_1p (P12 @ P13)).
  clear P3.
  assert (rr: P4 @ (P5 @ (P6 @ P7)) = P11).
  { repeat rewrite (concat_p_pp (r:=P7)).
    apply moveR_pM.

    unfold P4, P5, P6, P7, P11.
    clear P4; clear P5; clear P6; clear P7; clear P8
    ; clear P11; clear P12; clear P13; clear P14; clear P18; clear P19
    ; clear P21; clear P22; clear P23; clear P24; clear P25.
    rewrite <- (ap_V (λ U : Ot a = Ot a, p @ ap β U) (Otp_1 a)).
    rewrite ap_V. apply moveR_Vp.

    rewrite <- (apD (λ U, concat_1p (p @ ap β U)) (Otp_1 a)^).
    simpl.
    rewrite transport_paths_FlFr. simpl.
    rewrite ap_V. rewrite inv_V.
    repeat rewrite concat_p_pp.
    match goal with
    |[|- ?P1 @ (?P2 @ ?P3) = _]
     => rewrite (concat_p_pp (p:=P1))
    end. apply whiskerR.
    match goal with
    |[|- ?P1 @ (?P2 @ ?P3) = _]
     => rewrite (concat_p_pp (p:=P1))
    end. apply whiskerR.
    rewrite concat_ap_Fpq.
    unfold whiskerR.
    rewrite concat_ap_pFq. unfold whiskerL.
    rewrite concat_concat2. rewrite (concat_p1 (ap (λ u : Ot a = Ot a, (ap α u)^) (Otp_1 a))).
    rewrite (concat_1p (ap (λ u : Ot a = Ot a, p @ ap β u) (Otp_1 a))).
    rewrite concat_ap_FpFq_p_pp.
    unfold whiskerR, whiskerL.
    rewrite concat_pp_p. apply moveL_Mp.
    rewrite concat2_inv.
    rewrite concat_concat2.
    rewrite concat_Vp.
    rewrite (concat_1p (ap (λ u : Ot a = Ot a, p @ ap β u) (Otp_1 a))).
    rewrite concat_ap_pFq. unfold whiskerL.
    rewrite (concat2_p_pp). reflexivity. }
  rewrite (concat_pp_p (p:=P11)).
  destruct rr.
  rewrite (concat_pp_p (p:=P4)); apply whiskerL.
  rewrite (concat_pp_p (p:=P5)); apply whiskerL.
  rewrite (concat_pp_p (p:=P6)); apply whiskerL.
  do 2 apply whiskerL.
  clear P4; clear P5; clear P6; clear P7; clear P8; clear P12.
  clear P14; clear P18; clear P19.
  unfold P13, P21, P22, P23, P24, P25.
  clear P13; clear P21; clear P22; clear P23; clear P24; clear P25.
  rewrite <- (apD (λ U, concat_1p (ap α U @ p)) (Otp_1 a)^).
  rewrite transport_paths_FlFr. simpl.
  repeat rewrite ap_V. rewrite inv_V.
  repeat rewrite concat_pp_p. rewrite concat_Vp.
  rewrite (concat_p1).
  apply moveL_Vp.
  repeat rewrite (concat_p_pp (r:=(concat_1p (1 @ p)))). apply moveL_pM.
  match goal with
  |[|- ?XX = _] => assert (rr: 1 = XX)
  end.
  { destruct p. reflexivity. }
  destruct rr.
  apply moveL_Vp. rewrite concat_p1.
  rewrite concat_ap_Fpq.
  rewrite concat_ap_pFq. unfold whiskerR, whiskerL.
  rewrite concat_concat2.
  rewrite concat_p1, (concat_1p (ap (λ u : Ot a = Ot a, ap α u @ p) (Otp_1 a))).
  rewrite concat_ap_FFpq_p_pp. rewrite concat_ap_Fpq.
  unfold whiskerR. simpl.
  rewrite <- concat2_p_pp. reflexivity.
Qed.

Lemma path_OT (A:(n.+1)-Type) (B:Type)
      (α β :OTid A -> B)
      (eq1: α o Ot == β o Ot)
      (eq2: forall a b p, eq1 a @ ap β (Otp a b p) = ap α (Otp a b p) @ eq1 b)
      (eq3: forall a,  (eq2 a a °1)
                      = transport (λ U, eq1 a @ ap β U = ap α U @ eq1 a) (Otp_1 a)^ (concat_p1 (eq1 a) @ (concat_1p (eq1 a))^))
  : α == β.
Proof.
  refine (OTid_ind _ _ _ _ _).
  - exact eq1.
  - intros a b p.
    refine (transport_paths_FlFr _ _ @ _).
    etransitivity; try apply concat_pp_p.
    apply (cancelL (ap α (Otp a b p))).
    etransitivity; try apply eq2.
    apply concat_p_Vp.
  - apply path_OT_lemma. exact eq3.
Defined.

Lemma path_OT_compute (A:(n.+1)-Type) (B:Type)
      (α β :OTid A -> B)
      (eq1: α o Ot == β o Ot)
      (eq2: forall a b p, eq1 a @ ap β (Otp a b p) = ap α (Otp a b p) @ eq1 b)
      (eq3: forall a,  (eq2 a a °1)
                       = transport (λ U, eq1 a @ ap β U = ap α U @ eq1 a) (Otp_1 a)^ (concat_p1 (eq1 a) @ (concat_1p (eq1 a))^)) x
  : path_OT A B α β eq1 eq2 eq3 (Ot x) = eq1 x.
Proof.
  reflexivity.
Defined.

Lemma equiv_ap_OTid_fun {X Y:TruncType (n.+1)} (e: X -> Y)
  : OTid X -> OTid Y.
Proof.
  refine (OTid_rec _ _ _ _ _).
  intro x; apply Ot; exact (e x).
  intros a b p; cbn. apply Otp.
  exact (Oap e p).
  intro a; cbn. etransitivity; [apply (ap (Otp (e a) (e a)) (Oap_1 e))| apply Otp_1].
Defined.

Lemma isequiv_ap_OTid_path {X Y:TruncType (n.+1)} (e: X = Y :> Type)
  : IsEquiv (equiv_ap_OTid_fun (equiv_path _ _ e)).
Proof.
  destruct X as [X tX], Y as [Y tY]; cbn in *.
  destruct e; cbn in *.
  assert (r: tX = tY) by apply path_ishprop. destruct r.
  refine (isequiv_homotopic idmap _).
  
  refine (path_OT _ _ _ _ _ _ _).
  - intro x; reflexivity.
  - intros a b p; cbn.
    refine (concat_1p _ @ _ @ (concat_p1 _)^).
    unfold equiv_ap_OTid_fun. cbn.
    refine (OT_rec_beta_Otp _ _ _ _ _ _ _ _ @ _ @ (ap_idmap _)^).
    apply ap.
    apply Oap_idmap.
  - intro a; cbn. rewrite transport_paths_FlFr.
    rewrite concat_ap_Fpq; rewrite concat_ap_pFq.
    apply moveR_pV. rewrite !concat_pp_p.
    pose (rew:= whiskerR_p1 (ap (ap idmap) (Otp_1 a)^)).
    rewrite concat_pp_p in rew; apply moveL_Vp in rew; rewrite rew; clear rew.
    cbn. apply moveL_Vp. rewrite !concat_p_pp.
    pose (rew:= whiskerL_1p (ap (ap (equiv_ap_OTid_fun idmap)) (Otp_1 a)^)).
    rewrite concat_pp_p in rew; apply moveL_Vp in rew; rewrite rew; clear rew.
    cbn. rewrite !concat_1p. rewrite !ap_V.
    rewrite <- (ap02_is_ap _ _ (equiv_ap_OTid_fun idmap) _ _ _ _ (Otp_1 a)).
    unfold equiv_ap_OTid_fun. cbn.
    rewrite OT_rec_beta_Otp_1. rewrite inv_pp. rewrite concat_pV_p.
    rewrite <- (apD (λ U, ap_idmap U) (Otp_1 a)^).
    rewrite transport_paths_FlFr. cbn. rewrite !ap_V.
    rewrite (ap_idmap (Otp_1 a)). rewrite concat_p1. rewrite !inv_pp.
    rewrite !inv_V. rewrite concat_p_pp. refine (_ @ concat_1p _). apply whiskerR.
    apply moveR_pM. rewrite concat_1p. refine (_ @ concat_p1 _).
    rewrite !concat_pp_p. apply whiskerL.
    rewrite <- ap_V. rewrite <- ap_pp.
    path_via ((ap (Otp a a) (idpath °1))).
    apply ap. apply moveR_Vp. refine (_ @ (concat_p1 _)^).
    apply (Oap_idmap_Oap_1 a).
Qed.

Lemma isequiv_ap_OTid `{ua: Univalence} {X Y:TruncType (n.+1)} (e: X <~> Y)
  : IsEquiv (equiv_ap_OTid_fun e).
Proof.
  refine (isequiv_homotopic (equiv_ap_OTid_fun (equiv_path _ _ (path_universe_uncurried e))) _).
  exact ua.
  apply (isequiv_ap_OTid_path (path_universe_uncurried e)).
  rewrite equiv_path_path_universe_uncurried. intro; reflexivity.
Qed.

Lemma equiv_ap_OTid {X Y:TruncType (n.+1)} (e: X <~> Y)
  : OTid X <~> OTid Y.
Proof.
  exists (equiv_ap_OTid_fun e).
  apply isequiv_ap_OTid.
Defined.

Section OT_telescope.
  
  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  Definition OTtelescope_aux (X:TruncType (n.+1)) (m: nat)
  : TruncType (n.+1).
    induction m as [|m U].
    - exact X. 
    - exact (BuildTruncType _ (Trunc (n.+1) (OTid U))).
  Defined.

  Definition OTtelescope (X:TruncType (n.+1)) 
  : diagram mappingtelescope_graph.
    refine (Build_diagram _ _ _).
    - intros m. exact (OTtelescope_aux X m).
    - intros n m q; destruct q; simpl.
      intro x. apply tr. apply Ot. exact x.
  Defined.

    
End OT_telescope.

