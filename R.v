(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import PathGroupoid_.
(* Require Import Forall_ Equivalences_ epi_mono reflective_subuniverse modalities OPaths. *)



Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
Local Open Scope type_scope.

Module Export R.

  Private Inductive R {A:Type} (P:A -> A -> Type) (p0: forall x:A, P x x) : Type :=
    | r : A -> (R P p0).

  Arguments r {A P p0} a.

  Axiom rp : forall {A P p0} (a b:A), P a b -> @r A P p0 a = r b.

  Axiom rp_1 : forall {A P p0} (a:A), @rp A P p0 a a (p0 a) = 1.

  Definition R_ind {A:Type} (P:A -> A -> Type) (p0: forall x:A, P x x)
             (Q : R P p0 -> Type)
             (r' : forall a, Q (r a))
             (rp' : forall a b p, transport Q (rp a b p) (r' a) = r' b)
             (rp_1' : forall a, transport2 Q (rp_1 a) (r' a) = rp' a a (p0 a))
    : forall w, Q w
    := fun w => match w with
                |r a => fun _ => r' a
                end rp_1'.

  Axiom R_ind_beta_rp : forall {A:Type} (P:A -> A -> Type) (p0: forall x:A, P x x)
             (Q : R P p0 -> Type)
             (r' : forall a, Q (r a))
             (rp' : forall a b p, transport Q (rp a b p) (r' a) = r' b)
             (rp_1' : forall a, transport2 Q (rp_1 a) (r' a) = rp' a a (p0 a))
             a b p,
      apD (R_ind P p0 Q r' rp' rp_1') (rp a b p) = rp' a b p.

  Axiom R_ind_beta_rp_1 : forall {A:Type} (P:A -> A -> Type) (p0: forall x:A, P x x)
             (Q : R P p0 -> Type)
             (r' : forall a, Q (r a))
             (rp' : forall a b p, transport Q (rp a b p) (r' a) = r' b)
             (rp_1' : forall a, transport2 Q (rp_1 a) (r' a) = rp' a a (p0 a))
             (a:A),
      apD02 (R_ind P p0 Q r' rp' rp_1') (rp_1 a) @ (concat_p1 _) @ (rp_1' a) = R_ind_beta_rp P p0 Q r' rp' rp_1' a a (p0 a).
End R.

Definition R_rec {A:Type} (P:A -> A -> Type) (p0: forall x:A, P x x)
           (Q:Type)
           (r': A -> Q)
           (rp' : forall (a b:A) (p:P a b), r' a = r' b)
           (rp_1' : forall a, rp' a a (p0 a) = 1)
  : R P p0 -> Q.
Proof.
  refine (R_ind _ _ _ r' (fun a b p => transport_const _ _ @ rp' a b p)  _).
  intro a.
  pose (p:=whiskerR (transport2_const (A:=R P p0) (B:= Q) (rp_1 a) (r' a) @ concat_p1 _)^ (rp' a a (p0 a))). cbn in p.
  pose (p1:=(whiskerL (transport2 (λ _ : R P p0, Q) (rp_1 a) (r' a)) (rp_1' a) @ concat_p1 _)^).
  exact (p1 @ p).
Defined.

Definition R_rec_beta_rp {A:Type} (P:A -> A -> Type) (p0: forall x:A, P x x)
           (Q:Type)
           (r': A -> Q)
           (rp' : forall (a b:A) (p:P a b), r' a = r' b)
           (rp_1' : forall a, rp' a a (p0 a) = 1)
           a b p
  : ap (R_rec _ _ Q r' rp' rp_1') (rp a b p) = rp' a b p.
Proof.
Admitted.

Definition R_rec_beta_rp_1 {A:Type} (P:A -> A -> Type) (p0: forall x:A, P x x)
           (Q:Type)
           (r': A -> Q)
           (rp' : forall (a b:A) (p:P a b), r' a = r' b)
           (rp_1' : forall a, rp' a a (p0 a) = 1)
           (a:A)
  : ap02 (R_rec P p0 Q r' rp' rp_1') (rp_1 a) = R_rec_beta_rp P p0 Q r' rp' rp_1' a a (p0 a) @ (rp_1' a).
Proof.
Admitted.
  


Lemma path_R {A B:Type} (P: A -> A -> Type) (p0 : forall x, P x x)
      (α β :R P p0 -> B)
      (eq1: α o r == β o r)
      (eq2: forall a b p, eq1 a @ ap β (rp a b p) = ap α (rp a b p) @ eq1 b)
      (eq3: forall a,  (eq2 a a (p0 a))
                      = transport (λ U, eq1 a @ ap β U = ap α U @ eq1 a) (rp_1 a)^ (concat_p1 (eq1 a) @ (concat_1p (eq1 a))^))
  : α == β.
Proof with cbn.
  refine (R_ind _ _ _ _ _ _).
  - exact eq1.
  - intros a b p.
    refine (transport_paths_FlFr _ _ @ _).
    etransitivity; try apply concat_pp_p.
    apply (cancelL (ap α (rp a b p))).
    etransitivity; try apply eq2.
    apply concat_p_Vp.
  - intro a...
    rewrite eq3; clear eq3. clear eq2. generalize (eq1 a). intro p. clear eq1.
    unfold cancelL.
    pose (rew :=@transport_paths_FlFr _ _ (λ U:r a = r a, p @ ap β U) (λ U:r a = r a, ap α U @ p)).
    rewrite rew; clear rew.
    cbn.
    repeat rewrite concat_pp_p.
    rewrite ap_V. rewrite inv_V.
    repeat rewrite whiskerL_pp.
    (* apply moveR_Vp. *)
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
     => rewrite <- (apD (λ U, ff U p) (rp_1 a)^)
    end.
    cbn.
    rewrite (transport_paths_FlFr (f:= λ U, transport (λ x : R P p0, α x = β x) U p)
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
                                       ((ap α U)^ @ (p @ ap β U)))^) (rp_1 a)^).
    cbn.
    rewrite (transport_paths_FlFr (f:=(λ U : r a = r a, (ap α U)^ @ (p @ ap β U)))
                                  (g:=λ U : r a = r a, (ap α U)^ @ (ap α U @ ((ap α U)^ @ (p @ ap β U))))).
    rewrite ap_V. rewrite inv_V.
    match goal with
    |[|- _ @ (((?PP31 @ ?PP32) @ ?PP33) @ _) = _] =>
     set (P31 := PP31); set (P32 := PP32); set (P33 := PP33); cbn in *
    end.
    repeat rewrite (@concat_pp_p _ _ _ _ _ P31).
    repeat rewrite (@concat_pp_p _ _ _ _ _ P32).
    rewrite (@concat_p_pp _ _ _ _ _ P2 P31 _).

    assert (rr: P11 @ (concat_pp_p _ _ _) = (P2 @ P31)).
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
    repeat rewrite (concat_p_pp _ _ P9). apply moveR_pM.
    unfold P9.
    rewrite <- (apD (λ U, (concat_V_pp (ap α U) p)^) (rp_1 a)^). simpl.
    rewrite (transport_paths_Fr (g:= λ U, (ap α U)^ @ (ap α U @ p))).
    clear P2.
    repeat rewrite (concat_p_pp _ _ P8).
    apply moveR_pM.
    set (P2 := ap (λ U : r a = r a, (ap α U)^ @ (ap α U @ p)) (rp_1 a)^).
    
    unfold P8.
    rewrite <- (apD (λ U, whiskerL (z:=β (r a)) (q:= 1 @ p) (r := ap α (rp a a (p0 a)) @ p) (ap α U)^) (rp_1 a)^).
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
                           (concat_p_Vp (ap α U) (p @ ap β U)))) (rp_1 a)^).
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
                                                            whiskerL (ap α U)^ (concat_1p p)^)) (rp_1 a)^).
    simpl.
    rewrite transport_paths_FlFr.
    rewrite ap_V. rewrite inv_V.
    match goal with
    |[|- _ @ (_ @ (_ @ ((?PP6 @ ?PP7) @ ?PP8))) = _]
     => set (P6:=PP6); set (P7:=PP7); set (P8:=PP8)
    end.

    unfold P5; clear P5.
    rewrite <- (apD (λ U, whiskerL (q:=p @ ap β (rp a a (p0 a))) (r:=p@1) (ap α U)^) (rp_1 a)^).
    rewrite transport_arrow.
    rewrite transport_const. rewrite transport_paths_FlFr.
    simpl.
    rewrite ap_V. rewrite inv_V.
    repeat rewrite (concat_p_pp _ _ P8).
    repeat rewrite (concat_p_pp _ _ P14).

    unfold P8, P14. repeat rewrite ap_V. apply whiskerR. clear P8; clear P14.
    repeat rewrite (concat_pp_p P17 _ _).
    rewrite <- (concat_pp_p P33 P17 _).
    unfold P33, P17; clear P33; clear P17.
    rewrite ap_V. rewrite concat_Vp.
    match goal with |[|- 1 @ ?XX = _] => rewrite (concat_1p XX) end.
    pose (p1 := whiskerL_1p (concat_p_Vp 1 (p @ 1))). simpl in p1.
    apply moveL_pV in p1.
    apply moveL_Mp in p1.
    unfold P18; clear P18; rewrite p1; clear p1.
    unfold P15; clear P15.
    pose (p1 := whiskerL_1p (ap (λ U : r a = r a, ap α U @ p) (rp_1 a))). simpl in p1.
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
    pose (p1 := whiskerL_1p (ap (λ U : r a = r a, p @ ap β U) (rp_1 a))). simpl in p1.
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
    repeat rewrite (concat_p_pp _ _ P16).
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
    rewrite (concat_p_pp _ (P19 @ P14)).
    rewrite rr; clear rr.
    rewrite (concat_p_pp P9).
    unfold P9, P10. rewrite concat_Vp. rewrite (concat_1p (P11 @ (P12 @ P13))).
    clear P9; clear P10.
    rewrite (concat_p_pp P3).
    unfold P3 at 1, P11 at 1. rewrite concat_Vp.
    rewrite (concat_1p (P12 @ P13)).
    clear P3.
    assert (rr: P4 @ (P5 @ (P6 @ P7)) = P11).
    { repeat rewrite (concat_p_pp _ _ P7).
      apply moveR_pM.

      unfold P4, P5, P6, P7, P11.
      clear P4; clear P5; clear P6; clear P7; clear P8
      ; clear P11; clear P12; clear P13; clear P14; clear P18; clear P19
      ; clear P21; clear P22; clear P23; clear P24; clear P25.
      rewrite <- (ap_V (λ U : r a = r a, p @ ap β U) (rp_1 a)).
      rewrite ap_V. apply moveR_Vp.

      rewrite <- (apD (λ U, concat_1p (p @ ap β U)) (rp_1 a)^).
      simpl.
      rewrite transport_paths_FlFr. simpl.
      rewrite ap_V. rewrite inv_V.
      repeat rewrite concat_p_pp.
      match goal with
      |[|- ?P1 @ (?P2 @ ?P3) = _]
       => rewrite (concat_p_pp P1)
      end. apply whiskerR.
      match goal with
      |[|- ?P1 @ (?P2 @ ?P3) = _]
       => rewrite (concat_p_pp P1)
      end. apply whiskerR.
      rewrite concat_ap_Fpq.
      unfold whiskerR.
      rewrite concat_ap_pFq. unfold whiskerL.
      rewrite concat_concat2. rewrite (concat_p1 (ap (λ u : r a = r a, (ap α u)^) (rp_1 a))).
      rewrite (concat_1p (ap (λ u : r a = r a, p @ ap β u) (rp_1 a))).
      rewrite concat_ap_FpFq_p_pp.
      unfold whiskerR, whiskerL.
      rewrite concat_pp_p. apply moveL_Mp.
      rewrite concat2_inv.
      rewrite concat_concat2.
      rewrite concat_Vp.
      rewrite (concat_1p (ap (λ u : r a = r a, p @ ap β u) (rp_1 a))).
      rewrite concat_ap_pFq. unfold whiskerL.
      rewrite (concat2_p_pp). reflexivity. }
    rewrite (concat_pp_p P11).
    destruct rr.
    rewrite (concat_pp_p P4); apply whiskerL.
    rewrite (concat_pp_p P5); apply whiskerL.
    rewrite (concat_pp_p P6); apply whiskerL.
    do 2 apply whiskerL.
    clear P4; clear P5; clear P6; clear P7; clear P8; clear P12.
    clear P14; clear P18; clear P19.
    unfold P13, P21, P22, P23, P24, P25.
    clear P13; clear P21; clear P22; clear P23; clear P24; clear P25.
    rewrite <- (apD (λ U, concat_1p (ap α U @ p)) (rp_1 a)^).
    rewrite transport_paths_FlFr. simpl.
    repeat rewrite ap_V. rewrite inv_V.
    repeat rewrite concat_pp_p. rewrite concat_Vp.
    rewrite (concat_p1).
    apply moveL_Vp.
    repeat rewrite (concat_p_pp _ _ (concat_1p (1 @ p))). apply moveL_pM.
    match goal with
    |[|- ?XX = _] => assert (rr: 1 = XX)
    end.
    { destruct p. reflexivity. }
    destruct rr.
    apply moveL_Vp. rewrite concat_p1.
    rewrite concat_ap_Fpq.
    rewrite concat_ap_pFq. unfold whiskerR, whiskerL.
    rewrite concat_concat2.
    rewrite concat_p1, (concat_1p (ap (λ u : r a = r a, ap α u @ p) (rp_1 a))).
    rewrite concat_ap_FFpq_p_pp. rewrite concat_ap_Fpq.
    unfold whiskerR. simpl.
    rewrite <- concat2_p_pp. reflexivity.
Qed.

Context `{fs: Funext}.

Lemma equiv_R_id_fun {A:Type} (P: A -> A -> Type) (p0 : forall x, P x x)
      (Q: A -> A -> Type) (q0: forall x, Q x x)
      (φ : forall a b, P a b -> Q a b)
      (κ : forall a, (φ a a) (p0 a) = q0 a)
  : R P p0 -> R Q q0.
Proof.
  refine (R_rec _ _ _ _ _ _).
  intro a; apply r. exact a.
  intros a b p; cbn.
  apply rp. exact (φ a b p).
  intro a; cbn.
  etransitivity; try apply rp_1.
  apply ap. apply κ.
Defined.

Lemma equiv_R_id_sect {A:Type} (P: A -> A -> Type) (p0 : forall x, P x x)
      (Q: A -> A -> Type) (q0: forall x, Q x x)
      (φ : forall a b, P a b <~> Q a b)
      (κ : forall a, (φ a a) (p0 a) = q0 a)
      (κ': forall a, (φ a a)^-1 (q0 a) = p0 a)
      (κκ' : (λ a : A, ap (φ a a)^-1 (κ a)^ @ eissect (φ a a) (p0 a)) = κ')
  : Sect (equiv_R_id_fun Q q0 P p0 (λ a b, equiv_inverse (φ a b)) κ') (equiv_R_id_fun P p0 Q q0 φ κ).
Proof.
  destruct κκ'.
  unfold Sect.
  refine (path_R _ _ _ _ _ _ _); cbn.
  + intro x; reflexivity.
  + intros a b p; cbn.
    refine (concat_1p _ @ _).
    refine (_ @ (concat_p1 _)^).
    refine (ap_idmap _ @ _).
    match goal with |[|- _ = ap (λ x, ?ff (?gg x)) ?pp]
                     => refine (_ @ (ap_compose gg ff pp)^)
    end.
    match goal with
    |[|- _ = ap ?ff _ ]
     => refine (_ @ (ap (ap ff) (R_rec_beta_rp _ _ _ _ _ _ _ _ _))^)
    end.
    refine (_ @ (R_rec_beta_rp _ _ _ _ _ _ _ _ _)^).
    apply ap. symmetry; apply eisretr.
  + intro a; cbn.
    rewrite transport_paths_FlFr.
    repeat rewrite ap_V. rewrite inv_V.
    match goal with
    |[|- ?yy @ ((?zz @ _) @ _) = ?xx @ _] => assert (rr: xx = yy @ zz @ (rp_1 a))
    end.
    { match goal with
      |[|- ?xx @ ?yy = _] => rewrite (concat_p1 xx)
      end.
      rewrite (concat_ap_pFq).
      rewrite concat_pp_p.
      apply moveL_Mp.
      match goal with
      |[|- _ @ whiskerL _ ?pp = _] 
       => pose (whiskerL_1p pp)
      end.
      apply moveL_pV in p. rewrite p; clear p.
      cbn. rewrite concat_p1.
      assert (lemma : forall (X:Type) (x:X) (p:x = x) (r:1 = p),
                 ap (ap idmap) r^ = ap_idmap p @ r^).
      { intros X x p r0. destruct r0.
        reflexivity. }
      specialize (lemma (R Q q0) (r a) (rp a a (q0 a)) (rp_1 a)^).
      rewrite inv_V in lemma. exact lemma. }
    
    rewrite rr; clear rr.
    repeat rewrite concat_pp_p. apply whiskerL. apply whiskerL.
    apply moveR_Vp.
    repeat rewrite concat_p_pp.
    apply moveR_pV.
    repeat rewrite concat_pp_p.
    rewrite concat_ap_Fpq.
    rewrite <- whiskerR_RV.
    match goal with
    |[|- _ = _ @ (_ @ (whiskerR ?pp 1 @ _)) ]
     => pose (whiskerR_p1 pp)
    end.
    rewrite concat_pp_p in p.
    apply moveL_Vp in p. rewrite p; clear p.
    rewrite inv_V. simpl. rewrite concat_1p.
    repeat rewrite concat_p_pp. apply moveL_pV.
    repeat rewrite concat_pp_p.
    do 3 apply moveR_Vp.
    repeat rewrite concat_p_pp.
    match goal with
    |[|- ap (ap ?ff) ?pp = _]
     => refine ((ap02_is_ap _ _ ff _ _ _ _ pp)^ @ _)
    end.
    rewrite ap02_compose.
    repeat rewrite concat_pp_p. apply whiskerL.
    rewrite <- (ap02_is_ap _ _ (R_rec P p0 (R Q q0) (λ a0 : A, r a0)
                                      (λ (a0 b : A) (p : P a0 b), rp a0 b ((φ a0 b) p))
                                      (λ a0 : A, ap (rp a0 a0) (κ a0) @ rp_1 a0)) _ _ _ _ (R_rec_beta_rp Q q0 (R P p0) (λ a0 : A, r a0)
                                                                                                         (λ (a0 b : A) (p : Q a0 b), rp a0 b ((φ a0 b)^-1 p))
                                                                                                         (λ a0 : A,
                                                                                                                 ap (rp a0 a0) (ap (φ a0 a0)^-1 (κ a0)^ @ eissect (φ a0 a0) (p0 a0)) @
                                                                                                                    rp_1 a0) a a (q0 a))).
    simpl. rewrite concat_p1.
    apply moveL_Mp.
    match goal with
    |[|- (ap02 ?ff ?pp)^@ (ap02 ?gg ?qq) = _] =>
     rewrite <- (ap02_V _ _ ff _ _ _ _ pp);
       rewrite <- (ap02_pp ff pp^ qq)
    end.

    pose @R_rec_beta_rp_1.
    unfold equiv_R_id_fun.
    rewrite p.
    rewrite concat_V_pp.
    rewrite ap02_pp.
    rewrite p; clear p.
    repeat rewrite concat_p_pp.
    apply whiskerR.
    transparent assert (X : (∀ a : A, (φ a a)^-1 (q0 a) = p0 a)).
    { intro b. pose (eissect (φ b b) (p0 b)).
      refine (_ @ p).
      apply ap. exact (κ b)^. }

    pose (apD (λ U, R_rec_beta_rp P p0 (R Q q0) (λ a0 : A, r a0)
                                  (λ (a0 b : A) (p : P a0 b), rp a0 b ((φ a0 b) p))
                                  (λ a0 : A, ap (rp a0 a0) (κ a0) @ rp_1 a0) a a 
                                  U) (X a)^). cbn in p.
    rewrite <- p; clear p.
    rewrite transport_paths_FlFr. simpl.
    unfold X; clear X. simpl.
    rewrite (ap_compose (φ a a) (rp a a)). simpl.
    repeat rewrite concat_pp_p.
    rewrite <- (ap_pp (rp a a) (ap (φ a a) (ap (φ a a)^-1 (κ a)^ @ eissect (φ a a) (p0 a))^) (eisretr (φ a a) (q0 a))).
    match goal with
    |[|- _ = _ @ (_ @ ap _ ?pp)] => assert (κ a = pp)
    end.
    { destruct (κ a). cbn.
      rewrite concat_1p. rewrite eisadj.
      rewrite ap_V. symmetry; apply concat_Vp. }
    destruct X.
    apply whiskerR.
    do 2 rewrite ap_V. rewrite inv_V.
    rewrite ap02_is_ap.
    rewrite ap_compose. reflexivity.
Qed.

Lemma isequiv_equiv_R_id_fun {A:Type} (P: A -> A -> Type) (p0 : forall x, P x x)
      (Q: A -> A -> Type) (q0: forall x, Q x x)
      (φ : forall a b, P a b <~> Q a b)
      (κ : forall a, (φ a a) (p0 a) = q0 a)
  : IsEquiv (equiv_R_id_fun P p0 Q q0 φ κ).
Proof.
  refine (isequiv_adjointify _ _ _ _).
  - refine (equiv_R_id_fun Q q0 P p0 (λ a b, equiv_inverse (φ a b)) _).
    intro a. refine (_ @ (eissect (φ a a) (p0 a))).
    apply ap. exact (κ a)^.
  - apply equiv_R_id_sect. reflexivity.
  - apply equiv_R_id_sect.
    apply path_forall; intro a. cbn. destruct (κ a); cbn.
    rewrite concat_1p. rewrite eisadj. rewrite ap_V.
    apply concat_Vp.
Defined.

Lemma equiv_R_id {A:Type} (P: A -> A -> Type) (p0 : forall x, P x x)
      (Q: A -> A -> Type) (q0: forall x, Q x x)
      (φ : forall a b, P a b <~> Q a b)
      (κ : forall a, (φ a a) (p0 a) = q0 a)
  : R P p0 <~> R Q q0.
Proof.
  exists (equiv_R_id_fun P p0 Q q0 φ κ).
  exact (isequiv_equiv_R_id_fun P p0 Q q0 φ κ).
Defined.

Definition equiv_R_fun {A B:Type}
           (P: A -> A -> Type) (p0: forall x, P x x)
           (Q: B -> B -> Type) (q0: forall x, Q x x)
           (α: A -> B)
           (φ: forall a b, P a b -> Q (α a) (α b))
           (κ: forall a, (φ a a) (p0 a) = q0 (α a))
  : R P p0 -> R Q q0.
Proof.
  refine (R_rec _ _ _ _ _ _).
  - intro a. apply r. exact (α a).
  - intros a b p; cbn. apply rp.
    apply φ. exact p.
  - intro a; cbn.
    refine (ap (rp (α a) (α a)) (κ a) @ _).
    apply rp_1.
Defined.

Definition equiv_R {A B:Type}
           (P: A -> A -> Type) (p0: forall x, P x x)
           (Q: B -> B -> Type) (q0: forall x, Q x x)
           (α: A = B)
           (φ: forall a b, P a b <~> Q (equiv_path _ _ α a) (equiv_path _ _ α b))
           (κ: forall a, (φ a a) (p0 a) = q0 (equiv_path _ _ α a))
  : IsEquiv (equiv_R_fun P p0 Q q0 (equiv_path _ _ α) φ κ).
Proof.
  destruct α.
  assert ((equiv_R_fun P p0 Q q0 (equiv_path A A 1) (λ a b : A, φ a b) κ) =
          (equiv_R_id_fun P p0 Q q0 φ κ)).
  { reflexivity. }
  apply isequiv_equiv_R_id_fun.
Defined.

(*

Definition equiv_R_inv {A B:Type}
           (P: A -> A -> Type) (p0: forall x, P x x)
           (Q: B -> B -> Type) (q0: forall x, Q x x)
           (α: A <~> B)
           (φ: forall a b, P a b <~> Q (α a) (α b))
           (κ: forall a, (φ a a) (p0 a) = q0 (α a))
  : R Q q0 -> R P p0.
Proof.
  refine (equiv_R_fun Q q0 P p0 (equiv_inverse α) _ _).
  - intros a b q; cbn.    
    cut (Q (α (α^-1 a)) (α (α^-1 b))).
    apply (φ _ _)^-1.
    apply (transport (λ U, Q (α (α^-1 a)) U) (eisretr α b)^).
    apply (transport (λ U, Q U b) (eisretr α a)^). exact q.
  - intro a; cbn.
    path_via ((φ (α^-1 a) (α^-1 a))^-1 (q0 (α (α^-1 a)))).
    apply ap.
    pose (transport_transport Q (eisretr α a)^ (eisretr α a)^).
    pose (apD q0 (eisretr α a)^).
    destruct (eisretr α a)^. reflexivity.
    path_via ((φ (α^-1 a) (α^-1 a))^-1 ((φ (α^-1 a) (α^-1 a)) (p0 (α^-1 a)))).
    apply ap.
    apply (κ (α^-1 a))^.
    apply eissect.
Defined.

Definition equiv_R_sect {A B:Type}
           (P: A -> A -> Type) (p0: forall x, P x x)
           (Q: B -> B -> Type) (q0: forall x, Q x x)
           (α: A <~> B)
           (φ: forall a b, P a b <~> Q (α a) (α b))
           (κ: forall a, (φ a a) (p0 a) = q0 (α a))
  : forall x, (equiv_R_fun P p0 Q q0 α φ κ) (equiv_R_inv P p0 Q q0 α φ κ x) = x.
Proof.
  refine (path_R _ _ _ _ _ _ _).
  - intro a; cbn. exact (ap r (eisretr α a)).
  - intros a b q; cbn.
    refine (((idpath (ap r (eisretr α a))) @@ (ap_idmap (rp (p0:=q0) a b q))) @ _).
    unfold equiv_R_inv, equiv_R_fun; cbn.
    match goal with
    |[|- _ = ap (λ x, ?ff (?gg x)) ?pp @ _]
     => refine (_ @ ((ap_compose gg ff pp)^ @@ 1))       
    end.
    match goal with
    |[|- _ = ap ?ff (ap (R_rec ?X1 ?X2 ?X3 ?X4 ?X5 ?X6) _) @ _]
     => refine (_ @ ((ap02 ff (R_rec_beta_rp X1 X2 X3 X4 X5 X6 a b q)^) @@ 1))
    end.
    refine (_ @ ((R_rec_beta_rp _ _ _ _ _ _ _ _ _)^ @@ 1)).
    path_via ((rp (p0 := q0) _ _ (transport (λ U : B, Q (α (α^-1 a)) U) (eisretr α b)^
              (transport (λ U : B, Q U b) (eisretr α a)^ q))) @ (ap r (eisretr α b))).
    2: apply whiskerR; apply ap; symmetry; apply eisretr.

*)


(** Madame Maury : B323 *)
