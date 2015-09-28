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
             (rp_1' : forall a, (transport2 Q (rp_1 a) (r' a))^ @ rp' a a (p0 a) = 1)
    : forall w, Q w
    := fun w => match w with
                |r a => fun _ => r' a
                end rp_1'.

  Axiom R_ind_beta_rp : forall {A:Type} (P:A -> A -> Type) (p0: forall x:A, P x x)
             (Q : R P p0 -> Type)
             (r' : forall a, Q (r a))
             (rp' : forall a b p, transport Q (rp a b p) (r' a) = r' b)
             (rp_1' : forall a, (transport2 Q (rp_1 a) (r' a))^ @ rp' a a (p0 a) = 1)
             a b p,
      apD (R_ind P p0 Q r' rp' rp_1') (rp a b p) = rp' a b p.

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
  exact ((@concat_p_pp _ _ _ _ _ ((transport2 (λ _ : R P p0, Q) (rp_1 a) (r' a))^)  (transport_const (rp a a (p0 a)) (r' a)) (rp' a a (p0 a)))                                                                                                 @ whiskerR (moveR_Vp _ _ _ (transport2_const (A:=R P p0) (B:= Q) (rp_1 a) (r' a))) (rp' a a (p0 a))                                                                                                         @ concat_1p _                                                                                     @ (rp_1' a)).
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
    apply moveR_Vp.

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
    repeat rewrite concat_pp_p. apply whiskerL.
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
    