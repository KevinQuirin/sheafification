(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import PathGroupoid_.

Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
Local Open Scope type_scope.

Module Export T.

  Private Inductive T {A B:Type} (f: A -> B) : Type :=
    | t : A -> (T f).

  Arguments t {A B f} a.

  Axiom tp : forall {A B f} (a b:A), f a = f b -> @t A B f a = @t A B f b.

  Axiom tp_1 : forall {A B f} (a:A), @tp A B f a a 1 = 1.

  Definition T_ind {A B:Type} {f:A -> B} (P : T f -> Type)
             (t' : forall a, P (t a))
             (tp' : forall a b p, transport P (tp a b p) (t' a) = t' b)
             (tp_1' : forall a, transport2 P (tp_1 a) (t' a) = tp' a a 1)
    : forall w, P w
    := fun w => match w with
                |t a => fun _ => t' a
                end tp_1'.

  Axiom T_ind_beta_tp : forall {A B:Type} {f:A -> B} (P : T f -> Type)
             (t' : forall a, P (t a))
             (tp' : forall a b p, transport P (tp a b p) (t' a) = t' b)
             (tp_1' : forall a, transport2 P (tp_1 a) (t' a) = tp' a a 1)
             a b p,
      apD (T_ind P t' tp' tp_1') (tp a b p) = tp' a b p.

  Axiom T_ind_beta_tp_1 : forall {A B:Type} {f:A -> B} (P : T f -> Type)
             (t' : forall a, P (t a))
             (tp' : forall a b p, transport P (tp a b p) (t' a) = t' b)
             (tp_1' : forall a, transport2 P (tp_1 a) (t' a) = tp' a a 1)
             a,
      apD02 (T_ind P t' tp' tp_1') (tp_1 a) @ (concat_p1 _) @ (tp_1' a) = T_ind_beta_tp P t' tp' tp_1' a a 1.
        
End T.

Definition T_rec {A B:Type} {f:A -> B} (P:Type)
           (t': A -> P)
           (tp' : forall (a b:A) (p:f a = f b), t' a = t' b)
           (tp_1' : forall a, tp' a a 1 = 1)
  : T f -> P.
Proof.
  simple refine (T_ind _ t' (fun a b p => transport_const _ _ @ tp' a b p)  _).
  intro a.
  pose (p:=whiskerR (transport2_const (A:=T f) (B:= P) (tp_1 a) (t' a) @ concat_p1 _)^ (tp' a a 1)). cbn in p.
  pose (p1:=(whiskerL (transport2 (λ _ : T f, P) (tp_1 a) (t' a)) (tp_1' a) @ concat_p1 _)^).
  exact (p1 @ p).
Defined.

Definition T_rec_beta_tp {A B:Type} {f:A -> B} (P:Type)
           (t': A -> P)
           (tp' : forall (a b:A) (p:f a = f b), t' a = t' b)
           (tp_1' : forall a, tp' a a 1 = 1)
           a b p
  : ap (T_rec P t' tp' tp_1') (tp a b p) = tp' a b p.
Proof.
  simple refine (cancelL (transport_const (tp a b p) (t' a)) _ _ _).
  pose (e1:= T_ind_beta_tp (λ _ : T f, P) t'
        (λ (a0 b0 : A) (p1 : f a0 = f b0),
         transport_const (tp a0 b0 p1) (t' a0) @ tp' a0 b0 p1)
        (λ a0 : A,
         (whiskerL (transport2 (λ _ : T f, P) (tp_1 a0) (t' a0))
            (tp_1' a0) @
          concat_p1 (transport2 (λ _ : T f, P) (tp_1 a0) (t' a0)))^ @
         whiskerR
           (transport2_const (tp_1 a0) (t' a0) @
            concat_p1 (transport2 (λ _ : T f, P) (tp_1 a0) (t' a0)))^
         (tp' a0 a0 1)) a b p). 

  pose (e2:= apD_const (T_ind (λ _ : T f, P) t'
        (λ (a0 b0 : A) (p2 : f a0 = f b0),
         transport_const (tp a0 b0 p2) (t' a0) @ tp' a0 b0 p2)
        (λ a0 : A,
         (whiskerL (transport2 (λ _ : T f, P) (tp_1 a0) (t' a0))
            (tp_1' a0) @
          concat_p1 (transport2 (λ _ : T f, P) (tp_1 a0) (t' a0)))^ @
         whiskerR
           (transport2_const (tp_1 a0) (t' a0) @
            concat_p1 (transport2 (λ _ : T f, P) (tp_1 a0) (t' a0)))^
         (tp' a0 a0 1))) (tp a b p)).
  exact (e2^@ e1).
Defined.

Definition T_rec_beta_tp_1 {A B:Type} {f:A -> B} (P:Type)
           (t': A -> P)
           (tp' : forall (a b:A) (p:f a = f b), t' a = t' b)
           (tp_1' : forall a, tp' a a 1 = 1)
           a
  : ap02 (T_rec P t' tp' tp_1') (tp_1 a) = T_rec_beta_tp P t' tp' tp_1' a a 1 @ (tp_1' a).
Proof.
  apply (cancel2L (transport2_const (tp_1 (f:=f) a) (t' a))).
  apply (cancelL (apD_const (T_rec P t' tp' tp_1') (tp a a 1))).
  apply (cancelR _ _ (concat_p_pp _ (transport_const _ _) _)^).
  apply (cancelR _ _ (whiskerL (transport2 _ (tp_1 a) (t' a)) (apD_const (T_rec P t' tp' tp_1') 1)^)).
  simple refine ((apD02_const (T_rec P t' tp' tp_1') (tp_1 a) )^ @ _).
  apply (cancelR _ _ (concat_p1 (transport2 (λ _ : T f, P) (tp_1 a) (t' a)))).
  apply (cancelR _ _ ((whiskerL (transport2 (λ _ : T f, P) (tp_1 a) (t' a)) (tp_1' a) @
                                concat_p1 (transport2 (λ _ : T f, P) (tp_1 a) (t' a)))^ @
                                                                                             whiskerR
                                                                                             (transport2_const (tp_1 a) (t' a) @
                                                                                                               concat_p1 (transport2 (λ _ : T f, P) (tp_1 a) (t' a)))^
                      (tp' a a 1))).
  Opaque concat_p_pp.
  simple refine (T_ind_beta_tp_1 _ _ _ _ _ @ _); cbn.
  apply (cancelL (apD_const
                    (T_ind (λ _ : T f, P) t'
                           (λ (a0 b0 : A) (p2 : f a0 = f b0),
                            transport_const (tp a0 b0 p2) (t' a0) @ tp' a0 b0 p2)
                           (λ a0 : A,
                                   (whiskerL (transport2 (λ _ : T f, P) (tp_1 a0) (t' a0))
                                             (tp_1' a0) @
                                             concat_p1
                                             (transport2 (λ _ : T f, P) (tp_1 a0) (t' a0)))^ @
                                                                                                  whiskerR
                                                                                                  (transport2_const (tp_1 a0) (t' a0) @
                                                                                                                    concat_p1
                                                                                                                    (transport2 (λ _ : T f, P) (tp_1 a0) (t' a0)))^
                                   (tp' a0 a0 1))) (tp a a 1))^).

  apply (@equiv_inj _ _ _ (isequiv_cancelL (transport_const (tp a a 1) (t' a))
                                           (ap (T_rec P t' tp' tp_1') (tp a a 1))
                                           (tp' a a 1))).

  path_via (T_rec_beta_tp P t' tp' tp_1' a a 1).
  apply (@equiv_inj _ _ _ (isequiv_inverse _ (feq:= isequiv_cancelL (transport_const (tp (f:=f) a a 1) (t' a))
                                                                    (ap (T_rec P t' tp' tp_1') (tp a a 1))
                                                                    (tp' a a 1)))).
  rewrite eissect. cbn. repeat rewrite concat_pp_p.
  rewrite concat_V_pp.
  rewrite !inv_pp. repeat rewrite concat_p_pp. rewrite concat_pp_V.

  rewrite whiskerR_pp. 
  rewrite whiskerR_RV.
  rewrite <- (apD (λ u, (whiskerR (concat_p1 (transport2 (λ _ : T f, P) (tp_1 a) (t' a)))
                                  u)) (tp_1' a)^).
  cbn. rewrite transport_paths_FlFr. cbn. rewrite !ap_V; rewrite !inv_V.
  rewrite !concat_ap_pFq. rewrite ap_idmap. rewrite !inv_pp; rewrite !inv_V.
  rewrite !concat_p_pp. rewrite concat_pV_p. rewrite (concat_p1 ((transport2_const (tp_1 a) (t' a) @@
                                                                                   (T_rec_beta_tp P t' tp' tp_1' a a 1 @ tp_1' a)) @
                                                                                                                                             (concat_p_pp (transport2 (λ _ : T f, P) (tp_1 a) (t' a)) 1 1)^)).
  rewrite whiskerR_RV.
  apply moveL_pV.
  unfold whiskerR at 1, whiskerL at 1.
  rewrite concat_concat2. cbn.
  rewrite (concat_1p (transport2_const (tp_1 a) (t' a))).
  rewrite (concat_p1 (T_rec_beta_tp P t' tp' tp_1' a a 1)).
  simple refine ((concat_p1 _)^ @ _). rewrite !concat_pp_p.
  match goal with
  |[|- _ = (?P @@ ?Q) @ ?R] => path_via (((P @ 1) @@ Q) @ R)
  end.
  2: rewrite (concat_p1 (transport2_const (tp_1 a) (t' a))); reflexivity.
  rewrite <- concat_concat2.
  rewrite !concat_pp_p. apply whiskerL.
  rewrite !concat_p_pp. apply moveL_pV. rewrite concat_1p.
  rewrite !concat_pp_p. simple refine ((concat_p1 _)^@ _).
  apply whiskerL. cbn.
  pose (rew:= @triangulator _ _ _ _ (transport2 (λ _ : T f, P) (tp_1 a) (t' a)) 1).
  apply moveL_Vp in rew. rewrite rew; clear rew. cbn.
  rewrite inv_pp. cbn. rewrite concat_1p. symmetry; apply concat_pV.
Qed.

Lemma path_T_lemma {A A' B:Type} (f: A -> A')
      (α β : T f -> B)
      (eq1: α o t == β o t)
      (eq2: forall a b p, eq1 a @ ap β (tp a b p) = ap α (tp a b p) @ eq1 b)
      (eq3: forall a,  (eq2 a a 1)
                       = transport (λ U, eq1 a @ ap β U = ap α U @ eq1 a) (tp_1 a)^ (concat_p1 (eq1 a) @ (concat_1p (eq1 a))^))
  : ∀ a : A,
    transport2 (λ w : T f, α w = β w) (tp_1 a) (eq1 a) =
    transport_paths_FlFr (tp a a 1) (eq1 a) @
                         (concat_pp_p (ap α (tp a a 1))^
                          (eq1 a)
                            (ap β (tp a a 1))
                            @ cancelL (ap α (tp a a 1))
                            ((ap α (tp a a 1))^ @ (eq1 a @ ap β (tp a a 1))) 
                            (eq1 a)
                            (concat_p_Vp (ap α (tp a a 1)) (eq1 a @ ap β (tp a a 1)) @ eq2 a a 1)).
Proof.
  intro a; cbn.
  rewrite eq3; clear eq3. clear eq2. generalize (eq1 a). intro p. clear eq1.
  unfold cancelL.
  pose (rew :=@transport_paths_FlFr _ _ (λ U:t a = t a, p @ ap β U) (λ U:t a = t a, ap α U @ p)).
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
   => rewrite <- (apD (λ U, ff U p) (tp_1 a)^)
  end.
  cbn.
  rewrite (transport_paths_FlFr (f:= λ U, transport (λ x : T f, α x = β x) U p)
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
                                     ((ap α U)^ @ (p @ ap β U)))^) (tp_1 a)^).
  cbn.
  rewrite (transport_paths_FlFr (f:=(λ U : t a = t a, (ap α U)^ @ (p @ ap β U)))
                                (g:=λ U : t a = t a, (ap α U)^ @ (ap α U @ ((ap α U)^ @ (p @ ap β U))))).
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
  rewrite <- (apD (λ U, (concat_V_pp (ap α U) p)^) (tp_1 a)^). simpl.
  rewrite (transport_paths_Fr (g:= λ U, (ap α U)^ @ (ap α U @ p))).
  clear P2.
  repeat rewrite (concat_p_pp _ _ P8).
  apply moveR_pM.
  set (P2 := ap (λ U : t a = t a, (ap α U)^ @ (ap α U @ p)) (tp_1 a)^).
  
  unfold P8.
  rewrite <- (apD (λ U, whiskerL (z:=β (t a)) (q:= 1 @ p) (r := ap α (tp a a 1) @ p) (ap α U)^) (tp_1 a)^).
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
                         (concat_p_Vp (ap α U) (p @ ap β U)))) (tp_1 a)^).
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
                                                          whiskerL (ap α U)^ (concat_1p p)^)) (tp_1 a)^).
  simpl.
  rewrite transport_paths_FlFr.
  rewrite ap_V. rewrite inv_V.
  match goal with
  |[|- _ @ (_ @ (_ @ ((?PP6 @ ?PP7) @ ?PP8))) = _]
   => set (P6:=PP6); set (P7:=PP7); set (P8:=PP8)
  end.
  
  unfold P5; clear P5.
  rewrite <- (apD (λ U, whiskerL (q:=p @ ap β (tp a a 1)) (r:=p@1) (ap α U)^) (tp_1 a)^).
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
  pose (p1 := whiskerL_1p (ap (λ U : t a = t a, ap α U @ p) (tp_1 a))). simpl in p1.
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
  pose (p1 := whiskerL_1p (ap (λ U : t a = t a, p @ ap β U) (tp_1 a))). simpl in p1.
  apply moveL_pV in p1.
  apply moveL_Mp in p1.
  rewrite p1; clear p1.
  repeat rewrite concat_pp_p.
  unfold  P19, P6, P32, P1, P12, P13, P2, P16.
  clear P19; clear P6; clear P32; clear P1; clear P12; clear P13; clear P2; clear P16.
  (* rewrite inv_V. *)
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
    rewrite <- (ap_V (λ U : t a = t a, p @ ap β U) (tp_1 a)).
    rewrite ap_V. apply moveR_Vp.

    rewrite <- (apD (λ U, concat_1p (p @ ap β U)) (tp_1 a)^).
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
    rewrite concat_concat2. rewrite (concat_p1 (ap (λ u : t a = t a, (ap α u)^) (tp_1 a))).
    rewrite (concat_1p (ap (λ u : t a = t a, p @ ap β u) (tp_1 a))).
    rewrite concat_ap_FpFq_p_pp.
    unfold whiskerR, whiskerL.
    rewrite concat_pp_p. apply moveL_Mp.
    rewrite concat2_inv.
    rewrite concat_concat2.
    rewrite concat_Vp.
    rewrite (concat_1p (ap (λ u : t a = t a, p @ ap β u) (tp_1 a))).
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
  rewrite <- (apD (λ U, concat_1p (ap α U @ p)) (tp_1 a)^).
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
  rewrite concat_p1, (concat_1p (ap (λ u : t a = t a, ap α u @ p) (tp_1 a))).
  rewrite concat_ap_FFpq_p_pp. rewrite concat_ap_Fpq.
  unfold whiskerR. simpl.
  rewrite <- concat2_p_pp. reflexivity.
Qed.

Lemma path_T {A A' B:Type} (f: A -> A')
      (α β : T f -> B)
      (eq1: α o t == β o t)
      (eq2: forall a b p, eq1 a @ ap β (tp a b p) = ap α (tp a b p) @ eq1 b)
      (eq3: forall a,  (eq2 a a 1)
                      = transport (λ U, eq1 a @ ap β U = ap α U @ eq1 a) (tp_1 a)^ (concat_p1 (eq1 a) @ (concat_1p (eq1 a))^))
  : α == β.
Proof.
  simple refine (T_ind _ _ _ _).
  - exact eq1.
  - intros a b p.
    simple refine (transport_paths_FlFr _ _ @ _).
    etransitivity; try apply concat_pp_p.
    apply (cancelL (ap α (tp a b p))).
    etransitivity; try apply eq2.
    apply concat_p_Vp.
  - simple refine (path_T_lemma _ _ _ _ _ _). exact eq3.
Defined.

Lemma T_trunc_fun `{fs: Funext} (m:trunc_index) (A:Type) (B:TruncType m) (f:A -> B)
  : Trunc m (T f) -> Trunc m (T (Trunc_rec (n:=m) f)).
Proof.
  simple refine (Trunc_rec _).
  simple refine (T_rec _ _ _ _).
  intro a. exact (tr (t (tr a))).
  intros a b p; cbn. apply ap. apply tp. exact p.
  intros a; cbn.
  match goal with |[|- ap ?ff ?pp =_] => path_via (ap (x:=t (tr a)) ff 1) end.
  apply ap.
  apply (tp_1 (f:=Trunc_rec (n:=m) f) (tr a)).
Defined.

Lemma T_trunc_inv `{fs: Funext} (m:trunc_index) (A:Type) (B:TruncType m) (f:A -> B)
  : Trunc m (T (Trunc_rec (n:=m) f)) -> Trunc m (T f).
Proof.
  simple refine (Trunc_rec _).
  simple refine (T_rec _ _ _ _).
  simple refine (Trunc_rec _).
  intro a; exact (tr (t a)).
  simple refine (Trunc_ind _ _). intro a. 
  simple refine (Trunc_ind _ _). intros b p.
  cbn in *.
  apply ap. apply tp. exact p.
  simple refine (Trunc_ind _ _).
  intro a. cbn.
  match goal with |[|- ap ?ff ?pp =_] => path_via (ap (x:=t a) ff 1) end.
  apply ap. apply tp_1.
Defined.

Lemma T_trunc_retr `{fs: Funext} (m:trunc_index) (A:Type) (B:TruncType m) (f:A -> B)
  : Sect (T_trunc_inv m A B f) (T_trunc_fun m A B f).
Proof.
  unfold T_trunc_inv, T_trunc_fun.
  simple refine (Trunc_ind _ _).
  simple refine (path_T _ _ _ _ _ _).
  simple refine (Trunc_ind _ _). intro a; reflexivity.
  simple refine (Trunc_ind _ _). intro a.
  simple refine (Trunc_ind _ _). intros b p.
  cbn in *.
  simple refine (concat_1p _ @ _). simple refine (_ @ (concat_p1 _)^).
  match goal with
  |[|- _ = ap (λ x, Trunc_rec ?ff (?gg x)) ?pp]
   => simple refine (_ @ (ap_compose gg (Trunc_rec ff) pp)^)
  end.
  match goal with
  |[|- _ = ap ?ff (ap (T_rec ?X1 ?X2 ?X3 ?X4) (tp ?aa ?bb ?pp)) ]
   => simple refine (_ @ (ap02 ff (T_rec_beta_tp X1 X2 X3 X4 aa bb pp)^))
  end. cbn.
  match goal with
  |[|- _ = ap ?ff (ap ?gg ?pp)]
   => simple refine (_ @ (ap_compose gg ff pp))
  end. cbn.
  match goal with
  |[|- _ = (ap (λ x, T_rec ?X1 ?X2 ?X3 ?X4 x) (tp ?aa ?bb ?pp)) ]
   => simple refine ((T_rec_beta_tp X1 X2 X3 X4 aa bb pp)^)
  end.

  simple refine (Trunc_ind _ _). cbn.
  intro a. rewrite transport_paths_FlFr.
  repeat rewrite ap_V. repeat rewrite inv_V.
  match goal with
  |[|- _ = (?pp @ 1) @ _]
   => rewrite (concat_p1 pp)
  end.
  repeat rewrite concat_p_pp. apply moveL_Mp.
  match goal with
  |[|- ?XX = _] => path_via (XX^^); apply ap
  end.
  match goal with
  |[|- _ = ap (λ x, ap ?ff x @ 1) ?pp] => 
   assert (rr: ap (λ x, ap ff x @ 1) pp = concat_p1 _ @ ap02 ff pp @ (concat_1p _)^)
  end.
  { rewrite concat_ap_Fpq.
    apply moveL_pV.
    apply moveL_Mp.
    rewrite concat_p_pp.
    match goal with
    |[|- (_ @ whiskerR ?hh _) @ _ = _]
     => pose (rew := whiskerR_p1 hh)
    end.
    cbn in *. rewrite rew; clear rew.
    rewrite ap02_is_ap. reflexivity. }
  rewrite rr; clear rr.
  do 4 rewrite inv_pp.
  do 3 rewrite inv_V.
  repeat rewrite concat_pp_p.
  apply whiskerL. cbn.
  rewrite concat_p1.
  rewrite ap02_V. rewrite inv_V.
  match goal with
  |[|- _ = ap02 (λ x, Trunc_rec ?ff (?gg x)) ?pp]
   => rewrite (ap02_compose _ _ _ gg (Trunc_rec ff) _ _ _ _ pp)
  end.
  apply whiskerL.
  rewrite T_rec_beta_tp_1. cbn. rewrite concat_p1.
  rewrite ap02_pp. apply whiskerL.
  rewrite ap02_pp. cbn. rewrite concat_p1.
  rewrite <- ap02_is_ap. apply moveR_Vp.
  match goal with
  |[|- _ = _ @ (ap02 ?ff (ap02 ?gg ?pp))] =>
   pose (rew := ap02_compose _ _ _ gg ff _ _ _ _ pp)
  end.
  cbn in rew. rewrite concat_p1 in rew. repeat rewrite concat_pp_p.
  rewrite <- rew; clear rew.
  rewrite T_rec_beta_tp_1. cbn.
  rewrite concat_ap_pFq.
  rewrite concat_V_pp. apply moveL_Mp. apply moveL_pM.
  match goal with
  |[|- (_ @ whiskerL _ ?hh) @ _ = _] => exact (whiskerL_1p hh)
  end.
Qed.

Lemma T_trunc_sect `{fs: Funext} (m:trunc_index) (A:Type) (B:TruncType m) (f:A -> B)
  : Sect (T_trunc_fun m A B f) (T_trunc_inv m A B f).
Proof.
  unfold T_trunc_fun, T_trunc_inv.
  simple refine (Trunc_ind _ _).
  simple refine (path_T _ _ _ _ _ _).
  intro a; reflexivity.
  intros a b p; cbn.
  simple refine (concat_1p _ @ _). simple refine (_ @ (concat_p1 _)^).
  match goal with
  |[|- _ = ap (λ x, Trunc_rec ?ff (?gg x)) ?pp]
   => simple refine (_ @ (ap_compose gg (Trunc_rec ff) pp)^)
  end.
  match goal with
  |[|- _ = ap ?ff (ap (T_rec ?X1 ?X2 ?X3 ?X4) (tp ?aa ?bb ?pp)) ]
   => simple refine (_ @ (ap02 ff (T_rec_beta_tp X1 X2 X3 X4 aa bb pp)^))
  end. cbn.
  match goal with
  |[|- _ = ap ?ff (ap ?gg ?pp)]
   => simple refine (_ @ (ap_compose gg ff pp))
  end. cbn.
  match goal with
  |[|- _ = (ap (λ x, T_rec ?X1 ?X2 ?X3 ?X4 x) (tp ?aa ?bb ?pp)) ]
   => simple refine ((T_rec_beta_tp X1 X2 X3 X4 aa bb pp)^)
  end.

  intro a. rewrite transport_paths_FlFr.
  repeat rewrite ap_V. repeat rewrite inv_V.
  cbn.
  match goal with
  |[|- _ = (?pp @ 1) @ _]
   => rewrite (concat_p1 pp)
  end.
  repeat rewrite concat_p_pp. apply moveL_Mp.
  match goal with
  |[|- ?XX = _] => path_via (XX^^); apply ap
  end.
  match goal with
  |[|- _ = ap (λ x, ap ?ff x @ 1) ?pp] => 
   assert (rr: ap (λ x, ap ff x @ 1) pp = concat_p1 _ @ ap02 ff pp @ (concat_1p _)^)
  end.
  { rewrite concat_ap_Fpq.
    apply moveL_pV.
    apply moveL_Mp.
    rewrite concat_p_pp.
    match goal with
    |[|- (_ @ whiskerR ?hh _) @ _ = _]
     => pose (rew := whiskerR_p1 hh)
    end.
    cbn in *. rewrite rew; clear rew.
    rewrite ap02_is_ap. reflexivity. }
  rewrite rr; clear rr.
  do 5 rewrite inv_pp.
  repeat rewrite inv_V.
  repeat rewrite concat_pp_p.
  apply whiskerL. cbn. rewrite concat_p1.
  rewrite ap02_V. rewrite inv_V.
  match goal with
  |[|- _ = ap02 (λ x, Trunc_rec ?ff (?gg x)) ?pp]
   => rewrite (ap02_compose _ _ _ gg (Trunc_rec ff) _ _ _ _ pp)
  end.
  apply whiskerL.
  rewrite T_rec_beta_tp_1. cbn. rewrite concat_p1.
  rewrite ap02_pp. apply whiskerL.
  rewrite ap02_pp. cbn. rewrite concat_p1.        
  rewrite <- ap02_is_ap. apply moveR_Vp.
  match goal with
  |[|- _ = _ @ (ap02 ?ff (ap02 ?gg ?pp))] =>
   pose (rew := ap02_compose _ _ _ gg ff _ _ _ _ pp)
  end.
  cbn in rew. rewrite concat_p1 in rew. rewrite <- rew; clear rew.
  rewrite (T_rec_beta_tp_1 (f:= Trunc_rec f)).
  rewrite inv_pp. rewrite inv_V. rewrite concat_pp_p.
  apply whiskerL. 
  rewrite concat_ap_pFq. apply moveL_pM.
  match goal with
  |[|- (_ @ whiskerL _ ?hh) @ _ = _] => exact (whiskerL_1p hh)
  end.
Qed.

Lemma T_trunc `{fs: Funext} (m:trunc_index) (A:Type) (B:TruncType m) (f:A -> B)
  : Trunc m (T f) <~> Trunc m (T (Trunc_rec (n:=m) f)).
Proof.
  simple refine (equiv_adjointify _ _ _ _).
  - apply T_trunc_fun.
  - apply T_trunc_inv.
  - apply T_trunc_retr.
  - apply T_trunc_sect.
Defined.

Definition T_equiv_fun `{ua: Univalence} {A B C:Type}
           (f: A -> B)
           (g: C -> B)
           (α: A -> C)
           (e: g o α = f)
  : T f -> T g.
Proof.
  simple refine (T_rec _ _ _ _).
  intro a; apply t. exact (α a).
  intros a b p; cbn.
  apply tp. exact (ap10 e a @ p @ (ap10 e b)^).
  intro a; cbn.
  path_via (tp (f:=g) (α a) (α a) 1).
  apply ap.
  simple refine ((concat_p1 _ @@ 1) @ _).
  apply concat_pV.
  apply tp_1.
Defined.

Definition isequiv_T_equiv_fun_path `{ua: Univalence} {A B C:Type}
           (f: A -> B)
           (g: C -> B)
           (α: A = C)
           (e: g o (equiv_path _ _ α) = f)
  : IsEquiv (T_equiv_fun f g (equiv_path _ _ α) e).
Proof.
  destruct α. cbn. destruct e.
  unfold T_equiv_fun; cbn.
  assert ((T_rec (T g) (λ a : A, t a)
        (λ (a b : A) (p : g a = g b), tp a b ((1 @ p) @ 1))
        (λ a : A, 1 @ tp_1 a)) == idmap).
  { simple refine (path_T _ _ _ _ _ _).
    intro; reflexivity.
    intros a b p; cbn.
    simple refine (concat_1p _ @ _ @ (concat_p1 _)^).
    simple refine (_ @ (T_rec_beta_tp _ _ _ _ _ _ _)^).
    simple refine (ap_idmap _ @ _).
    apply ap.
    simple refine (_ @ (concat_p1 _)^). exact (concat_1p _)^.
    intro a; cbn.
    rewrite transport_paths_FlFr. cbn.
    rewrite ap_V. rewrite inv_V.
    rewrite concat_ap_pFq.
    rewrite concat_ap_Fpq.
    apply moveR_pV. 
    match goal with
    |[|- _ = ((?P1 @ _) @ ?P2) @ ?P3] =>
     rewrite (concat_p1 P1);
       rewrite (concat_pp_p _ _ P3)
    end.
    match goal with
    |[|- _ = _ @ (whiskerR ?hh 1 @ _) ]
     => pose (rew := whiskerR_p1 hh);
       rewrite concat_pp_p in rew;
       apply moveL_Vp in rew;
       rewrite rew; clear rew
    end.
    rewrite inv_V.
    apply moveR_Mp.
    match goal with
    |[|- _ = ?P1 @ ((whiskerL 1 ?hh) @ ?P3)] =>
     rewrite (concat_p_pp P1);
       pose (rew := whiskerL_1p hh);
       apply moveL_pV in rew;
       rewrite rew; clear rew
    end. cbn.
    repeat rewrite concat_p1; repeat rewrite concat_1p.
    rewrite <- (apD (λ U, ap_idmap U) (tp_1 a)^).
    rewrite transport_paths_FlFr. cbn. rewrite ap_V. rewrite inv_V.
    rewrite concat_p1.
    repeat rewrite concat_pp_p. apply whiskerL.
    repeat rewrite ap_V.
    rewrite <- (ap02_is_ap _ _ (T_rec (T g) (λ a0 : A, t a0)
            (λ (a0 b : A) (p : g a0 = g b), tp a0 b ((1 @ p) @ 1))
            (λ a0 : A, 1 @ tp_1 a0))).
    rewrite T_rec_beta_tp_1.
    rewrite ap_idmap. rewrite (concat_1p (tp_1 a)).
    rewrite inv_pp.  reflexivity. }
  simple refine (isequiv_homotopic idmap  _).
  exact (λ x, (X x)^).
Defined.

Definition isequiv_T_equiv_fun `{ua: Univalence} {A B C:Type}
           (f: A -> B)
           (g: C -> B)
           (α: A <~> C)
           (e: g o α = f)
  : IsEquiv (T_equiv_fun f g α e).
Proof.
  assert ((T_equiv_fun f g α e) = (T_equiv_fun f g (equiv_path _ _ (path_universe_uncurried α)) ((ap (λ u, g o u) (ap (@equiv_fun A C) (equiv_path_path_universe_uncurried α))) @ e))).
  { cbn.
    pose (ap (@equiv_fun A C) (equiv_path_path_universe_uncurried α)).
    pose (apD (λ U, T_equiv_fun f g U) p^).
    cbn in p0. rewrite <- p0. cbn.
    rewrite transport_arrow. rewrite transport_const.
    apply ap.
    cbn. rewrite transport_paths_Fl. apply moveL_Vp.
    rewrite inv_V. reflexivity. }
  simple refine (isequiv_homotopic _ (λ x, ap10 X^ x)).
  exact (isequiv_T_equiv_fun_path f g ((path_universe_uncurried α)) (ap (λ (u : A → C) (x : A), g (u x))
                                                                       (ap (equiv_fun (B:=C)) (equiv_path_path_universe_uncurried α)) @ e)).
Qed.
