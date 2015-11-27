Require Import HoTT HoTT.hit.Truncations Connectedness Utf8_core.
Require Import colimit nat_lemmas.


Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
(* Local Open Scope equiv_scope. *)
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
             (tp_1' : forall a, (transport2 P (tp_1 a) (t' a))^ @ tp' a a 1 = 1)
    : forall w, P w
    := fun w => match w with
                |t a => fun _ => t' a
                end tp_1'.

  Axiom T_ind_beta_tp : forall {A B:Type} {f:A -> B} (P : T f -> Type)
             (t' : forall a, P (t a))
             (tp' : forall a b p, transport P (tp a b p) (t' a) = t' b)
             (tp_1' : forall a, (transport2 P (tp_1 a) (t' a))^ @ tp' a a 1 = 1)
             a b p,
     apD (T_ind P t' tp' tp_1') (tp a b p) = tp' a b p.
        
End T.

Definition T_rec {A B:Type} {f:A -> B} (P:Type)
           (t': A -> P)
           (tp' : forall (a b:A) (p:f a = f b), t' a = t' b)
           (tp_1' : forall a, tp' a a 1 = 1)
  : T f -> P.
Proof.
  refine (T_ind _ t' (fun a b p => transport_const _ _ @ tp' a b p)  _).
  intro a.
  exact ((concat_p_pp (transport2 (λ _ : T f, P) (tp_1 a) (t' a))^  (transport_const (tp a a 1) (t' a)) (tp' a a 1))                                                                                                 @ whiskerR (moveR_Vp _ _ _ (transport2_const (A:=T f) (B:= P) (tp_1 a) (t' a))) (tp' a a 1)                                                                                                         @ concat_1p _                                                                                     @ (tp_1' a)).
Defined.

Definition T_rec_beta_tp {A B:Type} {f:A -> B} (P:Type)
           (t': A -> P)
           (tp' : forall (a b:A) (p:f a = f b), t' a = t' b)
           (tp_1' : forall a, tp' a a 1 = 1)
           a b p
  : ap (T_rec P t' tp' tp_1') (tp a b p) = tp' a b p.
Proof.
Admitted.
  

Section Gpd.

  Definition Gpd_graph_ : graph.
  Proof.
    refine (Build_graph _ _).
    exact nat.
    intros n m. exact (S n = m).
  Defined.

  Definition Gpd_aux_ (X:Type) (n:nat) : Type.
  Proof.
    induction n.
    - exact X. 
    - exact (T (λ x:IHn, tt)).
  Defined.
  
  Definition Gpd_ (X:Type) : diagram Gpd_graph_.
  Proof.
    refine (Build_diagram _ _ _).
    - intros i. exact (Gpd_aux_ X i).
    - intros i j q; destruct q; simpl.
      exact t.
  Defined.

End Gpd.

Section TheProof.
  (* There, we want to prove that the colimit of the sequence of iterated kernel pairs is the truncation of [X].

The proof is just a traduction of the one created by F. Van Doorn, available in Lean here : https://github.com/fpvandoorn/leansnippets/blob/master/truncation.hlean .

We first show that the colimit is [hProp].
   *)


  Lemma ap_w_const (X Y:Type) (f:X -> Y) (wconst : forall x y, f x = f y) (x y : X) (p q:x=y)
    : ap f p = ap f q.
  Proof.
    assert (H' : forall (a b:X) (r:a=b), (wconst x a)^ @ (wconst x b) = ap f r).
    { intros a b r. destruct r. simpl. apply concat_Vp. }
    transitivity ((wconst x x)^ @ wconst x y).
    symmetry; apply H'.
    apply H'.
  Defined.
    
  
  Variable (X:Type).
  Let D := @Gpd_ X.
  Let Q := colimit D.


  Instance trans_le : Transitive Peano.le.
  Proof.
    intros i j k p.
    induction p.
    exact idmap.
    intro q. apply IHp.
    exact (le_pred _ _ (le_S _ _ q)).
  Defined.
    
  Lemma not_ge_lt (n m:nat) (H: Peano.le n m) (H': Peano.le (m.+1) n) : Empty.
  Proof.
    assert (H0 : Peano.le n.+1 n).
    transitivity (m.+1).
    exact (le_succ _ _ H).
    exact H'.
    destruct (not_le_S _ H0).
  Qed.

  Lemma le_eq_lt {n m:nat}
    : (Peano.le n m) -> (n=m) + (Peano.lt n m).
  Proof.
    intro H.
    destruct H.
    left; reflexivity.
    right; exact (le_succ _ _ H).
  Defined.
  
  Lemma gt_lt_cases (n m:nat) : (Peano.le n m) + (Peano.le m n).
  Proof.
    induction n, m.
    - left; apply le_n.
    - left; apply le_0.
    - right; apply le_0.
    - destruct IHn.
      destruct (le_eq_lt l).
      destruct p.
      right; exact (le_S _ _ (le_n _)).
      left; exact l0.

      destruct (le_eq_lt l).
      destruct p.
      right; apply le_S; apply le_n.
      right. apply le_S. exact l.
  Qed.
  
  Lemma leS_ge : forall (i j:nat), (Peano.le i (j.+1)) -> (Peano.le j i) -> ((j.+1 = i) + (j = i)).
  Proof.
    induction i, j.
    - intros H H0. right; reflexivity.
    - intros H H0. destruct (not_lt_0 j). exact H0.
    - intros H H0. left. apply ap.
      symmetry; apply le_0_is_0.
      apply (le_pred _ _ H).
    - intros H H0.
      destruct (IHi j (le_pred _ _ H) (le_pred _ _ H0)).
      destruct p; left; reflexivity.
      destruct p; right; reflexivity.
  Qed.

  Definition eq_same (i:nat) (x y:D i) : colim x = colim y.
  Proof.
    transitivity (colim (diagram1 D (i:=i) (j:=(i.+1)) 1 x)).
    symmetry; apply pp.
    transitivity (colim (diagram1 D (i:=i) (j:=(i.+1)) 1 y)).
    apply ap. simpl.
    apply tp. reflexivity.
    apply pp.
  Defined.
    
  Definition HPropQ_fun_ij {i j:nat} (H : Peano.le i j) : D i -> D j.
  Proof.    
    induction H.
    exact idmap.
    exact ((diagram1 D (i := m) (j:= m.+1) idpath) o IHle).
  Defined.

  Definition HPropQ_colim_ij {i j:nat} (H : Peano.le i j)
    : forall (x:D i), colim x = colim (HPropQ_fun_ij H x).
  Proof.
    induction H.
    intro; reflexivity.
    intro x.
    etransitivity; [exact (IHle x) |].
    symmetry; apply pp.
  Defined.

  Lemma HPropQ_ij_eq (i j:nat) (x:D i) (y:D j) (H : Peano.le i j) : colim x = colim y.
  Proof.
    transitivity (colim (HPropQ_fun_ij H x)).
    apply HPropQ_colim_ij.
    generalize (HPropQ_fun_ij H x); intro d.
    transitivity (colim (diagram1 D (i := j) (j:= j.+1) idpath d)).
    symmetry; apply pp.
    transitivity (colim (diagram1 D (i := j) (j:= j.+1) idpath y)).
    apply ap.
    apply tp. reflexivity.
    (* exact (@cp ((D j)*(D j)) (D j) fst snd (d,y)). *)
    apply pp.
  Defined.

  Lemma HPropQ_fun_ij_map {i j:nat} (H : Peano.le i j) (H': Peano.le (i.+1) j) (x:D i)
    : HPropQ_fun_ij H x = HPropQ_fun_ij H' (diagram1 D (i := i) (j:= i.+1) idpath x).
  Proof.
    assert (rew : le_pred _ _ (le_S _ _ H') = H) by apply (path_ishprop (H := IsHProp_le _ _)); destruct rew.
    induction H'.
    - assert (rew : le_S _ _ (le_n i) = (le_pred i.+1 i.+2 (le_S i.+1 i.+1 (le_n i.+1)))) by apply (path_ishprop (H := IsHProp_le _ _)); destruct rew; cbn. reflexivity.
    - cbn in *.
      assert (rew : le_S _ _ (le_pred _ _ (le_S _ _ H')) = (le_pred i.+1 m.+2 (le_S i.+1 m.+1 (le_S i.+1 m H')))) by apply (path_ishprop (H := IsHProp_le _ _)); destruct rew; cbn.
      unfold HPropQ_fun_ij in *. simpl in *.
      exact (ap t IHH').
  Defined.

  Lemma i_fr_step (i j:nat) (H : Peano.le i j) (x:D i) 
    : (HPropQ_colim_ij (le_S _ _ H) x) = (HPropQ_colim_ij H x) @ (@pp _ D j (j.+1) 1 (HPropQ_fun_ij H x))^.
  Proof.
    induction H.
    - cbn. hott_simpl.
    - cbn. repeat rewrite inv_pp. repeat rewrite inv_V.
      reflexivity.
  Defined.

  Lemma ap_i_ap_f (i:nat) (x y : D i) (p : x = y)
    : ap colim (ap (diagram1 D (i := i) (j := i.+1) 1) p)
      = (@pp _ D i (i.+1) 1 x) @ (ap colim p) @ (@pp _ D i (i.+1) 1 y)^.
  Proof.
    destruct p; cbn. hott_simpl.
  Defined.

  Lemma ap_i_eq_ap_i_same (i:nat) (x y : D i) (p q : x=y)
    : ap colim p = ap colim q.
  Proof.
    apply ap_w_const. apply eq_same.
  Defined.    
  
  Lemma i_fr_g (i j:nat) (H : Peano.le i j) (H': Peano.le (i.+1) j) (x:D i)
    : (pp _ D i (i.+1) 1 x)^ @ HPropQ_colim_ij H' (diagram1 D (i:=i) (j:=i.+1) 1 x) @ (ap (colim (D:=D) (i := j)) (HPropQ_fun_ij_map H H' x))^ = HPropQ_colim_ij H x.
  Proof.
    assert (rew : le_pred _ _ (le_S _ _ H') = H) by apply (path_ishprop (H := IsHProp_le _ _)); destruct rew.
    induction H'.
    - cbn. rewrite concat_p1.
      assert (rew : le_S _ _ (le_n i) = (le_pred i.+1 i.+2 (le_S i.+1 i.+1 (le_n i.+1)))) by apply (path_ishprop (H := IsHProp_le _ _)); destruct rew; cbn.
      transitivity ((pp Gpd_graph_ D i i.+1 1 x)^ @ 1).
      2:hott_simpl.
      apply whiskerL. 
      assert (rew : 1 = (HPropQ_fun_ij_map (le_S i i (le_n i)) (le_n i.+1) x)).
      unfold HPropQ_fun_ij_map. simpl.
      pose (H := IsHProp_le).
      match goal with
      |[|- _ =  match ?xx with |1 => match ?yy with |1 => _ end end] => set (foo := yy); set (bar := xx)
      end.
      destruct foo.
      assert (X0 : 1 = bar).
      apply path_ishprop. destruct X0. reflexivity.
      destruct rew; cbn. reflexivity.
    - rewrite (i_fr_step _ _ H' (diagram1 D (i:=i) (j:=i.+1) 1 x)).
      assert ( rew : le_S _ _ (le_pred i.+1 m.+1 (le_S i.+1 m H')) = (le_pred i.+1 m.+2 (le_S i.+1 m.+1 (le_S i.+1 m H')))) by apply (path_ishprop (H := IsHProp_le _ _)); destruct rew.
      simpl.
      rewrite <- IHH'. clear IHH'.
      repeat rewrite concat_pp_p; apply whiskerL. apply whiskerL.
      apply moveL_Vp.
      match goal with |[|- _ = ?xx] => transitivity (xx @ 1); [| hott_simpl] end.
      apply moveL_Vp.
      repeat rewrite concat_p_pp. 
      apply moveR_pV. rewrite concat_1p.
      rewrite <- (ap_i_ap_f m _ _ (HPropQ_fun_ij_map (le_pred i.+1 m.+1 (le_S i.+1 m H')) H' x)).
      apply ap_i_eq_ap_i_same.
  Defined.

  Definition eq_same_con (i:nat) (x y z:D i) (p:y=z)
    : eq_same i x y = eq_same i x z @ (ap colim p)^.
  Proof.
    destruct p; symmetry; apply concat_p1.
  Defined.
    
  Definition HPropQ : IsHProp Q.
  Proof.
    apply hprop_allpath.
    assert (hp: forall x:Q, IsHProp (forall y:Q, x=y)).
    { intro x. apply hprop_inhabited_contr.
      intro H.
      assert (Contr Q).
      exists x. exact H.
      apply trunc_forall. }
    refine (colimit_rect _ _ _ _ _).
    2:intros; apply path_ishprop.
    clear hp.
    intros i x; cbn.
    refine (colimit_rect _ _ _ _ _).
    - intros j y.
      cbn in *.
      destruct (gt_lt_cases i j).
      transitivity (colim (HPropQ_fun_ij l x)).
      apply HPropQ_colim_ij.
      apply eq_same.

      transitivity (colim (HPropQ_fun_ij l y)).
      apply eq_same.
      symmetry; apply HPropQ_colim_ij.

    - intros j i0 f y; destruct f; cbn.
      rewrite transport_paths_Fr.
      rewrite ap_idmap.
      destruct (gt_lt_cases i (j.+1)), (gt_lt_cases i j).
      + assert (rew : Peano.le_S i j l0 = l) by apply (path_ishprop (H := IsHProp_le _ _)); destruct rew.
        rewrite i_fr_step.
        repeat rewrite concat_pp_p; apply whiskerL.
        unfold eq_same; simpl.
        repeat rewrite concat_pp_p; apply whiskerL.
        repeat rewrite concat_p_pp; apply whiskerR.
        apply moveR_pM.
        apply moveR_Vp.
        rewrite concat_p_pp.
        match goal with
        |[|- _ = (pp _ _ _ _ _ ?xx) @ ap _ ?ppp @ (pp _ _ _ _ _ ?yy)^] => 
         etransitivity; [| exact (ap_i_ap_f (j.+1) xx yy ppp)]
        end.
        apply ap_i_eq_ap_i_same.
      + destruct (leS_ge _ _ l l0).
        destruct p.
        assert (rew : le_n (j.+1) = l) by apply (path_ishprop (H := IsHProp_le _ _)); destruct rew.
        assert (rew : le_S _ _ (le_n j) = l0) by apply (path_ishprop (H := IsHProp_le _ _)); destruct rew. unfold eq_same. cbn. hott_simpl.
        
        destruct p.
        assert (rew : le_n j = l0) by apply (path_ishprop (H := IsHProp_le _ _)); destruct rew.
        assert (rew : le_S _ _ (le_n j) = l) by apply (path_ishprop (H := IsHProp_le _ _)); destruct rew.
        unfold eq_same. cbn. hott_simpl.
        repeat rewrite concat_p_pp; apply whiskerR.
        repeat rewrite concat_pp_p; apply whiskerL. 
        apply moveR_Vp. apply moveR_pM.
        match goal with
        |[|- _ = (pp _ _ _ _ _ ?xx) @ ap _ ?ppp @ (pp _ _ _ _ _ ?yy)^] => 
         etransitivity; [| exact (ap_i_ap_f (j.+1) xx yy ppp)]
        end.
        apply ap_i_eq_ap_i_same.
      + destruct (not_ge_lt _ _ l0 l).
      + unfold eq_same; simpl.
        apply moveR_pM. apply moveR_pV.
        assert (X0 : (ap colim (HPropQ_fun_ij_map l0 l y)) = (HPropQ_colim_ij l0 y)^ @ (pp Gpd_graph_ D j j.+1 1 y)^ @ HPropQ_colim_ij l (t y) ).
        { rewrite concat_pp_p. apply moveL_Vp. apply moveR_pM.
          exact (i_fr_g _ _ l0 l y)^. }
        repeat rewrite (concat_pp_p).
        apply moveL_Vp. apply moveL_Mp. apply moveL_Mp.
        repeat rewrite concat_p_pp.
        rewrite <- X0; clear X0.
        repeat rewrite concat_pp_p.
        apply moveR_Vp.
        apply moveR_Vp.
        rewrite concat_p_pp. rewrite concat_pV. rewrite concat_1p.
        apply moveR_pM.
        match goal with
        |[|- _ = _ @ (_ @ ap colim ?ff) @ _ ] => pose (p := ap_i_ap_f i _ _ ff)
        end. simpl in p.
        repeat rewrite concat_pp_p; repeat rewrite concat_pp_p in p.
        rewrite <- p; clear p.
        rewrite <- ap_pp.
        apply ap_i_eq_ap_i_same.
  Qed.
    
  Theorem VD_truncation : Q <~> Trunc -1 X.
  Proof.
    refine (equiv_adjointify _ _ _ _).
    3:intro; apply path_ishprop.
    3:intro; apply (path_ishprop (H:=HPropQ)).
    - refine (colimit_rectnd _ _ _ _ _).
      2:intros i j f x; apply path_ishprop.
      induction i.
      exact tr. simpl.
      refine (T_ind _ _ _ _).
      exact IHi.
      intros; apply path_ishprop.
      intros; apply path_ishprop.
    - refine (Trunc_rec _). exact HPropQ.
      exact (colim (D:=Gpd_ X) (i:=0)).
  Defined.
  
  
End TheProof.