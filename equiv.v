Require Export Utf8_core.
Require Import HoTT.
Require Import path univalence.

Set Universe Polymorphism.
Set Implicit Arguments.

Definition S_le n : (n <= trunc_S n)%trunc.
  induction n. exact tt. exact IHn. Defined.
  
Definition IsMono (A B : Type) (f : A -> B) := forall x y, IsEquiv (ap f (x:=x) (y:=y)).


Definition IsMonof (A B : Type) (f : A -> B) := forall (X:Type) (x y : X -> A), 
                                                      IsEquiv (apf f (x:=x) (y:=y)).

Definition IsMonof_isMono (A B : Type) (f : A -> B) : IsMonof f = IsMono f.
  (* apply univalence_hprop. repeat (apply (@trunc_forall _ _ (fun P => _)); intro).  *)
  (* apply hprop_isequiv. *)
  (* repeat (apply (@trunc_forall _ _ (fun P => _)); intro). apply hprop_isequiv. *)
  (* split. *)
  (* - intro H. intros x y. *)
  (*   apply isequiv_adjointify with (g := λ p:(f x = f y), (ap10 (equiv_inv (IsEquiv := H B (fun _ => x) (fun _ => y)) (path_forall (λ _ : B, f x) (λ _ : B, f y) (fun _ => p))) (f x))). *)
  (*   + intro u. unfold equiv_inv. destruct (H B (fun _ => x) (fun _ => y)). unfold composition, Sect in *; simpl in *. *)
  (*     admit.   *)
  (*   + intro v.  destruct (H B (fun _ => x) (fun _ => y)). unfold composition, Sect in *; simpl in *. destruct v. simpl in *. *)
  (*     rewrite path_forall_1. *)
  (*     admit. *)
  (* - intro H. intros X x y. *)
  (*   apply isequiv_adjointify with (g := λ p, path_forall _ _ (fun u => (equiv_inv (IsEquiv := H (x u) (y u)) (ap10 p u)))). *)
  (*   + intro p. unfold ap10. *)
  (*     admit. *)
  (*   + intro p. destruct p. simpl. admit. *)
      
Admitted.

Definition Trunc (n:trunc_index) := {T:Type & IsTrunc n T}.

Definition HProp := Trunc minus_one.

Lemma IsEquiv_unique : forall (A B:Type), forall (h : A -> B), forall (f g : IsEquiv h), f=g.
Proof.
  intros.
  apply allpath_hprop.
Defined. 

Instance Contr_IsEquiv A B (f : A -> B) (a : IsEquiv f): IsTrunc minus_two (IsEquiv f).
apply BuildContr with (center := a).
intro; apply IsEquiv_unique.
Defined.

Lemma IsHProp_IsTrunc A : IsHProp A -> forall n:trunc_index, IsTrunc (trunc_S n) A.
  induction n. 
  - assumption. 
  - apply (@trunc_succ _ _ IHn).
Defined.
  
Lemma concat_ap (A B:Type) (f : A -> B) (x y: A) (equiv_inv : B -> A) (eisretr : Sect equiv_inv f) (eissect : Sect f equiv_inv) :
    forall (eq : f x = f y), eisretr (f x) @ eq @ (eisretr (f y))^%path = ap f (ap equiv_inv eq).
  Proof.
    intro.
    destruct eq. simpl. 
    rewrite concat_p1.
    apply inverse_inv_R.
  Defined.
  
  Lemma concat_ap2 (A B:Type) (f : A -> B) (x y: A) (equiv_inv : B -> A) (eisretr : Sect equiv_inv f) (eissect : Sect f equiv_inv) :
    forall eq, ap equiv_inv (ap f eq) = (eissect x) @ eq @ (eissect y)^%path.
  Proof.
    intro.
    destruct eq.
    simpl. rewrite concat_p1.
    exact (id_sym (inverse_inv_R _)).
  Qed.

  Definition equiv_is_mono_f (A B:Type) (f: A -> B) (H :IsEquiv f) (x y : A) : f x = f y -> x = y. 
    intro X. destruct H as [equiv_inv eisretr eissect eisadj].
    pose (Y := ap equiv_inv X).
    pose (eq1 := eissect x); pose (eq2 := eissect y).
    exact (eq1^%path @ Y @ eq2).
  Defined.

  Instance equiv_is_mono_eq (A B:Type) (f: A -> B) (H :IsEquiv f) (x y : A) : IsEquiv (ap (x:=x) (y:=y) f).
  apply (isequiv_adjointify _ (equiv_is_mono_f _ x y)).
  - destruct H as [equiv_inv eisretr eissect eisadj].
    intro z. unfold equiv_is_mono_f.
    assert  (ap f (((eissect x) ^%path @ ap equiv_inv z) @ eissect y) = (eisretr (f x))^%path @ (eisretr (f x)) @ ap f (((eissect x)^%path @ ap equiv_inv z) @ eissect y) @ (eisretr (f y))^%path @ (eisretr (f y))).
      rewrite (inverse_inv_L).
      rewrite <- (concat_p_pp).
      rewrite <- (concat_p_pp).
      rewrite (inverse_inv_L).
      rewrite (idpath_L).
      rewrite (idpath_R).
      reflexivity. 
    rewrite (X). clear X.

    assert ((eisretr (f x)) @ ap f (((eissect x) ^%path @ ap equiv_inv z) @ eissect y) @ (eisretr (f y)) ^%path
                       =
                (ap f (ap equiv_inv ( ap f ((eissect x)^%path @ (ap equiv_inv z) @ (eissect y)))))).

      apply concat_ap.
      exact eissect.

    rewrite <- (concat_p_pp) with (p := (eisretr (f x)) ^%path) (q := eisretr (f x)) (r := ap f (((eissect x) ^%path @ ap equiv_inv z) @ eissect y)).
    rewrite <- (concat_p_pp) with (p := (eisretr (f x)) ^%path) (q := (eisretr (f x) @ ap f (((eissect x) ^%path @ ap equiv_inv z) @ eissect y))) (r := (eisretr (f y)) ^%path).
    
    rewrite X. clear X.
    
    assert ((ap equiv_inv (ap f (((eissect x) ^%path @ ap equiv_inv z) @ eissect y))) = ap equiv_inv z).
      rewrite concat_ap2 with (eissect := eissect).
      rewrite <- (concat_p_pp). rewrite <- (concat_p_pp).
      rewrite (inverse_inv_R).
      rewrite (concat_p_pp). rewrite (concat_p_pp).
      rewrite (inverse_inv_R).
      rewrite (idpath_L).
      rewrite (idpath_R).
      reflexivity.
      exact eisretr.

    rewrite X. clear X.

    rewrite <- concat_ap with (eisretr := eisretr).

    rewrite <- (concat_p_pp). rewrite <- (concat_p_pp).
    rewrite (inverse_inv_L).
    rewrite (concat_p_pp). rewrite (concat_p_pp).
    rewrite (inverse_inv_L).
    rewrite (idpath_L).
    rewrite (idpath_R).
    reflexivity.
    exact eissect.
  - unfold equiv_is_mono_f.
    destruct H as [equiv_inv eisretr eissect eisadj]; intro z; destruct z.
    destruct (eissect x); reflexivity.
  Defined.

  Definition equiv_is_mono (A B:Type) (f: A -> B) : IsEquiv f -> IsMono f :=
    fun H x y => equiv_is_mono_eq _ _ _.
  
Instance Tn_is_TSn : forall n, IsTrunc (trunc_S n) (Trunc n). (* Cf HoTT *)
Admitted.


Definition truncn_unique n (A B : Trunc n) : A.1 = B.1 -> A = B.
  intro e. destruct A, B. apply path_sigma' with (p:=e).  apply allpath_hprop.
Defined.

Lemma IsMono_IsHProp_fibers (A B:Type) (f:A->B) : IsMono f -> forall b:B, IsHProp ({ a:A & f a =b}).
  intros H b x y; simpl.
  destruct x as [x p], y as [y q].
  unfold IsMono in H.
  specialize (H x y). destruct H.

  assert (existT _ x p = existT (fun u => f u = b) y q).
  apply @path_sigma' with (p:= equiv_inv (p@q^)).
  destruct (equiv_inv (p@q^)).
  
  (* destruct x as [x p], y as [y q]. *)

  (* destruct (H x y). unfold Sect in *. simpl in *. clear eisadj. *)
  (* pose (foo := eisretr _ (IsEquiv := H x y)). unfold Sect in foo. *)
  
  (* assert (r := equiv_inv (IsEquiv := H x y) (p @ (inverse q))%path). destruct r. *)
  (* specialize (foo (p @ inverse q)%path). simpl in foo. destruct p. hott_simpl. destruct q. *)
  (* exists . *)
  (* assert (x = y). *)
  (*   apply path_sigma with (p:= r). *)
    
  
Admitted.
  

Definition HProp_contr A (B : A -> Type) (BProp : forall a, IsHProp (B a)) (a a' : A )
             (b : B a) (b' : B a') (e : a = a') : 
  Contr (e # b = b').
  destruct e.
  destruct (BProp a b b').
  apply BuildContr with (center := center).
  intro. apply (@path2_contr _ (contr_inhabited_hprop (B a) b) b b').
Defined.

Instance subset_is_subobject A (B : A -> Type) (BProp : forall a, IsHProp (B a)) x y : 
  IsEquiv (ap (pr1 (P := B)) (x:=x) (y:=y)).
destruct x, y.
apply  (isequiv_adjointify (ap (pr1 (P := B)) (x:=(x;b)) (y:=(x0;b0)))
                           (eq_dep_subset B BProp b b0)). 
- intro. unfold eq_dep_subset; simpl in *. destruct x1. 
  apply (projT1_path_sigma (P:=B) (u:=(x;b)) (v:=(x;b0)) idpath (center (b = b0))). 
- intro. unfold eq_dep_subset, path_sigma'; simpl in *. 
  pose (foo := eta_path_sigma x1). etransitivity; try exact foo. 
  apply ap. destruct (@HProp_contr A B BProp x x0 b b0 x1..1).
  etransitivity; try apply contr. symmetry. apply contr.
Defined.

Definition elim_E A B (f:A->B) (H:IsEquiv f) (x y : A) (p : f x = f y)
: x = y :=
  id_sym (eissect f x) @ @moveR_E _ _ (f ^-1)%equiv isequiv_inverse _ _ p.


Definition True_is_irr (x y : Unit) : x = y.
  destruct x, y. reflexivity. Defined.

Instance true_ishprop : IsHProp Unit.
intros x y. apply BuildContr with (center := True_is_irr x y). 
intro e. destruct e, x. reflexivity.
Defined.

Definition HTrue := (Unit; true_ishprop) : HProp.

Theorem univalence_hprop' (A B: HProp) : (A.1 <-> B.1) -> A = B.
Proof.
  destruct A, B. intro. apply eq_dep_subset. intro. apply hprop_trunc.
  apply univalence_hprop; auto.
Defined.

