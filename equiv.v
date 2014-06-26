Require Export Utf8_core.
Require Import HoTT.
Require Import univalence.

Set Universe Polymorphism.
Set Implicit Arguments.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

Definition S_le n : (n <= trunc_S n)%trunc.
  induction n. exact tt. exact IHn. Defined.

Definition IsMono (A B : Type) (f : A -> B) := forall x y, IsEquiv (ap f (x:=x) (y:=y)).


Definition IsMonof (A B : Type) (f : A -> B) := forall (X:Type) (x y : X -> A), 
                                                  IsEquiv (ap (fun u => f o u) (x:=x) (y:=y)).

Definition IsMonof_to_isMono (A B : Type) (f : A -> B) : IsMonof f -> IsMono f.
  intro H. intros x y.
  unfold IsMonof in H.
  specialize (H A). specialize (H (fun _ => x) (fun _ => y)).
  destruct H as [inv retr sect _]. unfold compose in inv.
  apply isequiv_adjointify with (g := fun (H:f x = f y) =>
            ap10 (inv (path_forall
                         (A:=A)
                         (fun _ => f x)
                         (fun _ => f y)
                         (fun x => H)))
                 x).
  - intro u.
    etransitivity; try exact (ap_ap10 (λ _ : A, x) (λ _ : A, y) f (inv (path_forall (λ _ : A, f x) (λ _ : A, f y) (λ _ : A, u))) x).
    rewrite retr.
    unfold ap10. unfold path_forall.
    rewrite eisretr.
    exact idpath.
  - intro u. destruct u; simpl in *. 
    rewrite path_forall_1.
    apply (transport (fun u => ap10 u x = 1) (sect 1)^).
    exact idpath.
Defined.

(* About ap_ap10_L. *)

(* Lemma path_forall_ap10 (A B X : Type) (a b : X -> A) (f : A -> B) (p : f o a = f o b) (H : ∀ x : X, f (a x) = f (b x) → a x = b x) (HH : f o a = f o b -> a = b) (HHH : forall x, H x (ap10 p x) = apD10 (HH p) x) *)
(* : (path_forall _ _ (λ x, H x (ap10 p x))) = HH p. *)
(*   (* assert (foo := HH p); destruct foo. *) *)
(*   unfold path_forall, equiv_inv. *)
(*   destruct (isequiv_apD10 X (λ _ : X, A) a b). unfold Sect in *. *)
(*   clear eisadj. *)
(*   specialize (eissect (HH p)). rewrite <- eissect. *)
(*   apply ap. *)
(*   apply path_forall; intro x. simpl. *)
(*   exact (HHH x). *)
(* Qed. *)
    
(*  Lemma ap10_ap (A B X : Type) (a b : X -> A) (f : A -> B) (p : f o a = f o b) (H : ∀ x : X, f (a x) = f (b x) → a x = b x) *)
(* : ap (λ u : X -> A, f o u) (path_forall _ _ (λ x, H x (ap10 p x))) = p. *)
(*    simpl in *. *)
   

(* Definition IsMono_to_IsMonof (A B : Type) (f : A -> B) : IsMono f -> IsMonof f. *)
(*   intro H. *)
(*   intros X a b. *)
(*   pose (φ := fun p => path_forall a b (fun x => equiv_inv (IsEquiv := H (a x) (b x)) (ap10 p x))). *)
(*   apply isequiv_adjointify with (g:= φ). *)
(*   - intro p. *)
(*     unfold φ. *)
(*     pose (fooo := path_forall_ap10). *)
(*     specialize (fooo A B X a b f p). *)
(*     (* unfold equiv_inv. *) *)
(*     specialize (fooo (λ x:X, λ _,(let (equiv_inv, eisretr, eissect, _) := H (a x) (b x) in equiv_inv) *)
(*            (ap10 p x) )). *)
(*     simpl in fooo. *)
(*     specialize (fooo (λ Y, path_forall _ _ (λ x,  *)
(*     specialize (fooo φ). *)
(*     simpl in fooo. *)
(*     assert (∀ x : X, *)
(*           (let (equiv_inv, eisretr, eissect, _) := H (a x) (b x) in equiv_inv) *)
(*             (ap10 p x) = apD10 (φ p) x). *)
(*     intro x. unfold φ. simpl. *)
(*     unfold path_forall. *)
(*     rewrite eisretr. exact idpath. *)
(*     specialize (fooo X0). clear X0. *)
(*     unfold φ, equiv_inv in fooo. *)
(*     rewrite fooo; unfold φ. *)
    
      
(*     admit. *)
(*   - intro p; destruct p. simpl. *)
(*     unfold φ. *)
(*     simpl. *)
(*     pose (foo := path_forall _ _ (fun y =>  (@eissect _ _ _ (H (a y) (a y)) idpath))). *)
(*     simpl in foo. *)
(*     rewrite foo. *)
(*     rewrite path_forall_1. exact 1. *)
(* Qed. *)

Definition IsMonof_isMono (A B : Type) (f : A -> B) : IsMonof f = IsMono f.
  apply univalence_hprop.
  apply @trunc_forall. exact equal_f_equiv. intro a.
  apply @trunc_forall. exact equal_f_equiv. intro φ.
  apply @trunc_forall. exact equal_f_equiv. intro ψ.
  
  (* repeat (apply (@trunc_forall _ _ (fun P => _)); intro). *)
  apply hprop_isequiv.
  repeat (apply (@trunc_forall _ _ (fun P => _)); intro). apply hprop_isequiv.
  split.
  - intro H. intros x y.
    apply isequiv_adjointify with (g := λ p:(f x = f y), (ap10 (equiv_inv (IsEquiv := H B (fun _ => x) (fun _ => y)) (path_forall (λ _ : B, f x) (λ _ : B, f y) (fun _ => p))) (f x))).
    + intro u. unfold equiv_inv. destruct (H B (fun _ => x) (fun _ => y)). unfold compose, Sect in *; simpl in *.
      admit.
    + intro v.  destruct (H B (fun _ => x) (fun _ => y)). unfold compose, Sect in *; simpl in *. simpl in *.
      admit.
  - intro H. intros X x y.
    apply isequiv_adjointify with (g := λ p, path_forall _ _ (fun u => (equiv_inv (IsEquiv := H (x u) (y u)) (ap10 p u)))).
    + intro p. unfold ap10.
      admit.
    + intro p. destruct p. simpl. admit.
      
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
  forall (eq : f x = f y), eisretr (f x) @ eq @ (eisretr (f y))^ = ap f (ap equiv_inv eq).
Proof.
  intro.
  destruct eq. simpl. 
  rewrite concat_p1.
  hott_simpl.
Defined.

Lemma concat_ap2 (A B:Type) (f : A -> B) (x y: A) (equiv_inv : B -> A) (eisretr : Sect equiv_inv f) (eissect : Sect f equiv_inv) :
  forall eq, ap equiv_inv (ap f eq) = (eissect x) @ eq @ (eissect y)^.
Proof.
  intro.
  destruct eq.
  simpl. rewrite concat_p1.
  hott_simpl.
Qed.

Definition equiv_is_mono_f (A B:Type) (f: A -> B) (H :IsEquiv f) (x y : A) : f x = f y -> x = y. 
  intro X. destruct H as [equiv_inv eisretr eissect eisadj].
  pose (Y := ap equiv_inv X).
  pose (eq1 := eissect x); pose (eq2 := eissect y).
  exact (eq1^ @ Y @ eq2).
Defined.

Instance equiv_is_mono_eq (A B:Type) (f: A -> B) (H :IsEquiv f) (x y : A) : IsEquiv (ap (x:=x) (y:=y) f).
apply (isequiv_adjointify _ (equiv_is_mono_f _ x y)).
- destruct H as [equiv_inv eisretr eissect eisadj].
  intro z. unfold equiv_is_mono_f.
  assert  (ap f (((eissect x) ^ @ ap equiv_inv z) @ eissect y) = (eisretr (f x))^ @ (eisretr (f x)) @ ap f (((eissect x)^ @ ap equiv_inv z) @ eissect y) @ (eisretr (f y))^ @ (eisretr (f y))) by hott_simpl.
  rewrite X. clear X.
  assert ((eisretr (f x)) @ ap f (((eissect x) ^ @ ap equiv_inv z) @ eissect y) @ (eisretr (f y)) ^
          =
          (ap f (ap equiv_inv ( ap f ((eissect x)^ @ (ap equiv_inv z) @ (eissect y)))))).

  apply concat_ap.
  exact eissect.

  rewrite <- (concat_p_pp) with (p := (eisretr (f x)) ^) (q := eisretr (f x)) (r := ap f (((eissect x) ^ @ ap equiv_inv z) @ eissect y)).
  rewrite <- (concat_p_pp) with (p := (eisretr (f x)) ^) (q := (eisretr (f x) @ ap f (((eissect x) ^ @ ap equiv_inv z) @ eissect y))) (r := (eisretr (f y)) ^).
  
  rewrite X. clear X.
  
  assert ((ap equiv_inv (ap f (((eissect x) ^ @ ap equiv_inv z) @ eissect y))) = ap equiv_inv z).
  rewrite concat_ap2 with (eissect := eissect).
  hott_simpl.
  exact eisretr.

  rewrite X. clear X.

  rewrite <- concat_ap with (eisretr := eisretr).

  hott_simpl.
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
  intro e. apply eq_dep_subset. intro. apply hprop_trunc. exact e.
Defined.

Arguments equiv_path A B p : simpl never.

Definition isequiv_truncn_unique n (A B : Trunc n)
: IsEquiv (truncn_unique A B).
  unfold truncn_unique.
  apply isequiv_adjointify with (g := ap pr1).
  - intro p; simpl.
    destruct p; simpl. unfold truncn_unique. simpl.
    destruct A as [A TrA]. simpl.
    apply (transport (λ U, path_sigma' (λ T, IsTrunc n T) 1 U = 1) (@contr (TrA = TrA) ((trunc_trunc A n minus_two TrA TrA)) 1)^).
    exact 1.
  - intro p; unfold truncn_unique; simpl.
    destruct A as [A TrA], B as [B TrB]. simpl in p. destruct p. simpl.
    assert (fo := allpath_hprop TrA TrB). destruct fo.
    unfold allpath_hprop.
    apply (transport (λ U, ap pr1 (path_sigma' (λ T : Type, IsTrunc n T) 1 U) = 1) (@contr (TrA = TrA) ((trunc_trunc A n minus_two TrA TrA)) 1)^).
    exact idpath.   
Defined.

    
(* Lemma fooo    *)
(*       (A : Type) *)
(*       (B : Type) *)
(*       (f : A → B) *)
(*       (x : A) *)
(*       (y : A) *)
(*       (* q : f y = f x *) *)
(*       (* X : (x; 1) = (y; q) *) *)
(*       (* foo := X ..2 : transport (λ u : A, f u = f x) X ..1 1 = q *) *)
(*       (X: x=y) *)
(* (* ============================ *) *)
(* : (ap f X^) = transport (λ u : A, f u = f x) X 1. *)
(*     by induction X. *)
(* Qed. *)

(* Lemma L425 (A B:Type) (f:A -> B) (b:B) (x y : A) (p: f x = b) (q: f y = b) *)
(* : ((x;p)= existT (fun u => f u = b) y q) <~> { Ɣ :x=y & (ap f Ɣ)^@ p = q}. *)
(*   assert (((x; p) = existT (fun u => f u = b) y q) -> (∃ Ɣ : x = y, ((ap f Ɣ)^@ p)%type = q)). *)
(*     destruct p. *)
(*     intro X. exists X..1. *)
(*     pose (foo:= (X^..2)). simpl in *. hott_simpl. rewrite <- (inverse_ap). *)
(*     (* unfold ap. unfold transport in foo. simpl in foo. *) *)
(*     etransitivity; try exact foo. apply fooo. *)


Lemma IsMono_IsHProp_fibers_center (A B:Type) (f:A->B) (H: IsMono f) (b:B) (x y:A) (p:f x = b) (q:f y = b)
: (existT _ x p = existT (fun u => f u = b) y q).
  (* pose (r := @equiv_inv _ _ _ (H x y) (p@q^)). *)
  (* apply @path_sigma' with (p:=r). *)
  (* assert (X : ap f r = p@q^). unfold r; rewrite eisretr; exact idpath. *)
  (* assert (foo := moveR_Vp _ _ _ X). simpl in *. *)
  (* assert ((ap f r)^@ p = q). admit. *)
  (* hott_simpl. *)
  (* etransitivity. Focus 2. exact X0. *)
  (* destruct p. hott_simpl. *)
  (* symmetry. apply fooo. *)
Admitted.

Lemma IsMono_IsHProp_fibers (A B:Type) (f:A->B) : IsMono f -> forall b:B, IsHProp (hfiber f b).
  (* intros H b x y; simpl. *)
  (* destruct x as [x p], y as [y q]. *)

  (* exists (IsMono_IsHProp_fibers_center H x y p q). *)

  (* intro z. unfold IsMono_IsHProp_fibers_center. *)
  (* simpl. hott_simpl. simpl.  *)
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
                           (eq_dep_subset BProp (x;b) (x0;b0))). 
- intro. unfold eq_dep_subset; simpl in *. destruct x1. 
  apply (projT1_path_sigma (P:=B) (u:=(x;b)) (v:=(x;b0)) idpath (center (b = b0))). 
- intro. unfold eq_dep_subset, path_sigma'; simpl in *. 
  pose (foo := eta_path_sigma x1). etransitivity; try exact foo. 
  apply ap. destruct (@HProp_contr A B BProp x x0 b b0 x1..1).
  etransitivity; try apply contr. symmetry. apply contr.
Defined.

Definition elim_E A B (f:A->B) (H:IsEquiv f) (x y : A) (p : f x = f y)
: x = y :=
  (eissect f x)^ @ @moveR_E _ _ (f ^-1) isequiv_inverse _ _ p.


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


Lemma isequiv_ap10 : forall (A B: Type) f g, IsEquiv (@ap10 A B f g).
  intros A B f g.
  apply isequiv_apD10.
Defined.

Lemma equal_equiv (A B:Type) (f g : A -> B) (eq_f : IsEquiv f) (eq_g : IsEquiv g)
: f = g -> (BuildEquiv _ _ f eq_f) = (BuildEquiv _ _ g eq_g).
  intro H. destruct H. assert (eq_f = eq_g).
  apply allpath_hprop. destruct X. exact 1.
Qed.

Lemma equal_inverse A (a b:A)
: (a=b) = (b=a).
  apply univalence_axiom.
  exists inverse.
  apply @isequiv_adjointify with (g := inverse);
    intro u; destruct u; exact 1.
Defined.

Definition equiv_VV (A B:Type) (f:A -> B) (H:IsEquiv f)
: (f ^-1) ^-1 = f.
  hott_simpl.
Defined.

Definition moveR_EV (A B:Type) (f:A -> B) (IsEquiv:IsEquiv f) a b
: a = f b -> (f ^-1) a = b.
  intro p.
  apply moveR_E. rewrite equiv_VV. exact p.
Defined.


Lemma equal_equiv_inv (A B:Type) (f g: Equiv A B)
: f=g -> equiv_fun A B f = equiv_fun A B g.
  intro H. destruct H.
  exact 1.
Qed.
  