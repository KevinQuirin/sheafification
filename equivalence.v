Require Export Utf8_core.
Require Import HoTT.
Require Import univalence.
Require Import lemmas epi_mono.

Set Universe Polymorphism.
Set Implicit Arguments.

Local Open Scope path_scope.
Local Open Scope equiv_scope.


Section Things.

Context `{ua: Univalence}.
Context `{fs: Funext}.

Definition S_le n : (n <= trunc_S n)%trunc.
  induction n. exact tt. exact IHn. Defined.

Definition Trunk (n:trunc_index) := {T:Type & IsTrunc n T}.

Definition HProp := Trunk -1.

Lemma IsEquiv_unique : forall (A B:Type), forall (h : A -> B), forall (f g : IsEquiv h), f=g.
Proof.
  intros.
  apply path_ishprop.
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
  
Instance Tn_is_TSn : forall n, IsTrunc (trunc_S n) (Trunk n). (* Cf HoTT *)
intro n.
assert (Trunk n = TruncType n).
apply path_universe_uncurried. apply issig_trunctype.
symmetry in X. destruct X.
apply istrunc_trunctype.
Admitted.

Definition truncn_unique n (A B : Trunk n) : A.1 = B.1 -> A = B.
  intro e. apply eq_dep_subset. intro. apply hprop_trunc. exact e.
Defined.

Arguments equiv_path A B p : simpl never.

Definition isequiv_truncn_unique n (A B : Trunk n)
: IsEquiv (truncn_unique A B).
  unfold truncn_unique.
  apply isequiv_adjointify with (g := ap pr1).
  - intro p; simpl.
    destruct p; simpl. unfold truncn_unique. simpl.
    destruct A as [A TrA]. simpl.
    apply (transport (λ U, path_sigma' (λ T, IsTrunc n T) 1 U = 1) (@contr (TrA = TrA) _ 1)^).
    reflexivity.
  - intro p; unfold truncn_unique; simpl.
    destruct A as [A TrA], B as [B TrB]. simpl in p. destruct p. simpl.
    assert (fo := path_ishprop TrA TrB). destruct fo.
    unfold path_ishprop.
    apply (transport (λ U, ap pr1 (path_sigma' (λ T : Type, IsTrunc n T) 1 U) = 1) (@contr (TrA = TrA) _ 1)^).
    reflexivity.   
Defined.

Definition HProp_contr A (B : A -> Type) (BProp : forall a, IsHProp (B a)) (a a' : A )
           (b : B a) (b' : B a') (e : a = a') : 
  Contr (e # b = b').
  destruct e.
  destruct (BProp a b b').
  apply BuildContr with (center := center).
  intro. apply (@path2_contr _ (contr_inhabited_hprop (B a) b) b b').
Defined.

Instance subset_is_subobject A (B : A -> Type) (BProp : forall a, IsHProp (B a)) x y : 
  IsEquiv (ap (@pr1 A B) (x:=x) (y:=y)).
destruct x as [x b], y as [x0 b0].
apply  (isequiv_adjointify (ap (@pr1 A B) (x:=(x;b)) (y:=(x0;b0)))
                           (eq_dep_subset BProp (x;b) (x0;b0))). 
- intro. unfold eq_dep_subset; simpl in *. destruct x1.
  apply (pr1_path_sigma (P:=B) (u:=(x;b)) (v:=(x;b0)) 1 (center (b = b0))). 
- intro. unfold eq_dep_subset, path_sigma'; simpl in *. 
  pose (foo := eta_path_sigma x1). etransitivity; try exact foo. 
  apply ap. destruct (@HProp_contr A B BProp x x0 b b0 x1..1).
  etransitivity; try apply contr. symmetry. apply contr.
Defined.

Definition elim_E A B (f:A->B) (H:IsEquiv f) (x y : A) (p : f x = f y)
: x = y :=
  (eissect f x)^ @ @moveR_equiv_M _ _ (f ^-1) (isequiv_inverse _)_ _ p.


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



Lemma equal_equiv (A B:Type) (f g : A -> B) (eq_f : IsEquiv f) (eq_g : IsEquiv g)
: f = g -> (BuildEquiv _ _ f eq_f) = (BuildEquiv _ _ g eq_g).
  intro H. destruct H. assert (eq_f = eq_g).
  apply path_ishprop. destruct X. reflexivity.
Qed.

Lemma equal_inverse A (a b:A)
: (a=b) = (b=a).
  apply path_universe_uncurried.
  exists inverse.
  apply @isequiv_adjointify with (g := inverse);
    intro u; destruct u; reflexivity.
Defined.

Definition equiv_VV (A B:Type) (f:A -> B) (H:IsEquiv f)
: (f ^-1) ^-1 = f.
  hott_simpl.
Defined.

Definition moveR_EV (A B:Type) (f:A -> B) (IsEquiv:IsEquiv f) a b
: a = f b -> (f ^-1) a = b.
  intro p.
  apply moveR_equiv_M. rewrite equiv_VV. exact p.
Defined.


Lemma equal_equiv_inv (A B:Type) (f g: Equiv A B)
: f=g -> equiv_fun f = equiv_fun g.
  intro H. destruct H.
  reflexivity.
Qed.

Definition transport_path_universe_uncurried A B (f:A -> B) feq
: transport idmap (path_universe_uncurried (BuildEquiv _ _ f feq)) = f.
  assert (s := (eissect _ (IsEquiv := isequiv_path_universe (A:=A) (B:=B) ) (BuildEquiv _ _ f feq))).
  apply equal_equiv_inv in s.
  exact s.
Defined.

Lemma moveL_equiv_V  : forall (X Y:Type), forall (f: X -> Y), forall (H:IsEquiv f), forall (x:Y) (y:X), x = f y -> f^-1 x = y.
  intros X Y φ H u v HH.
  apply (@equiv_inj _ _ _ H).
  rewrite eisretr. exact HH.
Qed.


End Things.