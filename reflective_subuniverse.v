Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import equivalence univalence sub_object_classifier epi_mono cech_nerve.

Set Universe Polymorphism.
Global Set Primitive Projections.
Set Implicit Arguments.

Definition Trunk (n:trunc_index) := @sig@{i' i} (Type2le@{i a}) (IsTrunc@{i} n) : Type@{i'}.
Definition HProp := Trunk -1.

Module Type subuniverse_struct.
  (* Definition 7.7.1 *)
  Parameter n0:trunc_index.

  Definition n := trunc_S n0.
  
  (* Parameter subu_family : Type2le@{u a}. *)
  Set Printing Universes.

  Parameter subu_family : Type2le@{u a}.
  (* Parameter sf : subu_family. *)
    
  Parameter subuniverse_HProp : forall (sf : subu_family@{u a}) (T:Trunk@{i' i a} n), HProp@{i' i a}.
  
  Parameter O : forall (sf : subu_family@{u a}), Trunk@{i' i a} n -> Trunk@{i' i a} n.

  Parameter subuniverse_O : forall (sf : subu_family@{u a}) (T:Trunk@{i' i a} n),
                                   (subuniverse_HProp@{u a i' i} sf (O@{u a i' i} sf T)).1.
  
  Parameter O_unit : forall (sf : subu_family@{u a}), forall T:Trunk@{i' i a} n, T.1 -> (O@{u a i' i} sf T).1.
  
  Parameter O_equiv : forall (sf : subu_family@{u a}), forall (P : Trunk@{i' i a} n) (Q : Trunk@{j' j a} n) (modQ : (subuniverse_HProp@{u a j' j} sf Q).1),
                        IsEquiv@{i j} (fun f : (O@{u a i' i} sf P).1 -> Q.1 => f o (O_unit@{u a i' i} sf P)).
  
End subuniverse_struct.

Module Reflective_Subuniverse (subU : subuniverse_struct).
  Export subU.

  (* Variable {n:trunc_index}. *)
  (* Generalizable Variables n. *)

  (* Variable subU : subuniverse_struct n. *)
  (* Variable (sf : subu_family@{u a}). *)
  (* Generalizable Variable sf. *)
  (* Definition sf := tt : subu_family.  *)
  
  Context `{ua: Univalence}.
  Context `{fs: Funext}.
  
  Definition subuniverse_Type (sf : subu_family) :=
    let S := subuniverse_HProp@{u a i' i} in {T : Trunk@{i' i a} n & pr1 (S sf T)}.

  Definition subuniverse_Type_is_TrunkSn (sf : subu_family) : IsTrunc@{u} (trunc_S n) (subuniverse_Type@{u a i' i} sf)
    :=
    @trunc_sigma@{i' i u u} _ (fun T => (subuniverse_HProp sf T) .1) _ (Tn_is_TSn@{i' i u} (n:=n))
           (fun T => IsHProp_IsTrunc (pr2 ((subuniverse_HProp) sf T)) n).

  Definition O_rec (sf : subu_family) (P Q : Trunk n) (modQ : (subuniverse_HProp@{u a i' i} sf Q).1) :
    (P.1 -> Q.1) -> ((O) sf P).1 -> Q.1 := 
    (@equiv_inv _ _ _ ((O_equiv sf) _ _ modQ)).

  Definition O_rec_retr (sf : subu_family) (P Q : Trunk n) (modQ : (subuniverse_HProp@{u a i' i} sf Q).1) f
   :=
    @eisretr _ _ _ ((O_equiv) sf P Q modQ) f.

  Definition O_rec_sect (sf : subu_family) (P Q : Trunk n) (modQ : (subuniverse_HProp@{u a i' i} sf Q).1) f :=
    @eissect _ _ _ ((O_equiv) sf P Q modQ) f.
  
  Definition O_rec_const (sf : subu_family) (P Q : Trunk n) (modQ : (subuniverse_HProp@{u a i' i} sf Q).1) y : O_rec sf P Q _ (λ _, y) = (λ _, y)
    := eissect _ (IsEquiv := O_equiv sf P Q modQ) (λ x, y).

  Lemma transport_O_rec (sf : subu_family) (P:Trunk n) (Q R:subuniverse_Type@{u a i' i} sf) (B:= λ S:subuniverse_Type sf, S.1.1) (eq : Q = R) f r:
    transport B eq (O_rec sf P Q.1 Q.2 f r) = O_rec sf P R.1 R.2 (λ v, transport B eq (f v)) r.
    destruct eq. simpl. reflexivity.
  Defined.
  
  Definition O_unit_retract_equiv (sf : subu_family) (T:Trunk n) (μ : ((O@{u a i' i} sf) T).1 -> T.1) (η := (O_unit) sf T) : Sect η μ -> IsEquiv η.
    unfold Sect; intros H. apply isequiv_adjointify with (g:=μ).
    - assert (η o μ o η = idmap o η).
      apply (ap (fun x => η o x)).
      apply path_forall; intro y.
      exact (H y).
      exact (apD10 (@equiv_inj _ _ _ ((O_equiv) sf T (O sf T) (subuniverse_O sf T)) (η o μ) idmap X)).
    - exact H.
  Defined.
    
  Instance O_modal_equiv (sf : subu_family) (P : subuniverse_Type@{u a i' i} sf) : IsEquiv ((O_unit) sf P.1).
  apply O_unit_retract_equiv with (μ := (O_rec sf P.1 P.1 P.2 idmap)).
  pose (f := O_rec_retr sf P.1 P.1 P.2 idmap). 
  intro. eapply apD10 in f. exact (f x).
  Defined.

  Definition unique_subuniverse (sf : subu_family) : forall (T T' : subuniverse_Type@{u a i' i} sf), pr1 T = pr1 T' -> T = T'. 
    intros. destruct T, T'. eapply (eq_dep_subset' (λ x, let (a, _) := subuniverse_HProp sf x in a) _ _ _ X). 
    Grab Existential Variables. intro. simpl. exact ((subuniverse_HProp sf a) .2).
  Defined.

  Definition isequiv_unique_subuniverse (sf : subu_family) (T T':subuniverse_Type@{u a i' i} sf)
  : IsEquiv (unique_subuniverse@{u a i' i} T T').
    apply isequiv_adjointify with (g := λ p, p..1).
     - intro p; destruct p.
      unfold unique_subuniverse; simpl.
      destruct T as [[T TrT] ShT]. simpl.
      unfold eq_dep_subset. simpl.
      apply (transport (λ U, path_sigma' (λ x : Trunk n, let (a, _) := subuniverse_HProp sf x in a) 1 U = 1) (@contr (ShT = ShT) ((subuniverse_HProp sf (T;TrT)).2 ShT ShT) 1)^).
      reflexivity.
    - intro p. unfold unique_subuniverse, eq_dep_subset. 
      destruct T as [T ShT], T' as [T' ShT']; simpl in *. destruct p.
      assert (ShT = ShT').
      apply @path_ishprop.
      exact (subuniverse_HProp sf T).2.
      destruct X.
      apply (transport (λ U, ap pr1
                                (path_sigma'
                                   (λ x : Trunk n, let (a, _) := subuniverse_HProp sf x in a) 1
                                   U) = 1) (@contr (ShT = ShT) ((subuniverse_HProp sf T).2 ShT ShT) 1)^).
      reflexivity.
  Defined.
      
  Definition O_modal (sf : subu_family) (T:subuniverse_Type@{u a i' i} sf) : T.1 = (O sf) T.1.
    apply truncn_unique.
    apply path_universe_uncurried.
    exact (BuildEquiv _ _ ((O_unit) sf (pr1 T)) (O_modal_equiv _)).
  Defined.

  Definition O_invol (sf : subu_family) : forall T:Trunk n, O@{u a i' i} sf (O sf T) = O sf T.
    intro T; symmetry. apply (O_modal (O sf T; subuniverse_O sf T)).
  Defined.

  Definition subuniverse_struct_transport (sf : subu_family) (T U:Trunk n) (f : (T.1 <~> U.1)%equiv) :
    ((subuniverse_HProp@{u a i' i} sf) T).1 -> ((subuniverse_HProp@{u a i' i} sf) U).1.
    apply path_universe_uncurried in f. apply truncn_unique in f. rewrite f.
    intro x; exact x.
  Defined.
  
  Definition subuniverse_iff_O (sf : subu_family) (T:Trunk n) : 
    IsEquiv (O_unit@{u a i' i} sf T) = pr1 ((subuniverse_HProp@{u a i' i} sf) T).
    apply univalence_hprop. apply hprop_isequiv. apply (pr2 ((subuniverse_HProp sf) T)).
    split.
    - exact (fun X => subuniverse_struct_transport sf _ _ (BuildEquiv _ _ _ (isequiv_inverse _ (feq:=X))) (((subuniverse_O sf) T))). 
    - exact (fun X => O_modal_equiv (T;X)).
  Defined.


(* ○-lift of functions *)
  
  Definition function_lift (sf : subu_family)  (A B : Trunk n) (f : A.1 -> B.1) :
    ((O@{u a i' i} sf) A).1 -> ((O@{u a i' i} sf) B).1.
    apply (O_rec sf A (O sf B) (subuniverse_O sf B)). intro x; apply (O_unit sf); apply f; exact x.
  Defined.

  Definition function_lift_modal (sf : subu_family)  (A:Trunk n) (B:Trunk n) (modB : (subuniverse_HProp@{u a i' i} sf B).1) (f : A.1 -> B.1) : (O@{u a i' i} sf A).1 -> B.1.
    apply O_rec. exact modB. exact f.
  Defined.

  Notation "'○' f" := (function_lift _ _ _ f) (at level 0).
  Notation "'○' f" := (function_lift_modal _ _ _ f) (at level 0).
  
  Lemma reflect_factoriality_pre (sf : subu_family)  
        (X:Trunk n)
        (Y Z : Trunk n)
        (modY : (subuniverse_HProp@{u a i' i} sf Y).1)
        (modZ : (subuniverse_HProp@{u a i' i} sf Z).1)
        (* (Y Z:subuniverse_Type) *)
        (g : Y.1 -> Z.1)
        (f : X.1 -> Y.1)
  : g o (O_rec@{u a i' i} sf X Y modY f) = O_rec@{u a i' i} sf X Z modZ (g o f).
  Proof.
    match goal with
      |[|- ?a = ?b] => pose (λ q, ap10 (@equiv_inj _ _ _ (O_equiv sf X Z modZ) a b q))
    end. simpl in p. 
    apply path_forall; intro x.
    
    refine (p _ x).
    apply path_forall; intro y.
    transitivity ((g o f) y).
    - apply (ap g).
      (* apply (ap (λ f, (g o f) y)). *)
      exact (ap10 (O_rec_retr sf X Y modY f) y). 
    - exact (ap10 (O_rec_retr sf X Z modZ (g o f))^ y).
  Defined.

  Lemma reflect_factoriality_post (sf : subu_family) 
        (X Y:Trunk n)
        (Z : Trunk n)
        (modZ : (subuniverse_HProp@{u a i' i} sf Z).1)
        (* (Z:subuniverse_Type) *)
        (g:Y.1 -> Z.1)
        (f:X.1 -> Y.1)
  : (O_rec@{u a i' i} sf Y Z modZ g) o (function_lift sf X Y f) = O_rec@{u a i' i} sf X Z modZ (g o f).
  Proof.
    transitivity (O_rec sf X Z modZ ((O_rec sf Y Z modZ g) o (O_unit sf Y o f))).
    - apply reflect_factoriality_pre.
    - apply ap.
      transitivity (((O_rec sf Y Z modZ g) o O_unit sf Y) o f).
      reflexivity.
      exact (ap (λ u, u o f) (O_rec_retr sf Y Z modZ g)).
  Defined.

  Lemma reflect_functoriality (sf : subu_family) 
        (X Y Z:Trunk n)
        (g:Y.1 -> Z.1)
        (f:X.1 -> Y.1)
  : (function_lift@{u a i' i} sf Y Z g) o (function_lift@{u a i' i} sf X Y f) = function_lift@{u a i' i} sf X Z (g o f).
    apply reflect_factoriality_post.
  Defined.

  Lemma O_rec_O_unit (sf : subu_family)  (A : subuniverse_Type@{u a i' i} sf) (B : Trunk n) (f : B.1 -> A.1.1) (x : (O@{u a i' i} sf B).1) :
    O_unit sf A.1 (O_rec sf B A.1 A.2 f x) = O_rec sf B (O sf A.1) (subuniverse_O sf A.1) ((O_unit sf A.1) o f) x.
    assert (O_rec sf B (O sf A .1) (subuniverse_O sf A.1) (O_unit sf A .1 o f) x = O_rec sf B (O sf A .1) (subuniverse_O sf A.1) ((O_unit sf A .1) o (O_rec sf B A.1 A.2 f) o (O_unit sf B)) x).
      pose (foo := O_rec_retr sf B A.1 A.2 f).
      apply (ap (fun u => O_rec sf B (O sf A.1) (subuniverse_O sf A.1) u x)).
      apply (ap (fun u => O_unit sf A.1 o u)).
      exact foo^.
    rewrite X; clear X.
    assert (forall U, O_rec sf B (O sf A .1) (subuniverse_O sf A.1) (U o O_unit sf B) x = U x).
      intro U.
      exact (apD10 (O_rec_sect sf B (O sf A.1) (subuniverse_O sf A.1) U) x).
    exact (inverse (X (O_unit sf A .1 o O_rec sf B A.1 A.2 f))).
  Defined.

  Definition function_lift_modal_square (sf : subu_family)  (A : Trunk n) (B : subuniverse_Type@{u a i' i} sf) (f : A.1 -> B.1.1) : (@equiv_inv _ _ ((O_unit) sf B.1) (O_modal_equiv B)) o (function_lift sf A B.1 f) o ((O_unit) sf A) =  f.
    apply path_forall; intro x; unfold function_lift; simpl.
    exact (transport (λ U, O_rec sf B .1 B.1 B.2 (λ x : (B .1) .1, x) U = f x) (inverse (apD10 ((O_rec_retr sf A ((O) sf B.1)) (subuniverse_O sf B.1) ((O_unit sf B.1) o f)) x)) (apD10 (O_rec_retr sf B.1 B.1 B.2 idmap) (f x))).
  Defined.

  Definition function_lift_compose (sf : subu_family) (A B C : Trunk n) ( f : A.1 -> B.1) (g : B.1 -> C.1) :
    (function_lift@{u a i' i} sf A C (g o f)) = (function_lift@{u a i' i} sf B C g) o (function_lift@{u a i' i} sf A B f).
    apply path_forall; intro x; simpl.
    unfold function_lift.
    (* fold ( (O_unit C) o g). *)
    (* fold ( (O_unit B) o f). *)
    (* assert ((λ x : A .1, O_unit C ((g ( f x)))) = ((((O_unit C) o g) o f))). *)
    (* reflexivity. *)
    (* rewrite X; clear X. *)
    
    assert (O_rec sf A (O sf C) (subuniverse_O sf C) (((O_unit sf C o g) o f)) = O_rec sf A (O sf C) (subuniverse_O sf C) (((O_rec sf B (O sf C) (subuniverse_O sf C) (O_unit sf C o g) o O_unit sf B) o f))).
    pose (foo := O_rec_retr sf B (O sf C) (subuniverse_O sf C) (O_unit sf C o g)).
    apply (transport (λ U, _ = O_rec sf _ _ _ (λ x0, U (f x0))) foo^).
    reflexivity.
    rewrite X; clear X.

    assert (O_rec sf A (O sf C)
     (subuniverse_O sf C) (O_rec sf B (O sf C) (subuniverse_O sf C) (O_unit sf C o g) o (O_unit sf B o f)) =
            O_rec sf A (O sf C)
     (subuniverse_O sf C) (O_rec sf B (O sf C) (subuniverse_O sf C) (O_unit sf C o g) o (O_rec sf A (O sf B) (subuniverse_O sf B) (O_unit sf B o f) o O_unit sf A))).
    pose (foo := O_rec_retr sf A (O sf B) (subuniverse_O sf B) (O_unit sf B o f)).
    apply (transport (λ U, _ = O_rec sf _ _ _ (λ x0, O_rec sf _ _ _ _ (U x0))) foo^).
    reflexivity.
      
    etransitivity. exact (ap10 X x).

    pose (foo := apD10 (O_rec_sect sf A (O sf C) (subuniverse_O sf C) (O_rec sf B (O sf C) (subuniverse_O sf C) (O_unit sf C o g)
       o O_rec sf A (O sf B) (subuniverse_O sf B) (O_unit sf B o f))) x).

    unfold O_rec, equiv_inv in *; simpl in *.
    rewrite foo.
    reflexivity.
  Defined.

  Definition function_lift_square (sf : subu_family) (A B C X : Trunk n) (π1 : X.1 -> A.1) (π2 : X.1 -> B.1) (f : A.1 -> C.1) (g : B.1 -> C.1) (comm : (f o π1) = (g o π2)) :
    (function_lift@{u a i' i} sf A C f) o (function_lift@{u a i' i} sf X A π1) =
    (function_lift@{u a i' i} sf B C g) o (function_lift@{u a i' i} sf X B π2).
    unfold function_lift in *; simpl in *.
    apply path_forall; intro x; simpl.

    pose (foo1 := apD10 (function_lift_compose sf X A C π1 f) x). unfold function_lift in foo1; simpl in foo1.
    pose (foo2 := apD10 (function_lift_compose sf X B C π2 g) x). unfold function_lift in foo2; simpl in foo2.
    pose (foo3 := ap (λ u, O_rec sf X (O sf C) (subuniverse_O sf C) (λ x0, O_unit sf C (u x0)) x) (x:=f o π1) (y:=g o π2) comm). simpl in foo3.

    exact ((inverse foo1) @ foo3 @ foo2).
  Defined.

  Definition function_lift_idmap (sf : subu_family) A : function_lift@{u a i' i} sf A A idmap = idmap
    := O_rec_sect@{u a i' i} sf A (O sf A) (subuniverse_O sf A) idmap.

  Lemma function_lift_equiv (sf : subu_family)  A B f 
  : IsEquiv f -> IsEquiv (function_lift@{u a i' i} sf A B f).
    intro H.
    eapply (isequiv_adjointify (function_lift sf A B f) (function_lift sf B A (@equiv_inv A.1 B.1 f H))).
    - intro x.
      etransitivity; try exact (ap10 (reflect_functoriality sf B A B f equiv_inv) x).
      etransitivity; try exact (ap10 (function_lift_idmap sf B) x).
      apply (ap (λ u, function_lift sf B B u x)).
      apply path_forall; intro.
      apply eisretr.
    - intro y.
      etransitivity; try exact (ap10 (reflect_functoriality sf A B A equiv_inv f) y).
      etransitivity; try exact (ap10 (function_lift_idmap sf A) y).
      apply (ap (λ u, function_lift sf A A u y)).
      apply path_forall; intro.
      apply eissect.
  Defined.

  Lemma function_lift_transport (sf : subu_family)  (A B:Trunk n) (p:A=B)
  : ((ap (O@{u a i' i} sf) p)..1) = (@path_universe _ (O@{u a i' i} sf A).1 (O sf B).1 (function_lift sf A B (transport idmap p..1)) (function_lift_equiv sf A B (f := (equiv_path A.1 B.1 p..1)) _)) .
    destruct p. simpl.
    unfold path_universe, path_universe_uncurried.
    apply (@equiv_inj _ _ _ (isequiv_equiv_path _ _)).
    rewrite eisretr. apply equal_equiv. simpl.
    apply path_forall; intro a. simpl.
    unfold function_lift. simpl.
    exact ((ap10 (O_rec_sect sf A (O sf A) _ idmap) a)^).
  Qed.

(* The universal property commute with η *)

  Definition equal_fun_modal (sf : subu_family) (A:Trunk n) (B:Trunk n) (modB : (subuniverse_HProp@{u a i' i} sf B).1) (f g:(O@{u a i' i} sf A).1 -> B.1) (η := O_unit@{u a i' i} sf A) : ((f o η = g o η) -> (f=g))
    := λ H, ((inverse (eissect _ (IsEquiv := (O_equiv sf A B modB)) f) @ (ap equiv_inv H) @ (eissect _ (IsEquiv := (O_equiv sf A B modB)) g))).

  Lemma universality_unit_lemma_lemma (oA A B: Type) (η : A -> oA) (f g : A -> B) (inv : (A -> B) -> oA -> B) (π : f = g) (eisretr : forall x:A -> B, (inv x) o η = x) (eissect : forall x : oA -> B, inv (x o η) = x) a
  : apD10 (ap inv π) (η a) = ((apD10 (eisretr f) a @ apD10 π a) @ (apD10 (eisretr g) a) ^)%path.
    destruct π.
    hott_simpl.
  Qed.
    
  Lemma universality_unit_lemma  (oA A: Type) (B:Type) (η : A -> oA) (f g : oA -> B) (inv : (A -> B) -> oA -> B) (π : f o η = g o η) (eisretr : forall x:A -> B, (inv x) o η = x) (eissect : forall x : oA -> B, inv (x o η) = x) a
  : apD10 (ap inv π) (η a) = ((apD10 (eisretr (f o η)) a @ apD10 π a) @ (apD10 (eisretr (g o η)) a) ^)%path.
    apply universality_unit_lemma_lemma.
    exact eissect.
  Defined.
      
  Definition universality_unit (sf : subu_family)  (A:Trunk n) (B:Trunk n) (modB : (subuniverse_HProp@{u a i' i} sf B).1) (f g:(O@{u a i' i} sf A).1 -> B.1)  (π : (f o O_unit@{u a i' i} sf A = g o O_unit@{u a i' i} sf A)) : forall a, apD10 (equal_fun_modal sf A B modB _ _ π) (O_unit sf A a) = apD10 π a.
    intro a. unfold equal_fun_modal.
    destruct (O_equiv sf A B modB) as [inv retr sect adj]. simpl.
    repeat rewrite apD10_pp. rewrite apD10_V. rewrite concat_pp_p.
    apply moveR_Mp. apply moveR_pM. rewrite inv_V.
    assert (apD10 (retr (g o O_unit sf A)) a = apD10 (sect g) (O_unit sf A a)).
    rewrite (adj g).
    apply (apD10_ap_precompose (O_unit sf A) (sect g)).
    rewrite <- X; clear X.
    assert (apD10 (retr (f o O_unit sf A)) a =
            apD10 (sect f) (O_unit sf A a)).
    rewrite (adj f).
    apply (apD10_ap_precompose (O_unit sf A) (sect f)).
    rewrite <- X. clear X. unfold Sect in *. 
    pose (universality_unit_lemma (O_unit sf A) f g inv π (λ x, path_forall _ _ (ap10 (retr x))) (λ x, path_forall _ _ (ap10 (sect x))) a).
    simpl in p.
    unfold path_forall in p. repeat rewrite eisretr in p. exact p.
  Defined.

(* Things *)

  Lemma O_rec_O_rec_dep_retr (sf : subu_family) 
        (A: Trunk n)
        (B: A.1 -> Trunk n)
        f g
        (H : forall a, f a (g a) = a)
  : O_rec@{u a i' i} sf A (O sf A) (subuniverse_O@{u a i' i} sf A) (λ x:A.1, O_rec@{u a i' i} sf (B x) (O@{u a i' i} sf A) (subuniverse_O sf A) (λ y, O_unit sf A (f x y)) (O_unit@{u a i' i} sf (B x) (g x))) = idmap.
    simpl.
    assert (X:forall x0 : A .1, (function_lift sf (B x0) A (f x0) (O_unit sf (B x0) (g x0)))  = (O_unit sf A x0)).
    intro a.
    etransitivity. exact (ap10 (O_rec_retr sf (B a) (O sf A) (subuniverse_O sf A) (λ x : (B a) .1, O_unit sf A (f a x))) (g a)).
    apply ap; apply H.
    transitivity (
        O_rec sf A (O sf A) (subuniverse_O sf A)
              (λ x0 : A .1,
                      (function_lift sf (B x0) A (f x0))
                        (O_unit sf (B x0) (g x0)))
      ).

    transitivity (O_rec sf A (O sf A) (subuniverse_O sf A) (λ x0 : A .1, O_unit sf A x0)).
    apply ap. apply path_forall; intro a; exact (X a).
    rewrite (path_forall _ _ X).
    reflexivity.
    rewrite (path_forall _ _ X).
    apply path_forall; intro x.
    exact (ap10 (O_rec_sect sf A (O sf A) (subuniverse_O sf A) idmap) x). 
  Qed.

  Lemma O_rec_O_rec_dep_sect (sf : subu_family) 
        (A: Trunk n)
        (B: A.1 -> Trunk n)
        f g
        (H : forall a, f a (g a) = a)
  : O_rec@{u a i' i} sf A (O sf A) (subuniverse_O sf A) (λ x:A.1, O_rec sf (B x) (O sf A) (subuniverse_O sf A) (λ y, O_unit sf A (f x (O_unit sf (B x) y))) (g x)) = idmap.
    simpl.
    transitivity (O_rec sf A (O sf A) (subuniverse_O sf A) (λ x : A .1, O_unit sf A x)).
    apply ap. apply path_forall; intro a.
    etransitivity; try exact (ap10 (O_rec_sect sf (B a) (O sf A) (subuniverse_O sf A) (λ u, O_unit sf A (f a u))) (g a)).
    apply ap. apply H.
    apply path_forall; intro x.
    exact (ap10 (O_rec_sect sf A (O sf A) (subuniverse_O sf A) idmap) x).
  Qed.

  Lemma O_rec_O_rec (sf : subu_family)  (A B C : Trunk n) f g x (H : forall b c, (f (g b c) c) = b)
  : O_rec@{u a i' i} sf A
          (O sf B)
          (subuniverse_O sf B)
          (λ u:A.1, O_rec sf C
                          (O sf B)
                          (subuniverse_O sf B)
                          (λ v:C.1, O_unit sf B (f u v))
                          x)
          o (O_rec sf B
                   (O sf A)
                   (subuniverse_O sf A)
                   (λ u:B.1, O_rec sf C
                                   (O sf A)
                                   (subuniverse_O sf A)
                                   (λ v:C.1, O_unit sf A (g u v))
                                   x)
            ) = idmap.

    match goal with
      |[|- ?a = ?b] => 
       assert (p := λ p, ap10 (equal_fun_modal sf B (O sf B) (subuniverse_O sf B) a b p))
    end.
    apply path_forall; intro u.
    refine ((p _) u).
    apply path_forall; intro b.

    pose (eq := ap10 (O_rec_retr sf B (O sf A) (subuniverse_O sf A) (λ u : B .1, O_rec sf C (O sf A) (subuniverse_O sf A) (λ v : C .1, O_unit sf A (g u v)) x)) b); simpl in eq.
    simpl in *.
    unfold O_rec.
    rewrite eq; clear eq.

    pose (eq := ap10 (reflect_factoriality_post sf C A (O sf B) (subuniverse_O sf B) (λ u : A .1, O_rec sf C (O sf B) (subuniverse_O sf B) (λ v : C .1, O_unit sf B (f u v)) x) (g b)) x); unfold  function_lift in eq; simpl in eq.
    unfold O_rec in eq. rewrite eq; clear eq.

    assert ((λ x, 
            O_rec sf C (O sf B) (subuniverse_O sf B)
                  (λ x0 : C .1,
                          O_rec sf C (O sf B) (subuniverse_O sf B) (λ v : C .1, O_unit sf B (f (g b x0) v)) x) x) = (λ _, O_unit sf B b)).

    apply (@equiv_inj _ _ _ (O_equiv sf C (O sf B) (subuniverse_O sf B))).
    simpl.
    apply path_forall; intro c.
    pose (foo := ap10 (O_rec_retr sf C (O sf B) (subuniverse_O sf B) (λ x1 : C .1,
       O_rec sf C (O sf B) (subuniverse_O sf B) (λ v : C .1, O_unit sf B (f (g b x1) v))
         (O_unit sf C c))) c).
    simpl in foo. unfold O_rec. rewrite foo; clear foo.
    pose (foo := ap10 (O_rec_retr sf C (O sf B) (subuniverse_O sf B) (λ v : C .1, O_unit sf B (f (g b c) v))) c).
    simpl in foo. unfold O_rec. rewrite foo; clear foo.
    apply ap. exact (H b c).
    
    exact (ap10 X x).
  Qed.

  Lemma equiv_nj_inverse (sf : subu_family) A a b
  : (O@{u a i' i} sf (a=b ; istrunc_paths (H:=A.2) A.1 n a b)).1 = (O sf (b=a ; istrunc_paths (H:=A.2) A.1 n b a)).1.
    repeat apply (ap pr1). apply ap.
    apply truncn_unique.
    exact (equal_inverse a b).
  Defined.

(* Dependent product and arrows *)
  Definition subuniverse_forall (sf : subu_family) (A:Trunk@{i' i a} n) (B:A.1 -> Trunk n) : (* Theorem 7.7.2 *)
    (forall x, ((subuniverse_HProp@{u a i' i} sf) (B x)).1) -> (((subuniverse_HProp@{u a i' i} sf)) (forall x:A.1, (B x).1 ; trunc_forall (H0 := λ x, (B x).2))).1.
    intro H.
    pose (ev := λ x, (λ (f:(forall x, (B x).1)), f x)).
    pose (ζ := λ x:A.1, O_rec sf (∀ x0 : A.1, (B x0) .1; trunc_forall (H0 := λ x, (B x).2)) (B x) (H x) (ev x)).
    pose (h := λ z, λ x, ζ x z).
    simpl in *.
    rewrite <- (subuniverse_iff_O).
    set (η := (O_unit sf (∀ x : A.1, (B x) .1; trunc_forall (H0 := λ a, (B a).2)))).
    apply O_unit_retract_equiv with (μ := h).
    intro φ.
    unfold h, ζ, ev; clear h; clear ζ; clear ev.
    apply path_forall; intro x.
    pose (foo := @O_rec_retr sf (∀ x0 : A.1, (B x0) .1; trunc_forall (H0 := λ x, (B x).2)) (B x) (H x) (λ f : ∀ x0 : A.1, (B x0) .1, f x)).
    exact (apD10 foo φ).
  Defined.

  Definition subuniverse_arrow (sf : subu_family) (A : Trunk@{i' i a} n) (B : subuniverse_Type@{u a i' i} sf) :
    (subuniverse_HProp@{u a i' i} sf (A.1 -> B.1.1 ; trunc_arrow (H0 := B.1.2))).1.
    apply subuniverse_forall.
    intro a. exact B.2.
  Defined.

(* Product *)
  Definition subuniverse_product (sf : subu_family) (A B : Trunk n) (modA : (subuniverse_HProp@{u a i' i} sf A).1) (modB : (subuniverse_HProp@{u a i' i} sf B).1) :
    (subuniverse_HProp@{u a i' i} sf (A.1*B.1 ; trunc_prod (H:=A.2) (H0 := B.2))).1.
    rewrite <- subuniverse_iff_O.

    pose (μ := λ (X : ((O sf (A.1 * B.1; trunc_prod (H:=A.2) (H0 := B.2))) .1) ),
               (O_rec sf (A.1 * B.1; trunc_prod (H:=A.2) (H0 := B.2)) A modA
                      (λ x : (A.1 * B.1; trunc_prod (H:=A.2) (H0 := B.2)) .1, (fst x)) X,
                O_rec sf (A.1 * B.1; trunc_prod (H:=A.2) (H0 := B.2)) B modB
                      (λ x : (A.1 * B.1; trunc_prod (H:=A.2) (H0 := B.2)) .1, (snd x)) X)).
    apply (O_unit_retract_equiv  (μ := μ)).
    intro x; destruct x as [a b].
    unfold μ; apply path_prod.
    - simpl.
      exact (apD10 (O_rec_retr sf (A.1 * B.1; trunc_prod (H:=A.2) (H0 := B.2)) A modA (λ x : A.1 * B.1, fst x)) (a,b)). 
    - simpl.
      exact (apD10 (O_rec_retr sf (A.1 * B.1; trunc_prod (H:=A.2) (H0 := B.2)) B modB (λ x : A.1 * B.1, snd x)) (a,b)). 
  Defined.
  
  Definition subuniverse_product_fun (sf : subu_family) (A B : Trunk n) : (O@{u a i' i} sf (A.1*B.1; trunc_prod (H:=A.2) (H0:=B.2))).1 -> (O@{u a i' i} sf A).1*(O sf B).1
    := function_lift_modal sf
         (A.1*B.1; trunc_prod (H:=A.2) (H0:=B.2))
         (((O sf A).1*(O sf B).1 ; trunc_prod (H := (O sf A).2) (H0 := (O sf B).2)))
         (subuniverse_product sf (O sf A) (O sf B) (subuniverse_O sf A) (subuniverse_O sf B))
         (λ x, (O_unit sf A (fst x), O_unit sf B (snd x))).

  Definition subuniverse_product_inv (sf : subu_family) (A B : Trunk n) : (O@{u a i' i} sf A).1*(O@{u a i' i} sf B).1 -> (O sf (A.1*B.1 ; trunc_prod (H:=A.2) (H0:=B.2))).1.
    intro x. destruct x as [p p0].
    generalize dependent p; apply O_rec; [apply subuniverse_O | intro p].
    generalize dependent p0; apply O_rec; [apply subuniverse_O | intro p0].
    apply (O_unit).
    exact (p,p0).
  Defined.

  Definition product_universal (sf : subu_family) (A B C : Trunk n) (modC : (subuniverse_HProp@{u a i' i} sf C).1) :
    Equiv (A.1 * B.1 -> C.1) ((O@{u a i' i} sf A).1*(O@{u a i' i} sf B).1 -> C.1).
    apply (@equiv_compose' _ (A.1 -> B.1 -> C.1) _).
    Focus 2.
    exists (λ f, λ u v, f (u,v)).
    refine (@isequiv_adjointify _ _ _ (λ u, λ x, u (fst x) (snd x)) _ _).
    intro x. apply path_forall; intro u; apply path_forall; intro v. reflexivity.
    intro x. apply path_forall; intro u. apply (transport (λ U, x U = x u) (eta_prod u)). reflexivity.

    apply (@equiv_compose' _ ((O sf A).1 -> B.1 -> C.1) _).
    Focus 2. apply equiv_inverse.
    exists (λ f : (((O sf A)) .1 -> (existT (λ S, (subuniverse_HProp sf S).1) (existT (λ T, IsTrunc n T) (B .1 -> (C .1)) (trunc_arrow (H0 := C.2))) (subuniverse_arrow B (C;modC))).1.1), 
                  f o O_unit sf A).
    exact (O_equiv sf A (( B.1 -> C.1 ; trunc_arrow (H0 := C.2))) (subuniverse_arrow B (C;modC))).
    
    apply (@equiv_compose' _ ((O sf A).1 -> (O sf B).1 -> C.1) _).
    exists (λ f:(((O sf A)).1 → ((O sf B)).1 → (C).1), λ u, f (fst u) (snd u)).
    apply isequiv_adjointify with (g := λ f, λ u v, f (u,v)).
    intro x. apply path_forall; intro u. rewrite (eta_prod u). reflexivity.
    intro x. apply path_forall; intro u. apply path_forall; intro v. reflexivity.

    apply equiv_postcompose'.
    apply equiv_inverse.
    exists (λ f : ((O sf B)) .1 -> (C) .1, f o O_unit sf B).
    exact (O_equiv sf B C modC).
  Defined.

  Definition product_universal' (sf : subu_family) (A B : Trunk n) (C : subuniverse_Type@{u a i' i} sf) :
    (A.1 * B.1 -> C.1.1) = ((O@{u a i' i} sf A).1*(O@{u a i' i} sf B).1 -> C.1.1):=
    path_universe_uncurried (product_universal sf A B C.1 C.2).

  Definition subuniverse_product' (sf : subu_family) (A B : Trunk n) (TrP : IsTrunc n (A.1*B.1)) : (O@{u a i' i} sf (A.1*B.1 ; TrP)).1 = ((O@{u a i' i} sf A).1*(O@{u a i' i} sf B).1).
    apply path_universe_uncurried.
    refine (equiv_adjointify _ _ _ _).
    - intros x.
      econstructor.
      revert x; apply O_rec; [apply subuniverse_O | intro x]; apply O_unit; exact (fst x).
      revert x; apply O_rec; [apply subuniverse_O | intro x]; apply O_unit; exact (snd x).
    - intros [x y].
      revert x; apply O_rec; [apply subuniverse_O | intro x].
      revert y; apply O_rec; [apply subuniverse_O | intro y].
      apply O_unit; exact (x,y).
    - intros [oa ob]. simpl.
      pose (s0 := ((((O sf A)).1 ∧ ((O sf B)).1); trunc_prod (H :=(O sf A).2) (H0 := (O sf B).2) )).
      pose (s := (s0 ; subuniverse_product sf (O sf A) (O sf B) (subuniverse_O sf A) (subuniverse_O sf B)) : subuniverse_Type sf).

      pose (p := λ (A:Trunk n) (f g : (O sf A).1 -> s.1.1) pp, ap10 (@equal_fun_modal sf A s.1 s.2 f g pp)).
      revert oa; refine (p _ _ _ _); apply path_forall; intro a.
      revert ob; refine (p _ _ _ _); apply path_forall; intro b.
      simpl.

      assert (rew := λ P Q modQ f, ap10 (O_rec_retr sf P Q modQ f)).
      simpl in rew.
      unfold O_rec.
      repeat rewrite rew. reflexivity.
    - simpl.
      pose (p := λ (X:Trunk n) (f g : (O sf X).1 -> (O sf (existT (IsTrunc n) (A.1 ∧ B.1) TrP)).1) pp, ap10 (@equal_fun_modal sf X (O sf (A.1 ∧ B.1; TrP)) (subuniverse_O sf _) f g pp)).
      refine (p _ _ _ _). apply path_forall.
      intros [a b]. simpl.
      assert (rew := λ P Q modQ f, ap10 (O_rec_retr sf P Q modQ f)).
      simpl in *.
      unfold O_rec.
      repeat rewrite rew. reflexivity.
  Defined.
  
  Lemma subuniverse_product_unit (sf : subu_family) (A B : Trunk n) (TrP : IsTrunc n (A.1*B.1))
  : forall x, ((equiv_path _ _ (subuniverse_product'@{u a i' i} sf A B TrP)) o (O_unit@{u a i' i} sf (A.1*B.1 ; TrP))) x =  (O_unit@{u a i' i} sf A (fst x), O_unit@{u a i' i} sf B (snd x)).
    intro x.
    simpl. unfold subuniverse_product'. unfold equiv_adjointify.
    rewrite transport_path_universe_uncurried.
    (* unfold compose; simpl. *)
    refine (path_prod _ _ _ _).
    - simpl.
      (* rewrite O_rec_retr. *)
      refine (@apD10 _ _ ( O_rec sf (A.1 ∧ B.1; TrP) (O sf A) (subuniverse_O sf A)
                                 (λ x0 : A.1 ∧ B.1, O_unit sf A (fst x0)) o (O_unit sf (A.1 ∧ B.1; TrP))) ((O_unit sf A) o fst) _ x).
      simpl.
      apply (O_rec_retr sf (A.1 ∧ B.1; TrP) (O sf A) (subuniverse_O sf A) (λ x0 : A.1 ∧ B.1, O_unit sf A (fst x0))).
    - simpl.
      refine (@apD10 _ _ ( O_rec sf (A.1 ∧ B.1; TrP) (O sf B) (subuniverse_O sf B)
                                 (λ x0 : A.1 ∧ B.1, O_unit sf B (snd x0)) o (O_unit sf (A.1 ∧ B.1; TrP))) ((O_unit sf B) o snd) _ x).
      apply O_rec_retr.
  Defined.
  
  (* Theorem 7.7.4 *)
  Definition subuniverse_sigma (sf : subu_family) :
    (forall (A:subuniverse_Type@{u a i' i} sf) (B:A.1.1 -> subuniverse_Type@{u a i' i} sf), (subuniverse_HProp@{u a i' i} sf ({x:A.1.1 & (B x).1.1} ; trunc_sigma (H:=A.1.2) (H0 := λ x, (B x).1.2))).1) <->
    (forall (A:Trunk n) (B: (O@{u a i' i} sf A).1 -> subuniverse_Type@{u a i' i} sf) (g : forall (a:A.1), (B (O_unit@{u a i' i} sf A a)).1.1), {f : forall (z:(O@{u a i' i} sf A).1), (B z).1.1 & forall a:A.1, f (O_unit@{u a i' i} sf A a) = g a}).
    split.
    - intro H. intros A B g.
      pose (Z := existT (λ T, (subuniverse_HProp sf T).1) ({z:(O sf A).1 & (B z).1.1} ; trunc_sigma (H:=(O sf A).2) (H0:=λ z, (B z).1.2)) (H ((O sf A); subuniverse_O sf A) B)).
      pose (g' :=( λ a:A.1, (O_unit sf A a ; g a)) : A.1 -> Z.1.1).
      pose (f' := O_rec sf _ _ Z.2 g'). unfold O_rec in f'.
      pose (eqf :=λ a:A.1, (apD10 (O_rec_retr sf _ _ Z.2 g') a)). fold f' in eqf.
      pose (g'' := λ x, (f' x).1).
      pose (f'' := λ x:(O sf A).1, x).
      pose (eq'' := path_forall _ _ (λ x, @ap _ _ pr1 _ _ (eqf x))).
      (* assert (g'' o (O_unit sf A) = f'' o (O_unit sf A)). *)
        (* exact eq''. *)
      pose (eq''' := apD10 (equal_fun_modal sf A (O sf A) (subuniverse_O sf A) (f'') (g'') eq''^)). unfold f'', g'' in eq'''; simpl in eq'''.
      pose (f := λ z, (f' z).2). simpl in f.
      set (η := O_unit sf A) in *.

      exists (λ z, transport (λ u, (B u).1.1) (eq''' z)^ (f z)).
      intro a.

      unfold f. unfold g' in eqf; simpl in eqf.
      pose (p := pr1_path (eqf a)^). simpl in p.
      pose (q := pr2_path (eqf a)^). simpl in q.

      rewrite <- q. 
      assert ( (eq''' (η a)) =  (eqf a)^ ..1).
        unfold eq''', pr1_path, eqf, q, p, f, eq''', eq'', f'', g'', eqf, f', g', Z, η in *; simpl in *.
        rewrite universality_unit. unfold path_forall.
        repeat rewrite apD10_V.
        rewrite (eisretr apD10).
        rewrite ap_V.
        reflexivity.
      rewrite X.
      rewrite transport_Vp. reflexivity.
    - intros H A B.
      pose (h := λ x, O_rec sf ({x:A.1.1 & (B x).1.1};trunc_sigma (H := A.1.2) (H0 := λ u, (B u).1.2)) A.1 A.2 pr1 x).
      pose (p := λ z, apD10 (O_rec_retr sf ({x : (A .1) .1 | ((B x) .1) .1}; trunc_sigma (H := A.1.2) (H0 := λ u, (B u).1.2)) A.1 A.2 pr1) z).
      pose (C := λ w, B(h w)).
      pose (g := λ z, (transport (λ u, (B u).1.1) (inverse (p z)) z.2)).
      simpl in *.
      specialize (H ({x:A.1.1 & (B x).1.1};trunc_sigma (H := A.1.2) (H0 := λ u, (B u).1.2)) C g).
      destruct H as [f q]. simpl in q.
      pose (k := (λ w, (h w; f w)) : (O sf ({x:A.1.1 & (B x).1.1};trunc_sigma (H := A.1.2) (H0 := λ u, (B u).1.2))).1 -> ({x:A.1.1 & (B x).1.1};trunc_sigma (H := A.1.2) (H0 := λ u, (B u).1.2)).1); simpl in k.

      rewrite <- subuniverse_iff_O.
      apply O_unit_retract_equiv with (μ := k).

      intro x; destruct x as [x1 x2]. unfold k.
      rewrite (q (x1;x2)).
      apply @path_sigma'  with (p := (p (x1;x2))).
      unfold g; simpl.
      rewrite transport_pV.
      reflexivity.
  Defined.
      
  Lemma subuniverse_unit (sf : subu_family) : ((subuniverse_HProp@{u a i' i} sf) (existT (λ T, IsTrunc n T) (Unit) (trunc_unit n))).1.
    rewrite <- subuniverse_iff_O.
    apply O_unit_retract_equiv with (μ := λ x:((O) sf (Unit;trunc_unit n)).1, tt).
    intro u.
    destruct u; reflexivity.
  Defined.

  Definition OUnit_is_Unit (sf : subu_family) : (((O@{u a i' i} sf (Unit; trunc_unit n)).1) = Unit)
    := ((O_modal ((((Unit; trunc_unit n) : Trunk n); subuniverse_unit sf) : subuniverse_Type sf))..1)^.

  (** Paths *)

  Definition subuniverse_paths (sf : subu_family) (A : subuniverse_Type@{u a i' i} sf)
  : forall x y:A.1.1, (subuniverse_HProp sf (x = y ; istrunc_paths _ n (H:= (trunc_succ (H := A.1.2))) _ _)).1.
  Admitted.

  (** Things' *)
  
  
  Lemma reflect_factoriality_arrow_space (sf : subu_family)
        (P:Trunk n)
        (Q R: subuniverse_Type@{u a i' i} sf)
        (f : P.1 -> (Q.1.1 -> R.1.1))
        (g : P.1 -> (R.1.1 -> Q.1.1))
        (S := ((Q.1.1 -> R.1.1; trunc_arrow (H0 := R.1.2)); subuniverse_arrow Q.1 R) : subuniverse_Type@{u a i' i} sf)
        (T := ((R.1.1 -> Q.1.1; trunc_arrow (H0 := Q.1.2)); subuniverse_arrow R.1 Q) : subuniverse_Type@{u a i' i} sf)
        (RR := ((R.1.1 -> R.1.1; trunc_arrow (H0 := R.1.2)); subuniverse_arrow R.1 R) : subuniverse_Type@{u a i' i} sf )
  : (λ v, (O_rec sf P S.1 S.2 f v) o (O_rec sf P T.1 T.2 g v)) = (λ v, O_rec sf P RR.1 RR.2 (λ v, (f v) o (g v)) v).
    simpl in *.
    pose (foo := @equiv_inj _ _ _ (O_equiv sf P RR.1 RR.2)).
    specialize (foo (λ w, O_rec sf P S.1 S.2 f w o O_rec sf P T.1 T.2 g w) (λ w, O_rec sf P RR.1 RR.2 (λ v : P .1, f v o g v) w)). simpl in foo.
    apply path_forall; intro x. simpl.
    refine (ap10 (foo _) x); clear foo.
    apply path_forall; intro v.  simpl.
    transitivity ((λ v : P .1, f v o g v) v).
    - apply path_forall; intro r; simpl.
      pose (foo := ap10 (O_rec_retr sf P S.1 S.2 f) v). simpl in foo.
      unfold O_rec. rewrite foo. simpl.
      apply ap.
      pose (bar := ap10 (O_rec_retr sf P T.1 T.2 g) v). simpl in bar.
      rewrite bar.
      reflexivity.
    - apply path_forall; intro r; simpl.
      pose (foo := ap10 (O_rec_retr sf P RR.1 RR.2 (λ (v0 : P .1) (x : (R .1) .1), f v0 (g v0 x))) v). simpl in foo.
      unfold O_rec; rewrite foo.
      reflexivity.
  Defined.

  
  Lemma transport_arrow_space (sf : subu_family)
        (P Q : subuniverse_Type@{u a i' i} sf)
        (p : P.1.1 = Q.1.1)
  : (λ x0:Q.1.1, (transport idmap p (transport idmap p^ x0))) = idmap.
    destruct p; reflexivity.
  Qed.

  Lemma transport_arrow_space_dep_path  (sf : subu_family)
        (P Q : subuniverse_Type@{u a i' i} sf)
        (R : Trunk@{i' i a} n)
        (p : R.1 -> P.1.1 = Q.1.1)
  : (λ v:R.1, λ x0:Q.1.1, (transport idmap (p v) (transport idmap (p v)^ x0))) = λ v, idmap.
    apply path_forall; intro v.
    apply transport_arrow_space.
  Qed.

  Lemma ap10_O_retr_sect (sf : subu_family) (P:Trunk n) (Q:subuniverse_Type@{u a i' i} sf) f x0
  : (ap10
       (O_rec_sect@{u a i' i} sf P Q.1 Q.2
                   f) (O_unit sf P x0)) =
    (ap10
       (O_rec_retr@{u a i' i} sf P Q.1 Q.2
                   (λ x1 : P.1, f (O_unit sf P x1))) x0).

    unfold O_rec_retr, O_rec_sect. simpl.
    pose (foo := O_equiv sf P Q.1 Q.2).
    pose (adj := eisadj _ (IsEquiv := foo)).
    specialize (adj f). simpl in adj. 

    transitivity (ap10 (ap
                      (λ (f : ((O sf P)) .1 → (Q .1) .1) (x : P .1), f (O_unit sf P x))
                      (eissect
                         (λ (f : ((O sf P)) .1 → (Q .1) .1) 
                            (x : P .1), f (O_unit sf P x)) f)) x0).

    pose (rew := @ap10_ap_precompose).  rewrite rew. reflexivity.
    apply (ap (λ u, ap10 u x0) (x:=(ap
                                      (λ (f0 : ((O sf P)) .1 → (Q .1) .1) (x : P .1), f0 (O_unit sf P x))
                                      (eissect
                                         (λ (f0 : ((O sf P)) .1 → (Q .1) .1) (x : P .1),
                                          f0 (O_unit sf P x)) f))) (y:=(eisretr
                                                                          (λ (f0 : ((O sf P)) .1 → (Q .1) .1) (x : P .1), f0 (O_unit sf P x))
                                                                          (λ x1 : P .1, f (O_unit sf P x1))))).
    exact adj^.
  Defined.

  Definition O_invol_ (sf : subu_family) : forall T:Trunk n, O@{u a i' i} sf T = O sf (O sf T)
    := λ T, (O_modal (O sf T; subuniverse_O sf T)).

  Lemma OO_unit_idmap (sf : subu_family) (T:Trunk n)
  : (O_unit@{u a i' i} sf (O sf T)) = equiv_path _ _ ((O_invol_ sf T)..1).
    unfold O_invol_. unfold O_modal.
    pose (rew := eissect _ (IsEquiv := isequiv_truncn_unique (O sf T) (O sf (O sf T))) (path_universe_uncurried
                                                                                                 {|
                                                                                                   equiv_fun := O_unit sf (O sf T);
                                                                                                   equiv_isequiv := O_modal_equiv ((O sf T); subuniverse_O sf _) |})). 
    simpl in rew. unfold pr1_path. rewrite rew; clear rew.
    unfold path_universe_uncurried. rewrite eisretr. simpl. reflexivity.
  Defined.

End Reflective_Subuniverse.