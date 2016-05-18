Require Import Basics Types Diagram MyLemmas MyTacs.
Generalizable All Variables.

Context `{Funext}.

Section Cone.
  Record cone {G: graph} (D: diagram G) (X: Type) :=
    {q :> forall i, X -> D i;
     qq : forall (i j: G) (g: G i j), (D _f g) o (q i) == q j}.
  
  Global Arguments Build_cone {G D X} q qq.
  Global Arguments q {G D X} C i x : rename.
  Global Arguments qq {G D X} C i j g x : rename.

  
  Context {G: graph} {D: diagram G} {X:Type}.
  
  Definition path_cone_naive {C1 C2: cone D X}
           (P := λ q', forall {i j:G} (g: G i j), (D _f g) o (q' i) == q' j)
             (eq0 : q C1 = q C2)
             (eq1 : transport P eq0 (qq C1) = qq C2)
: C1 = C2 :=
             match eq1 in (_ = v1) return C1 = {|q := q C2; qq := v1 |} with
               | idpath =>
                 match eq0 in (_ = v0) return C1 = {|q := v0; qq := eq0 # (qq C1) |} with
                   | idpath => idpath
                 end
             end.

  Definition path_cone {C1 C2: cone D X}  
             (eq1 : forall i,  C1 i == C2 i)
             (eq2 : forall i j g x, qq C1 i j g x @ eq1 j x = ap (D _f g) (eq1 i x) @ qq C2 i j g x)
  : C1 = C2.
    destruct C1 as [q pp_q], C2 as [r pp_r].
    simple refine (path_cone_naive (path_forall (λ i, path_forall (eq1 i))) _). simpl.
    funext4 i j f x.
    unfold pointwise_paths.
    repeat rewrite transport_forall_constant.
    rewrite transport_paths_FlFr.
    rewrite concat_pp_p. apply moveR_Vp.
    rewrite (ap_ap2_path_forall _ _ q r eq1 j x).
    rewrite ap_compose.
    rewrite (ap_ap2_path_forall _ _ q r eq1 i _).
    apply eq2.
  Defined.

  Definition postcompose_cone (C: cone D X) {Y: Type} : (Y -> X) -> cone D Y.
    intros f.
    simple refine (Build_cone _ _).
    - intros i. exact ((C i) o f).
    - intros i j g x. exact (qq _ i j g (f x)).
  Defined.

  Definition is_universal (C: cone D X)
    := forall (Y: Type), IsEquiv (@postcompose_cone C Y).
End Cone.

Section IsColimit.
  Context {G: graph}.
  
  Record is_limit (D: diagram G) (Q: Type) :=
    {is_limit_C :> cone D Q;
     is_limit_H : is_universal is_limit_C}.

  Global Arguments Build_is_limit {D Q} C H : rename.
  Global Arguments is_limit_C {D Q} C : rename.
  Global Arguments is_limit_H {D Q} H X : rename.
  
  (* Definition is_colimit_H' (D: diagram G) `(H: is_colimit D Q) *)
  (* : forall (X: Type), IsEquiv (@postcompose_cocone _ _ _ (is_colimit_C H) X) := is_colimit_H H. *)

  (* Coercion is_colimit_H' : is_colimit >-> Funclass. *)
  
  Definition postcompose_cone_inv {D: diagram G} `(H: is_limit D Q) `(C: cone D X) : X -> Q
    := equiv_inv _ (IsEquiv := (is_limit_H H X)) C.
End IsColimit.


Section limit_sigma.
  Definition limit {G:graph} (D:diagram G)
    := {x: forall i:G, D i
                  & forall (i j:G) (f:G i j), (D _f f (x i)) = x j}.

  Definition cone_limit {G:graph} (D:diagram G) : cone D (limit D).
  Proof.
    simple refine (Build_cone _ _).
    - intros i x. exact (x.1 i).
    - intros i j g x; cbn. apply x.2.
  Defined.

  Definition is_limit_limit {G:graph} (D:diagram G)
    : is_limit D (limit D).
  Proof.
    simple refine (Build_is_limit (cone_limit D) _).
    intro Y.
    simple refine (isequiv_adjointify _ _ _).
    - intros C y.
      simple refine (exist _ _ _).
      intro i. exact (C i y).
      intros i j f; cbn. apply (qq C).
    - intro C.
      simple refine (path_cone _ _).
      + intros i x; reflexivity.
      + intros i j g x; cbn. simple refine (concat_p1 _ @ _).
        simple refine (concat_1p _)^.
    - intro f; reflexivity.
  Defined.
      
End limit_sigma.

Section FunctorialityCone.
  Context {G: graph}.

  (* postcompose *)
  Definition postcompose_cone_identity {D: diagram G} `(C: cone D X)
  : postcompose_cone C idmap = C.
    simple refine (path_cone _ _).
    intros i x; reflexivity.
    intros i j g x; simpl; hott_simpl.
  Defined.

  Definition postcompose_cone_comp  {D: diagram G} `(f: X -> Y) `(g: Y -> Z) (C: cone D Z)
  : postcompose_cone C (g o f) = postcompose_cone (postcompose_cone C g) f.
    simple refine (path_cone _ _).
    intros i x; reflexivity.
    intros i j h x; simpl; hott_simpl. 
  Defined.

  (* precompose *)
  Definition precompose_cone {D1 D2: diagram G} (m: diagram_map D1 D2) {X: Type}
  : (cone D1 X) -> (cone D2 X).
    intros C. simple refine (Build_cone _ _).
    intros i x. exact (m i (C i x)).
    intros i j g x; simpl.
    etransitivity; [apply diagram_map_comm |].
    apply ap.
    apply (qq C).
  Defined.

  Definition precompose_cone_identity (D: diagram G) (X: Type)
  : precompose_cone (X:=X) (diagram_idmap D) == idmap.
    intros C; simpl. simple refine (path_cone _ _).
    intros i x. reflexivity. intros; simpl. hott_simpl.
  Defined.

  Definition precompose_cone_comp {D1 D2 D3: diagram G} (m2: diagram_map D2 D3) (m1: diagram_map D1 D2) (X: Type):
     (precompose_cone (X:=X) m2) o (precompose_cone m1) == precompose_cone (diagram_comp m2 m1).
    intro C; simpl.
    simple refine (path_cone _ _).
    intros i x. reflexivity.
    intros i j g x. simpl. hott_simpl.
    unfold CommutativeSquares.comm_square_comp.
    rewrite !concat_pp_p. apply whiskerL.
    rewrite ap_pp. apply whiskerL.
    rewrite <- ap_compose. reflexivity.
  Defined.

  (* precompose and postcompose *)
  Definition precompose_postcompose_cone {D1 D2: diagram G} (m: diagram_map D1 D2) `(f: Y -> X) (C: cone D1 X)
  : postcompose_cone (precompose_cone m C) f = precompose_cone m (postcompose_cone C f).
    simple refine (path_cone _ _).
    - intros i x; reflexivity.
    - intros i j g x; simpl; hott_simpl.
  Defined.

  (* compose with equivalences *)
  Definition precompose_cone_equiv {D1 D2: diagram G} (m: D1 ≃ D2) (X: Type)
  : IsEquiv (precompose_cone (X:=X) m).
    simple refine (isequiv_adjointify (precompose_cone (diagram_equiv_inv m)) _ _).
    - intros C. etransitivity. apply precompose_cone_comp.
      rewrite diagram_inv_is_section. apply precompose_cone_identity.
    - intros C. etransitivity. apply precompose_cone_comp.
      rewrite diagram_inv_is_retraction. apply precompose_cone_identity.
  Defined.

  Definition postcompose_cone_equiv {D: diagram G} `(f: X <~> Y)
  : IsEquiv (λ C: cone D Y, postcompose_cone C f).
    simple refine (isequiv_adjointify _ _ _).
    - exact (λ C, postcompose_cone C f^-1).
    - intros C. etransitivity. symmetry. apply postcompose_cone_comp.
      etransitivity. 2:apply postcompose_cone_identity. apply ap.
      funext x; apply eissect.
    - intros C. etransitivity. symmetry. apply postcompose_cone_comp.
      etransitivity. 2:apply postcompose_cone_identity. apply ap.
      funext x; apply eisretr.
  Defined.

  (* universality preserved by equivalences *)
  Definition precompose_equiv_universality {D1 D2: diagram G} (m: D1 ≃ D2) `(C: cone D1 X)
  : is_universal C -> is_universal (precompose_cone (X:=X) m C).
    unfold is_universal.
    intros H Y.
    rewrite (path_forall (λ f, precompose_postcompose_cone m f C)).
    simple refine isequiv_compose. apply precompose_cone_equiv.
  Defined.

  Definition postcompose_equiv_universality {D: diagram G} `(f: X <~> Y) `(C: cone D Y)
  : is_universal C -> is_universal (postcompose_cone C f).
    unfold is_universal.
    intros H Z.
    pose (path_forall (λ g:Z -> X, postcompose_cone_comp g f C)).
    simple refine (isequiv_homotopic (λ g : Z → X, postcompose_cone C (f o g)) _).
    intro g. apply postcompose_cone_comp. 
  Defined.

  Definition precompose_equiv_is_colimit {D1 D2: diagram G} (m: D1 ≃ D2) {Q: Type}
  : is_limit D1 Q -> is_limit D2 Q.
    intros HQ. simple refine (Build_is_limit (precompose_cone m (is_limit_C HQ)) _).
    apply precompose_equiv_universality. apply HQ.
  Defined.

  Definition postcompose_equiv_is_colimit {D: diagram G} `(f: Q <~> Q')
  : is_limit D Q' -> is_limit D Q.
    intros HQ. simple refine (Build_is_limit (postcompose_cone HQ f) _).
    apply postcompose_equiv_universality. apply HQ.
  Defined.
End FunctorialityCone.


Section FunctorialityLimit.
  Context {G: graph}.
  
  Definition functoriality_limit {D1 D2: diagram G} (m: diagram_map D1 D2) `(HQ1: is_limit D1 Q1) `(HQ2: is_limit D2 Q2)
  : Q1 -> Q2
    := postcompose_cone_inv HQ2 (precompose_cone m (is_limit_C HQ1)).

  Definition functoriality_colimit_commute {D1 D2: diagram G} (m: diagram_map D1 D2) `(HQ1: is_limit D1 Q1) `(HQ2: is_limit D2 Q2)
  : forall i, (m i) o (q HQ1 i)  == (q HQ2 i) o (functoriality_limit m HQ1 HQ2) .
    intros i x.
    change (precompose_cone m HQ1 i x =
       postcompose_cone HQ2 (postcompose_cone_inv HQ2 (precompose_cone m HQ1)) i x). 
    f_ap. exact (eisretr (postcompose_cone HQ2) _)^.
  Defined.
  
  Context {D1 D2: diagram G} (m: D1 ≃ D2) `(HQ1: is_limit D1 Q1) `(HQ2: is_limit D2 Q2).
  
  Definition functoriality_limit_eissect
  : Sect (functoriality_limit (diagram_equiv_inv m) HQ2 HQ1) (functoriality_limit m HQ1 HQ2).
    unfold functoriality_limit. apply ap10.
    simple refine (equiv_inj (postcompose_cone HQ2) _). apply HQ2.
    etransitivity. 2:symmetry; apply postcompose_cone_identity.
    etransitivity. apply postcompose_cone_comp.
    unfold postcompose_cone_inv. rewrite eisretr.
    rewrite precompose_postcompose_cone. rewrite eisretr.
    rewrite precompose_cone_comp. rewrite diagram_inv_is_section.
    apply precompose_cone_identity.
  Defined.

  Definition functoriality_limit_eisretr
  : Sect (functoriality_limit m HQ1 HQ2) (functoriality_limit (diagram_equiv_inv m) HQ2 HQ1).
    unfold functoriality_limit.  apply ap10.
    simple refine (equiv_inj (postcompose_cone HQ1) _). apply HQ1.
    etransitivity. 2:symmetry; apply postcompose_cone_identity.
    etransitivity. apply postcompose_cone_comp.
    unfold postcompose_cone_inv. rewrite eisretr.
    rewrite precompose_postcompose_cone. rewrite eisretr.
    rewrite precompose_cone_comp. rewrite diagram_inv_is_retraction.
    apply precompose_cone_identity.
  Defined.

  Definition functoriality_limit_isequiv
  : IsEquiv (functoriality_limit m HQ1 HQ2)
    := isequiv_adjointify _ functoriality_limit_eissect functoriality_limit_eisretr.

  Definition functoriality_limit_equiv
  : Q1 <~> Q2
    := BuildEquiv functoriality_limit_isequiv.
End FunctorialityLimit.


Section LimitUnicity.
  Lemma limit_unicity {G: graph} {D: diagram G} {Q1 Q2: Type} (HQ1: is_limit D Q1) (HQ2: is_limit D Q2)
  : Q1 <~> Q2.
    simple refine (functoriality_limit_equiv _ HQ1 HQ2).
    simple refine (Build_diagram_equiv (diagram_idmap D) _).
  Defined.
End LimitUnicity.


(* Section TransportLimit. *)
(*   Context {G: graph} `(D: Y -> diagram G) {Q: Y -> Type} (HQ: forall y, is_limit (D y) (Q y)). *)

(*   Definition transport_limit {x y: Y} (p: x = y) (i: G) (u: D x i) *)
(*   : transport Q p (HQ x i u) = HQ y i (transport (λ y, D y i) p u). *)
(*     destruct p; reflexivity. *)
(*   Defined. *)
(* End TransportLimit. *)
    







  (*  *)