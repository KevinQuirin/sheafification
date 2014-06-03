Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import path equiv truncation univalence sub_object_classifier limit_colimit modalities.

Set Universe Polymorphism.
Global Set Primitive Projections.
Set Implicit Arguments.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

Definition HSet := Trunc 0.
Context {Fun : Funext}.   
Section Reflective_Subuniverse_base_case.

  Lemma j_sym_ (P:HSet) (a b:P.1) : (~~(a=b)) = (~~(b=a)).
    assert ((a=b)=(b=a)).
    apply univalence_axiom; exists (symmetric_paths a b); apply isequiv_adjointify with (g := symmetric_paths b a); [intro x; hott_simpl | intro x; hott_simpl].
    rewrite X; exact idpath.
  Qed.

  Lemma j_sym (P:HSet) (a b:P.1) : (~~(a=b)) -> ~~(b=a).
    intro x. intro A; apply x; intro B; apply A; exact (inverse B).
  Qed.
  
  Instance _j (P:HProp) : IsHProp (not (not (P.1))).
  repeat (apply trunc_forall; intro). Defined.

  Definition j (P:HProp) := (not (not (P.1));_j _).

  Instance _is_classical (P:HProp) : IsHProp ((j P).1 -> P.1).
  apply (@trunc_forall _ _ (fun _ => P.1)). intro. exact (P.2). Defined.  
  
  Definition is_classical (P:HProp) := ((j P).1 -> P.1 ; _is_classical (P:=P)).

  Definition Oj (P:HProp) : {P : HProp & (is_classical P).1}.
    exists (j P). exact (λ X X0, X (λ X1, X1 X0)). Defined.
    
  Definition Oj_unit (P:HProp) : P.1 -> (Oj P).1.1 := fun x k => k x.

  Definition Oj_equiv (P : Trunc minus_one) (Q : {T : Trunc minus_one & (is_classical T).1}) :
      (P.1 -> Q.1.1) -> (Oj P).1.1 -> Q.1.1.
    intros f jp. apply (Q.2). intro notQ. apply jp. intro p. exact (notQ (f p)). Defined.
  
  Definition subuniverse_Prop : subuniverse_struct minus_one.
  apply (Build_subuniverse_struct is_classical Oj Oj_unit). 
  intros. eapply log_equiv_is_equiv.
  apply (@trunc_forall _ _ (fun P => _)); intro. exact Q.1.2.
  apply (@trunc_forall _ _ (fun P => _)); intro. exact Q.1.2.
  exact (Oj_equiv _).
  Defined.  

End Reflective_Subuniverse_base_case.

(* induction step based on induction principle *)

Definition J :=
  (nchar_to_sub (pr1 (P:=_) o Oj)).1.
  (* {P : HProp & j (P.1)} *)

(* Definition True_is_irr (x y : Unit) : x = y. *)
(*   destruct x, y. reflexivity. Defined. *)

(* Instance true_ishprop : IsHProp Unit. *)
(* intros x y. apply BuildContr with (center := True_is_irr x y).  *)
(* intro e. destruct e, x. reflexivity. *)

Definition Oj_J_Contr (χ:J) : Contr ((j χ.1).1).
  apply BuildContr with (center := χ.2).
  intro. apply allpath_hprop.
Defined.

Section Sheafification_hset.

  Definition nj : subuniverse_struct minus_one := subuniverse_Prop.

  Variable j_is_nj : forall P, (j P).1 = (nj.(O) (P.1; IsHProp_IsTrunc P.2 minus_two)).1.1.

  Variable j_is_nj_unit : forall P x ,
             transport idmap (j_is_nj P) (Oj_unit P x) = nj.(O_unit) (P.1; IsHProp_IsTrunc P.2 minus_two) x.

  Definition E_to_χ_map (T:HSet) E (χ : E -> J) (f : E -> T.1) :
    (nchar_to_sub (pr1 o χ)).1 -> T.1 := f o pr1.

  Definition separated T :=  ∀ E (χ : E -> J), IsMono (E_to_χ_map T (E:=E) (χ:=χ)).
            
  Definition Snsheaf_struct T := ∀ E (χ : E -> J), IsEquiv (E_to_χ_map T (E:=E) (χ:=χ)). 

  Definition SnType_j_Type := {T : HSet & Snsheaf_struct T}.

  Definition separated_is_HProp T : IsHProp (separated T).
    repeat (apply (@trunc_forall Fun); intros).
    apply hprop_isequiv.
  Defined.

  Definition Snsheaf_struct_is_HProp T : IsHProp (Snsheaf_struct T).
    repeat (apply (@trunc_forall Fun); intro).
    apply hprop_isequiv.
  Defined.

  Definition nj_inter_f (A : HProp) (φ : A.1 -> HProp) : 
    (nj.(O) ({a:A.1 & (φ a).1}; trunc_sigma (H:= A.2) (H0 := fun a => (φ a).2))).1.1 ->
    (nj.(O) ({a:A.1 & (nj.(O) (φ a)).1.1}; trunc_sigma (H := A.2) (H0 := fun a => (nj.(O) (φ a)).1.2))).1.1.
    exact (function_lift
             nj
             ({a:A.1 & (φ a).1}; trunc_sigma (H:= A.2) (H0 := fun a => (φ a).2))
             ({a:A.1 & (nj.(O) (φ a)).1.1}; trunc_sigma (H := A.2) (H0 := fun a => (nj.(O) (φ a)).1.2))
             (λ X, (X.1;nj.(O_unit) _ X.2))).
  Defined.

  Definition nj_inter_g (A : HProp) (φ : A.1 -> HProp) : 
    (nj.(O) ({a:A.1 & (nj.(O) (φ a)).1.1}; trunc_sigma (H := A.2) (H0 := fun a => (nj.(O) (φ a)).1.2))).1.1 ->
    (nj.(O) ({a:A.1 & (φ a).1}; trunc_sigma (H:= A.2) (H0 := fun a => (φ a).2))).1.1.
    apply Oj_equiv. intro.
    generalize X.2. apply Oj_equiv; intro φa.
    apply Oj_unit. exact (X.1;φa).
  Defined.

  (* This remains to be proved *)

  Opaque trunc_sigma.

  Instance nj_inter_equiv (A : HProp) (φ : A.1 -> HProp) : IsEquiv (nj_inter_f A φ).
  apply (isequiv_adjointify _ (nj_inter_g A φ)).
  - intro x. unfold nj_inter_f, nj_inter_g, function_lift. simpl. 
    admit.
  - intro x. unfold nj_inter_f, nj_inter_g, function_lift. simpl.
    admit.
  Defined.

  Definition nj_inter (A : HProp) (φ : A.1 -> HProp) : 
    nj.(O) ({a:A.1 & (φ a).1}; trunc_sigma (H:= A.2) (H0 := fun a => (φ a).2)) =
    nj.(O) ({a:A.1 & (nj.(O) (φ a)).1.1}; trunc_sigma (H := A.2) (H0 := fun a => (nj.(O) (φ a)).1.2)).
    apply unique_subuniverse. apply truncn_unique.
    apply univalence_axiom. exact (BuildEquiv _ _ _ (nj_inter_equiv _ _)).
  Defined.

  Definition nj_fibers_composition A B C (f : A -> B) (g : B -> C) (c : C)
          (HB : ∀ b : B, IsHProp (hfiber f b)) (HC : ∀ c : C, IsHProp (hfiber g c))
  :
    nj.(O) (hfiber (g o f) c; function_trunc_compo minus_one f g HB HC c) =
    nj.(O) ({ w :  hfiber g c &  (nj.(O) (hfiber f (w.1);(HB (w.1)))).1.1};
            trunc_sigma (H0:=fun a => (O nj (hfiber f a .1; HB a .1)).1 .2)).
    assert ((hfiber (g o f) c; function_trunc_compo minus_one f g HB HC c) =
            ({ w : (hfiber g c) & hfiber f (w.1) }; trunc_sigma)).
    apply truncn_unique. apply fibers_composition.
    apply (transport (fun X => O nj X = _) (inverse X)). clear X.
    apply (nj_inter (hfiber g c; HC c) (fun w => (hfiber f w .1; HB w.1))).
  Defined.
    
  Definition type_j_f E (χ: E -> J) :
    (E -> subuniverse_Type nj) -> (nchar_to_sub (pr1 o χ)).1
    -> subuniverse_Type nj := λ α e, α (e.1).

  Definition type_j_inv E (χ: E -> J) : ((nchar_to_sub (pr1 o χ)).1 -> subuniverse_Type nj) -> E -> subuniverse_Type nj :=
  λ α e, let f := ((nchar_to_sub (pr1 o α)).2) in
         let m := ((nchar_to_sub (pr1 o χ)).2) in
         nj.(O) (nsub_to_char minus_one ({b : _ &  (α b).1.1}; ((m.1) o (f.1); function_trunc_compo minus_one (f.1) (m.1) (f.2) (fun e => IsHProp_IsTrunc (pr2 m e) minus_two))) e).

  Instance nTjTiSnTjT_eq E (χ : E -> J) : IsEquiv (λ (f : E -> subuniverse_Type nj) (t : {b : E &  (χ b).1.1}), f (t.1)). 
  apply (isequiv_adjointify _ (type_j_inv (E:=E) (χ := χ))).
  - intro φ.
    unfold type_j_inv, composition. simpl. unfold nchar_to_sub, hfiber, composition in φ; simpl in φ.
    apply path_forall; intro x.
    rewrite (O_modal (φ x)).
    repeat apply ap.
    apply truncn_unique.
    eapply concat; try exact (hfiber_pi1 ( (λ t : _, (φ t).1.1)) x).
    symmetry. apply (hfiber_mono (pr1 ) (g:=pr1 )).
    intros X Y. apply subset_is_subobject. intro.
    exact ((χ a).1.2).
  - intro φ.
    unfold type_j_inv, composition. simpl.
    apply path_forall; intro x.
    rewrite (O_modal (φ x)).
    unfold nsub_to_char. simpl.
    assert ((hfiber
        (λ t : {b : {b : E | ((χ b) .1) .1} | ((φ b .1) .1) .1}, (t .1) .1) x;
     function_trunc_compo minus_one pr1 pr1
       (nchar_to_sub_compat (λ t : {b : E | ((χ b) .1) .1}, (φ t .1) .1))
       (λ e : E,
        IsHProp_IsTrunc (nchar_to_sub_compat (λ t : E, (χ t) .1) e) minus_two) x) =
     (hfiber
        (λ t : {b : {b : E | ((φ b) .1) .1} | ((χ b .1) .1) .1}, (t .1) .1) x;
     function_trunc_compo minus_one pr1 pr1
       (λ e : _,
        IsHProp_IsTrunc (nchar_to_sub_compat (λ t : _, (χ (t.1)) .1) e) minus_two) 
       (nchar_to_sub_compat (λ t : E, (φ t) .1)) x)).
    apply truncn_unique. apply (inter_symm (fun b => ((χ b) .1) .1) (fun b => ((φ b) .1) .1)).
    apply (transport (fun x => O nj x = _ ) (inverse X)). clear X.
    pose (X := (nj_fibers_composition x (λ e : {b : E | ((φ b) .1) .1},
        IsHProp_IsTrunc
          (nchar_to_sub_compat (λ t : {b : E | ((φ b) .1) .1}, (χ t .1) .1) e)
          minus_two) (nchar_to_sub_compat (λ t : E, (φ t) .1)))). unfold composition in X.
    assert (foo := (transport (fun y => y = (Oj (φ x) .1)) (inverse X))). 
    apply (transport (fun y => y = (Oj (φ x) .1)) (inverse X)). clear X.
  
    apply ap. apply truncn_unique. simpl. etransitivity.
    apply univalence_axiom. apply equiv_sigma_contr.
    intro. pose (f := j_is_nj (hfiber pr1 a .1;
           (nchar_to_sub_compat (λ t : {b : E | ((φ b) .1) .1}, (χ t .1) .1)
              a .1))).
    apply (transport (fun X => Contr X) f).
    simpl.
    apply (transport (fun X => Contr (not (not X))) (inverse (nhfiber_pi1 _ _))).
    apply Oj_J_Contr.
    etransitivity. apply nhfiber_pi1. reflexivity.
  Defined.

  Definition nType_j_Type_is_SnType_j_Type : Snsheaf_struct (subuniverse_Type nj ;
                                                        @subuniverse_Type_is_TruncSn _ nj) :=
     λ E χ, nTjTiSnTjT_eq _.
  
  Definition nType_j_Type_sheaf : SnType_j_Type :=
    ((subuniverse_Type nj; @subuniverse_Type_is_TruncSn _ nj);nType_j_Type_is_SnType_j_Type).

  Instance dep_prod_SnType_j_Type_eq
          (A : Type)
          (B : A -> SnType_j_Type)
  : forall (E:Type) (χ : E -> J) (H := λ a, (((B a).2)) E χ), IsEquiv
      (λ (f : E -> ∀ a : A, (B a).1.1) (t : {b : E & (χ b).1.1}), f (t.1)).
  intros.   
  apply (isequiv_adjointify 
           _ (λ g e a, (@equiv_inv _ _ _ (H a) (λ x, g x a) e))).
  - intro φ.
    apply path_forall; intro x.
    apply path_forall; intro a.
    destruct (H a); simpl in *.
    clear eisadj; clear eissect.
    unfold nchar_to_sub, composition in equiv_inv; simpl.
    unfold Sect, nchar_to_sub, composition, E_to_χ_map, composition in eisretr.
    specialize (eisretr (λ x, φ x a)).
    exact (equal_f _ eisretr x).
  - intro φ.
    apply path_forall; intro x.
    apply path_forall; intro a.
    destruct (H a); simpl in *.
    clear eisadj; clear eisretr.
    unfold nchar_to_sub, composition in equiv_inv; simpl.
    unfold Sect, nchar_to_sub, composition, E_to_χ_map, composition in eissect.
    specialize (eissect (λ x, φ x a)).
    exact (equal_f _ eissect x).
  Defined.

  Definition dep_prod_SnType_j_Type : forall A (B : A -> SnType_j_Type) ,
                                   Snsheaf_struct (forall a, (B a).1.1; 
                    @trunc_forall _ A (fun a => (B a).1.1) (trunc_S minus_one) (fun a => (B a).1.2)) :=
    λ A B, dep_prod_SnType_j_Type_eq _.

  Definition closed E (χ : E -> HProp) := forall e, IsEquiv (Oj_unit (χ e)).
  
  Definition closed' E A (m : {f : A -> E & forall b:E, IsHProp (hfiber f b)}) := closed (nsub_to_char minus_one (A;m)).

  Definition cloture E (χ : E -> HProp) : E -> HProp := pr1 o nj.(O) o χ.
  
  Definition cloture' E A (m : {f : A -> E & forall b:E, IsHProp (hfiber f b)}) :=
    nchar_to_sub (cloture (nsub_to_char minus_one (A;m))).

  Definition cloture_is_closed (E :Type) (χ : E -> HProp) : closed (cloture χ).
    intro. apply O_modal_equiv.
  Defined.

  Lemma cloture_is_closed' (A:Type) (E:Type) (m : {f : A -> E & forall e:E, IsHProp (hfiber f e)}) : closed' ((cloture' m).2).
    unfold closed', cloture'.
    rewrite <- existT_eta.
    assert (f := cloture_is_closed (nsub_to_char minus_one (A; m))).
    rewrite <- (@nsub_eq_char_retr minus_one _ (cloture (nsub_to_char minus_one (A; m)))) in f.
    exact f. 
  Defined.

  Lemma closed_hprop E (χ : E -> HProp) : IsHProp (closed χ).  apply trunc_forall. Qed.
  Lemma closed'_hprop (E:Type) (A:Type) m : IsHProp (closed' (E:=E) (A:=A) m). apply closed_hprop. Qed.
          
  Definition δ (T:HSet) : ((T.1)**(T.1)) -> HProp.
    intro x. exists (fst x = snd x). apply istrunc_paths.
    exact T.2.
  Defined.

  Definition Δ T := (nchar_to_sub (δ T)).

  Definition clδ T := pr1 o nj.(O) o (δ T). 

  Definition clΔ T := (nchar_to_sub (clδ T)).
  
  (**** from type to separated type ****)

  Definition separated_Type (T:HSet) : Type :=
    Im (λ t : T.1, λ t', nj.(O) (t = t'; istrunc_paths (H:=T.2) (T.1) minus_one t t')).

  Definition sheaf_is_separated (T : SnType_j_Type) : separated (T.1) := λ E χ, equiv_is_mono (T.2 E χ).
  
  Definition separated_Type_is_Trunc_Sn (T:HSet) : IsHSet (separated_Type T).
    unfold separated_Type; simpl.
    destruct T as [T TrT]; simpl in *.
    apply (@trunc_sigma _ (fun P => _)). 
    apply (@trunc_forall _ _ (fun P => _)). intro. 
    exact (@subuniverse_Type_is_TruncSn _ nj).
    intro φ. exact (IsHProp_IsTrunc (istrunc_truncation _ _) minus_one). 
  Defined.

  Definition E_to_χ_map_ap (T U:HSet) E (χ : E -> Top.J) (f : E -> (T.1))
             (g : T.1 -> U.1) x y (e : x = y) : 
    apf g (ap (E_to_χ_map T (χ:=χ)) e) = ap (E_to_χ_map U (χ:=χ)) (apf g e).
    destruct e; reflexivity.
  Defined.

  Definition apf_Mono (T U:Type) (f: T -> U) (fMono : IsMonof f) X (x y : X -> T) (e e' : x = y) : 
    apf f e = apf f e' -> e = e'.
    intro. 
    rewrite <- (@eissect _ _ _ (fMono _ _ _) e). 
    rewrite <- (@eissect _ _ _ (fMono _ _ _) e'). exact (ap _ X0). 
  Defined.

  Instance separated_mono_is_separated_ (T U:HSet) E χ g h (f: T.1 -> U.1)
        (H:IsEquiv (ap (E_to_χ_map U (E:=E) (χ:=χ)) (x:=f o g) (y:=f o h))) (fMono : IsMonof f) : 
           IsEquiv (ap (E_to_χ_map T (E:=E) (χ:=χ)) (x:=g) (y:=h)).
  apply (isequiv_adjointify _ (fun X => @equiv_inv _ _ _ (fMono E g h) (@equiv_inv _ _ _ H (apf f X)))).
  - intro e. 
    apply (@apf_Mono _ _ _ fMono). 
    unfold equiv_inv.
    pose (E_to_χ_map_ap T U χ g f 
                        (@equiv_inv _ _ _ (fMono _ g h) (@equiv_inv _ _ _ H (apf f e)))).
    apply (transport (fun X => X = _) (inverse p)). clear p.
    eapply concat; try exact (@eisretr _ _ _ H (apf f e)). 
    apply ap. apply (@eisretr _ _ _ (fMono _ _ _)).
  - intro e. 
    pose (E_to_χ_map_ap T U χ g f e).
    apply (transport (fun X => equiv_inv (equiv_inv X) = _) (inverse p)).
    apply (transport (fun X => equiv_inv X = _) 
                     (inverse ((@eissect _ _ _ H (apf f e))))).
    apply eissect.
  Defined.

  Definition separated_mono_is_separated (T U:HSet) (H:separated U) (f: T.1 -> U.1)
             (fMono : IsMonof f) : separated T
 :=
    fun E χ x y => separated_mono_is_separated_ _ (H E χ (f o x) (f o y)) fMono.

  Definition T_nType_j_Type_trunc (T:HSet) : IsHSet (T.1 -> subuniverse_Type nj).
    apply (@trunc_forall _ _ (fun P => _)). intro. 
    apply (@trunc_sigma _ (fun P => _)). apply Tn_is_TSn.
    intro. apply IsHProp_IsTrunc. exact ((subuniverse_HProp nj a0).2).
  Defined.

  Definition T_nType_j_Type_isSheaf : forall T, Snsheaf_struct (T.1 -> subuniverse_Type nj;
                                                    T_nType_j_Type_trunc T).
    intro.
    apply (dep_prod_SnType_j_Type (fun x:T.1 => ((subuniverse_Type nj ; @subuniverse_Type_is_TruncSn _ nj);nType_j_Type_is_SnType_j_Type))).
  Defined.

  Definition T_nType_j_Type_sheaf T : SnType_j_Type :=  ((T.1 -> subuniverse_Type nj; T_nType_j_Type_trunc T); T_nType_j_Type_isSheaf _).

  Definition separated_Type_is_separated (T:HSet) : separated (separated_Type T; separated_Type_is_Trunc_Sn (T:=T)).
    apply (@separated_mono_is_separated
              (separated_Type T;separated_Type_is_Trunc_Sn (T:=T))
              (T.1 -> subuniverse_Type nj; T_nType_j_Type_trunc T)
              (sheaf_is_separated (T_nType_j_Type_sheaf T))
              (pr1 )).
    rewrite IsMonof_isMono. intros x y. apply subset_is_subobject. intro.
    unfold squash. apply istrunc_truncation.
  Defined.

  Definition separation (T:HSet) : {T : HSet & separated T} :=
    ((separated_Type T ; separated_Type_is_Trunc_Sn (T:=T));separated_Type_is_separated (T:=T)).

  Definition separated_unit T : T.1 -> separated_Type T := toIm _.

  Definition kpsic_func T : (clΔ T) .1 -> kernel_pair (separated_unit T).
    intro X. destruct X as [ab p]. destruct ab as [a b]. simpl in p.
      pose (Ωj := (T.1 -> subuniverse_Type nj; T_nType_j_Type_trunc T)).
      pose (inj := pr1 : (separated_Type T) -> Ωj.1).
      assert (IsMono inj).
            intros x y. apply subset_is_subobject. intro.
            unfold squash. apply istrunc_truncation.
      unfold kernel_pair, pullback.
      exists a. exists b.
      assert (inj (separated_unit T a) = inj (separated_unit T b)).
        unfold inj, separated_unit. simpl.
        apply path_forall; intro t; simpl.
        apply unique_subuniverse; apply truncn_unique.
        unfold Oj; simpl.
        apply univalence_hprop; try apply (_j (existT (λ U, IsHProp U) (_=t) (istrunc_paths T.1 (H:=T.2) minus_one _ t))).
        split; intro H ; intro; apply p; intro; destruct X1; apply H; exact X0.
      destruct (X (separated_unit T a) (separated_unit T b)).
      apply equiv_inv. exact X0.
  Defined.

  Definition kpsic_inv T : kernel_pair (separated_unit T) -> (clΔ T).1.
    unfold kernel_pair, separated_unit, clΔ, toIm, pullback. simpl.
      intro X0; destruct X0 as [a [b p]].
      exists (a,b).
      simpl.
      pose (foo := ap10 (projT1_path p) a); unfold Oj, j in foo; simpl in foo.
      assert (bar := projT1_path (projT1_path foo)); simpl in bar; clear foo.
      assert ((a=b) = (b=a)).
        apply univalence_axiom.
        exists (λ x, inverse x).
        apply isequiv_adjointify with (g:= λ x, inverse x); try intro x; hott_simpl.
      destruct X.
      rewrite <- bar.
      auto.
  Defined.

  Definition kernel_pair_separated_is_clΔ_equiv T : IsEquiv (@kpsic_func T).
    apply isequiv_adjointify with (g := @kpsic_inv T).
    - intro x.
      destruct x as [a [b p]]. 
      apply (path_sigma' (λ x, {y:T.1 & separated_unit T x = separated_unit T y}) idpath).
      apply (path_sigma' (λ x, separated_unit T a = separated_unit T x) idpath).
      simpl.
      unfold eq_dep_subset; simpl. 
      assert (IsHProp (separated_unit T a = separated_unit T b)) by (apply istrunc_paths; apply separated_Type_is_Trunc_Sn).
      apply allpath_hprop.
    - intro x.
      destruct x as [ab p].
      destruct ab as [a b].
      apply (path_sigma' (λ x, ~ ~ (fst x = snd x)) (x := (a,b)) (x' := (a,b)) idpath).
      apply allpath_hprop.
  Defined.

  Definition kernel_pair_separated_is_clΔ T : (clΔ T).1 = kernel_pair (separated_unit T).
    apply univalence_axiom.
    exists (@kpsic_func T).
    exact (kernel_pair_separated_is_clΔ_equiv T).
  Defined.

  Lemma separated_unit_coeq T :
    is_coequalizer
      (* (kernel_pair (separated_unit T)) *)
      (* (T.1) *)
      (* (inj1 (f:=separated_unit T)) *)
      (* (inj2 (f:=separated_unit T)) *)
      (* (separated_Type T) *)
      (* (separated_unit T ; path_forall _ _ (λ x : kernel_pair (separated_unit T), (x .2) .2)). *)
      (separated_unit T ; Im_coequalizes_kernel_pair (λ t t' : T .1, O nj (t = t'; istrunc_paths (H:=T.2) T .1 minus_one t t'))).
  Proof.
    apply Im_is_coequalizer_kernel_pair.
  Qed.
  
  Lemma separated_unit_coeq_Δ_coeq (T:HSet) :
    separated_unit T o (λ x : (clΔ T) .1, fst x .1) = separated_unit T o (λ x : (clΔ T) .1, snd x .1).

    pose (foo := Im_coequalizes_kernel_pair (λ t t' : T .1, O nj (t = t'; istrunc_paths (H:=T.2) T .1 minus_one t t'))).
    unfold separated_unit; simpl.
    unfold inj1, inj2 in foo; simpl in foo.
    pose (ff := kpsic_inv (T:=T)).

    assert (p1 : (λ x : ∃ b : T .1 ** T .1, ~ ~ fst b = snd b, fst x .1) o ff = pr1).
      apply path_forall; intro x.
      (* unfold composition; simpl. *)
      (* unfold ff, kpsic_inv; simpl. *)
      destruct x as [a [b p]]. simpl.
      exact idpath.
    assert (p2 : (λ x : ∃ b : T .1 ** T .1, ~ ~ fst b = snd b, snd x .1) o ff = (λ x, x.2.1)).
      apply path_forall; intro x.
      (* unfold composition, ff, kpsic_inv; simpl. *)
      destruct x as [a [b p]].
      exact idpath.

    apply (elim_E (f:= λ u, u o ff)).
    admit.

    pose (fooo := transport (λ U, toIm (λ t t' : T .1, Oj (t = t'; istrunc_paths T .1 minus_one t t'))
        o U =
        toIm (λ t t' : T .1, Oj (t = t'; istrunc_paths T .1 minus_one t t'))
        o (λ x : kernel_pair
                   (λ t t' : T .1,
                    Oj (t = t'; istrunc_paths T .1 minus_one t t')),
           (x .2) .1)) p1 foo).
    rewrite <- p2 in foo.

    unfold composition in *; simpl in *.
    
    

      

    
    assert ( separated_unit T o (λ x : (clΔ T) .1, fst x .1) o (@kpsic_inv T) =
             separated_unit T o (λ x : (clΔ T) .1, snd x .1) o (@kpsic_inv T)).
    assert ((λ x : (clΔ T) .1, fst x .1) o kpsic_inv (T:=T) = (inj1 (f:=separated_unit T))).
      apply path_forall; intro x.
      destruct x as [a [b p]]. exact idpath.
    apply (transport (λ U, (separated_unit T) o U = separated_unit T o (λ x : (clΔ T) .1, snd x .1) o kpsic_inv (T:=T)) X^).
    assert (((λ x : (clΔ T) .1, snd x .1) o kpsic_inv (T:=T) = (inj2 (f:=separated_unit T)))).
      apply path_forall; intro x.
      destruct x as [a [b p]]. exact idpath.
    apply (transport (λ U, separated_unit T o inj1 (f:=separated_unit T) = separated_unit T o U) X0^).
    exact (path_forall _ _ (λ x : kernel_pair (separated_unit T), (x .2) .2)).
    assert (X0 := apf_L (kpsic_func (T:=T)) X).
    
      apply path_forall; intro u. unfold composition; simpl.

      pose (Ωj := (T.1 -> subuniverse_Type nj; T_nType_j_Type_trunc T)).
      pose (inj := pr1 : (separated_Type T) -> Ωj.1).
      assert (IsMono inj).
            intros x y. apply subset_is_subobject. intro.
            unfold squash. apply istrunc_truncation.
      unfold kernel_pair, pullback.
      assert (inj (separated_unit T (fst u.1)) = inj (separated_unit T (snd u.1))).
        unfold inj, separated_unit. simpl.
        apply path_forall; intro t; simpl.
        apply unique_subuniverse; apply truncn_unique.
        unfold Oj; simpl.
        apply univalence_hprop; try apply (_j (existT (λ U, IsHProp U) (_=t) (istrunc_paths T.1 (H:=T.2) minus_one _ t))).
        split; intro H; intro X3; apply u.2; intro X2 ; unfold δ in X2; simpl in X2; destruct X2; apply H; exact X3.
      destruct (X1 (separated_unit T (fst u.1)) (separated_unit T (snd u.1))).
      apply equiv_inv. exact X2.
  Defined.

  Lemma separated_unit_coeq_Δ (T:HSet) :
    is_coequalizer
      (* ((clΔ T).1) *)
      (* (T.1) *)
      (* (λ x, fst x.1) *)
      (* (λ x, snd x.1) *)
      (* (separated_Type T) *)
      (separated_unit T ; separated_unit_coeq_Δ_coeq T).
  Proof.

    intro Y; simpl.

    pose (φ := @kpsic_func T).
    pose (φeq := (kernel_pair_separated_is_clΔ_equiv T)).

    pose (kp := separated_unit_coeq T Y). simpl in *.

    set (foo := (separated_unit_coeq_Δ_coeq T)) in *.
    set (bar := (Im_coequalizes_kernel_pair
               (λ t t' : T .1, Oj (t = t'; istrunc_paths (H:=T.2) T .1 minus_one t t')))) in *.
    unfold inj1, inj2 in bar; simpl in bar.

    unfold separated_unit in foo.

    unfold toIm in *; simpl in *.

    unfold composition in foo, bar; simpl in foo, bar.

    assert (baar := apf_L φ bar); simpl in baar.
    unfold clΔ in foo. simpl in foo.
    unfold composition in *; simpl in *.
    unfold φ, kpsic_func in baar; simpl in baar.
    assert (baar = foo).
    destruct φ.
    
    
  Defined.
  
  Definition sep_eq_inv (P : HSet) (Q :{T : HSet & separated T})
  : (P .1 → (Q .1) .1) -> (separated_Type P → (Q .1) .1).
    intros f.
    apply (equiv_inv (IsEquiv := separated_unit_coeq_Δ P Q.1.1)).
    exists f.
    apply (equiv_inv (IsEquiv := (Q.2 (clΔ P).1 (λ u:(clΔ P).1, ((fst u.1 = snd u.1 ; @istrunc_paths P.1 minus_one P.2 (fst u.1) (snd u.1)) ; u.2)) (λ u, f (fst u.1)) (λ u, f (snd u.1))))).
    unfold E_to_χ_map, composition. simpl.
    apply path_forall; intro u; apply ap; exact u.2.
  Defined.
    

  Definition separated_equiv : forall (P : HSet) (Q :{T : HSet & separated T}),
                                 IsEquiv (fun f : separated_Type P -> Q.1.1 =>
                                           f o (separated_unit P)).
    intros P Q.
    apply isequiv_adjointify with (g := sep_eq_inv Q).
    - intro f.
      unfold sep_eq_inv, composition; simpl.
      apply path_forall; intro x.
      unfold equiv_inv.
      destruct (separated_unit_coeq_Δ P (Q .1) .1) as [inv1 retr1 sect1 _].
      unfold Sect, composition in *; simpl in *.

      specialize (retr1 (f;
     (let (equiv_inv, eisretr, eissect, _) :=
          Q .2 (∃ b : P .1 ** P .1, ~ ~ fst b = snd b)
            (λ u : ∃ b : P .1 ** P .1, ~ ~ fst b = snd b,
             ((fst u .1 = snd u .1;
              istrunc_paths P.1 (H:=P.2) minus_one (fst u .1) (snd u .1)); 
             u .2))
            (λ u : ∃ b : P .1 ** P .1, ~ ~ fst b = snd b, f (fst u .1))
            (λ u : ∃ b : P .1 ** P .1, ~ ~ fst b = snd b, f (snd u .1)) in
      equiv_inv)
       (path_forall
          (λ t : ∃ b : ∃ b : P .1 ** P .1, ~ ~ fst b = snd b,
                 fst b .1 = snd b .1, f (fst (t .1) .1))
          (λ t : ∃ b : ∃ b : P .1 ** P .1, ~ ~ fst b = snd b,
                 fst b .1 = snd b .1, f (snd (t .1) .1))
          (λ u : ∃ b : ∃ b : P .1 ** P .1, ~ ~ fst b = snd b,
                 fst b .1 = snd b .1, ap f u .2)))).
      simpl in retr1.
      pose (fooo := retr1..1); simpl in fooo.
      pose (baar := ap10 fooo x); simpl in baar.
      exact baar.
    - intro f.
      unfold sep_eq_inv; simpl.
      (* apply path_forall; intro x. *)
      unfold E_to_χ_map; simpl.

      (* unfold equiv_inv. *)
      destruct (separated_unit_coeq_Δ P (Q .1) .1) as [inv retr sect adj].
      unfold Sect, composition in *; simpl in *.

       set (eqqq := (path_forall
          (λ t : ∃ b : ∃ b : P .1 ** P .1, ~ ~ fst b = snd b,
                 fst b .1 = snd b .1, f (separated_unit P (fst (t .1) .1)))
          (λ t : ∃ b : ∃ b : P .1 ** P .1, ~ ~ fst b = snd b,
                 fst b .1 = snd b .1, f (separated_unit P (snd (t .1) .1)))
          (λ u : ∃ b : ∃ b : P .1 ** P .1, ~ ~ fst b = snd b,
                 fst b .1 = snd b .1,
           ap (λ t : P .1, f (separated_unit P t)) u .2))).
       clear adj.
       specialize (sect f).
       (* pose (bar := ap10 sect x). *)
       rewrite <- sect.
       apply (ap inv).
       apply path_sigma' with (p:=idpath). rewrite transport_1.
       clear retr; clear sect; clear inv.
       unfold separated_unit; simpl.
       
      apply (transport (λ U, _ = U) ((eissect (IsEquiv := Q .2 (∃ b : P .1 ** P .1, ~ ~ fst b = snd b)
          (λ u : ∃ b : P .1 ** P .1, ~ ~ fst b = snd b,
           ((fst u .1 = snd u .1;
            istrunc_paths P .1 (H:=P.2) minus_one (fst u .1) (snd u .1)); 
           u .2))
          (λ u : ∃ b : P .1 ** P .1, ~ ~ fst b = snd b,
           f
             (toIm
                (λ t t' : P .1,
                 Oj (t = t'; istrunc_paths P .1 minus_one t t')) 
                (fst u .1)))
          (λ u : ∃ b : P .1 ** P .1, ~ ~ fst b = snd b,
           f
             (toIm
                (λ t t' : P .1,
                 Oj (t = t'; istrunc_paths P .1 minus_one t t')) 
                (snd u .1)))) _ (apf f (separated_unit_coeq_Δ_coeq P))))).
      unfold E_to_χ_map.
      apply ap.
      assert (IsHProp
                ((λ t : ∃ b : ∃ b : P .1 ** P .1,
                                ~ ~ fst b = snd b,
                          fst b .1 = snd b .1,
                    f (separated_unit P (fst (t .1) .1))) =
                 (λ t : ∃ b : ∃ b : P .1 ** P .1,
                                ~ ~ fst b = snd b,
                          fst b .1 = snd b .1,
                    f (separated_unit P (snd (t .1) .1))))).
      apply istrunc_paths.
      apply (trunc_arrow (H0:=Q.1.2)).
      
      apply allpath_hprop.
  Defined.

  (**** From separated to sheaf ****)

  Definition closure_naturality_fun
             (E : Type)
             (F : Type)
             (A : Type)
             (m : A -> E)
             (Trm : forall b : E, IsHProp (hfiber m b))
             (Γ : F -> E)
  : {b : F & ((nj.(O) ( (hfiber m (Γ b) ; Trm (Γ b)))).1.1)} -> {b : F & hfiber (pr1 (P:=λ b0 : E, (cloture (nsub_to_char minus_one (A; (m; Trm))) b0).1)) (Γ b)}
    := λ X, (X.1 ; (((Γ (X.1) ; @Oj_equiv (hfiber m (Γ (X.1)); Trm (Γ (X.1)))
                        (nj.(O) (nsub_to_char minus_one (A; (m; Trm)) (Γ (X.1))))
                        (λ Hb : (hfiber m (Γ (X.1)); Trm (Γ (X.1))).1,
                                Oj_unit (nsub_to_char minus_one (A; (m; Trm)) (Γ (X.1))) Hb) 
                        (X.2))) ; idpath)).

  Definition closure_naturality_inv
             (E : Type)
             (F : Type)
             (A : Type)
             (m : A -> E)
             (Trm : ∀ b : E, IsHProp (hfiber m b))
             (Γ : F -> E)
  : {b : F & hfiber (pr1 (P:=λ b0 : E, (cloture (nsub_to_char minus_one (A; (m; Trm))) b0).1)) (Γ b)} -> {b : F & ((nj.(O) ( (hfiber m (Γ b) ; Trm (Γ b)))).1.1)}.
    intro X; exists (X.1).
    generalize (X.2.1.2); apply Oj_equiv; intro HHb; apply Oj_unit.
    destruct (X.2.2). exact HHb.
  Defined.

  Definition closure_naturality_retr
             (E : Type)
             (F : Type)
             (A : Type)
             (m : A -> E)
             (Trm : ∀ b : E, IsHProp (hfiber m b))
             (Γ : F -> E)
  : Sect (closure_naturality_inv Γ) (closure_naturality_fun Trm Γ).
    intro X; unfold closure_naturality_fun, closure_naturality_inv; simpl.
    destruct X as [b Hb]; simpl.
    apply path_sigma' with (p := idpath); simpl.
    destruct Hb as [[b0 Hb0] eq]; simpl in *.
    destruct eq.

    pose (rew1 := equal_f _ (eissect _ (IsEquiv := (nj.(O_equiv) (nsub_to_char minus_one (A; (m; Trm)) b0) (nj.(O) (existT (IsHProp) (hfiber m b0) (Trm b0))))) (λ x, x)) ( equiv_inv (IsEquiv := O_equiv nj (hfiber m b0; Trm b0)
                (O nj (nsub_to_char minus_one (A; (m; Trm)) b0))) (λ t : hfiber m b0, Oj_unit (hfiber m b0; Trm b0) t) Hb0)).

    pose (rew2 := equal_f _ (eissect _ (IsEquiv := nj.(O_equiv) (hfiber m b0; Trm b0) (nj.(O) (nsub_to_char minus_one (A; (m; Trm)) b0))) (λ x, x)) Hb0).

    unfold nsub_to_char, hfiber, composition in *; simpl in *.

    unfold Oj_equiv; simpl.
    apply path_sigma' with (p := (path_sigma' (λ x, _) (idpath b0) (rew1 @ rew2))). 
    destruct (rew1 @ rew2); simpl. reflexivity.
  Defined.

  Definition closure_naturality_sect
             (E : Type)
             (F : Type)
             (A : Type)
             (m : A -> E)
             (Trm : ∀ b : E, IsHProp (hfiber m b))
             (Γ : F -> E)
  : Sect (closure_naturality_fun Trm Γ) (closure_naturality_inv Γ).
    intro X; unfold closure_naturality_fun; simpl.
    destruct X as [b Hb]; simpl.
    apply path_sigma' with (p := idpath); simpl.
    unfold Oj_equiv.

    pose (rew1 := equal_f _ (eissect _ (IsEquiv := nj.(O_equiv) (hfiber m (Γ b); Trm (Γ b))
             (nj.(O) (nsub_to_char minus_one (A; (m; Trm)) (Γ b)))) (λ x, x))
                         (equiv_inv (IsEquiv := O_equiv nj (nsub_to_char minus_one (A; (m; Trm)) (Γ b))
          (O nj (hfiber m (Γ b); Trm (Γ b))))
        (λ Hb0 : hfiber m (Γ b),
         Oj_unit (nsub_to_char minus_one (A; (m; Trm)) (Γ b)) Hb0) Hb)
         ).

    pose (rew2 := equal_f _ (eissect _ (IsEquiv := O_equiv nj (nsub_to_char minus_one (A; (m; Trm)) (Γ b))
          (O nj (hfiber m (Γ b); Trm (Γ b)))) (λ x, x)) Hb).
    
    exact (rew1 @ rew2).
  Defined.

  Definition closure_naturality E F A (m : {f : A -> E & forall b:E, IsHProp (hfiber f b)}) (Γ : F -> E) :
    {b : F & ((nj.(O) ((hfiber (m.1) (Γ b)) ; (m.2) (Γ b))).1.1)} = {b : F & hfiber (((cloture' m).2.1)) (Γ b)}.
    destruct m as [m Trm]; simpl.
    apply univalence_axiom.
    exists (closure_naturality_fun _ _).
    apply (isequiv_adjointify _ _ (closure_naturality_retr _) (closure_naturality_sect _ _)).
  Defined.

  Definition cloture_fun
        (E : Type)
        (P : E -> J)
        (Q : E -> HProp)
        (f : forall e:E, (P e).1.1 -> (Q e).1)
  : {e:E | (nj.(O) (((P e).1.1); IsHProp_IsTrunc (((P e).1.2)) minus_two)).1.1} -> {e:E | (nj.(O) (Q e)).1.1}
    := (λ b, (b.1;
              @Oj_equiv (((P (b.1)).1.1); IsHProp_IsTrunc (((P (b.1)).1.2)) minus_two)
                    (nj.(O) (Q (b.1)))
                    (λ X2 : ((P (b.1)).1.1),
                            Oj_unit (Q (b.1)) (f (b.1) X2))
                    (b.2))).
    
  Definition cloture_fun_restriction
        (E : Type)
        (P : E -> J)
        (Q : E -> HProp)
        (f : forall e:E, (P e).1.1 -> (Q e).1)
  :forall (e : {e:E | (P e).1.1}), (cloture_fun P Q f (e.1; Oj_unit (((P (e.1)).1.1); IsHProp_IsTrunc (((P (e.1)).1.2)) minus_two) (e.2))).2 = Oj_unit (Q (e.1)) ((f (e.1) (e.2)))
    := λ e, equal_f _ (eisretr _ (IsEquiv := (O_equiv nj (((P e .1) .1) .1; IsHProp_IsTrunc ((P e .1) .1) .2 minus_two) (O nj (Q e .1)))) (λ X, Oj_unit _ (f _ X))) (e.2).

  Lemma cloture_fun_
        (E : Type)
        (P : E -> J)
        (Q : E -> HProp)
        (f : forall e:E, (P e).1.1 -> (Q e).1)
        (g : forall e:E, (nj.(O) (((P e).1.1); IsHProp_IsTrunc (((P e).1.2)) minus_two)).1.1)
        (h : forall e:E, (Q e).1)
        (H : forall e:E, forall X:(P e).1.1, f e X = h e)
  : forall (e:E), (cloture_fun P Q f (e; g e)).2 = Oj_unit (Q e) (h e).
    intro e.
    pose (foo := equal_f _ (eissect _ (IsEquiv := O_equiv nj (((P e) .1) .1; IsHProp_IsTrunc ((P e) .1) .2 minus_two)
          (O nj (Q e))) (λ _, Oj_unit (Q e) (h e))) (g e)); simpl in foo.
    assert ((λ X2 : ((P e) .1) .1, Oj_unit (Q e) (f e X2)) = (λ X2 : ((P e) .1) .1, Oj_unit (Q e) (h e))).
      apply path_forall; intro X2.
      rewrite <- H  with (X := X2).
      exact idpath.
    apply (transport _ foo).
    exact (equal_f _ (ap (equiv_inv (IsEquiv := O_equiv nj (((P e) .1) .1; IsHProp_IsTrunc ((P e) .1) .2 minus_two)
          (O nj (Q e)))) X) (g e)).
  Defined.

  Definition E_to_Y'A
             (A : HSet)
             (B : SnType_j_Type)
             (m : A.1 -> B.1.1)
             (X1 : ∀ b : B.1.1, IsHProp (hfiber m b))
             (closed0 : closed' (m; X1))
             (E : Type)
             (χ : E -> J)
             (X : {b : E & ((pr1 (P:=λ b0 : HProp, ~ ~ b0.1) o χ) b).1} -> A.1)
             (X0 : E)
             (inv_B : ((nchar_to_sub
                            (pr1
                               (P:=λ b : HProp,
                                         ((pr1 (P:=λ P : HProp, (is_classical P).1) o Oj) b).1)
                               o χ)).1 -> B.1.1) -> E -> B.1.1)
             (retr_B : Sect inv_B (E_to_χ_map (B.1) (χ:=χ)))
             (Y := inv_B (m o X) : E -> B.1.1)
    := (λ b, (b.1 ; (X b ; (inverse (equal_f _ (retr_B (moX)) b)))))  : {b : E & (χ b).1.1} -> {b : E & hfiber m (Y b)}.

  Definition clE_to_clY'A
             (A : HSet)
             (B : SnType_j_Type)
             (m : A.1 -> B.1.1)
             (X1 : ∀ b : B.1.1, IsHProp (hfiber m b))
             (closed0 : closed' (m; X1))
             (E : Type)
             (χ : E -> J)
             (X : {b : E & ((pr1 (P:=λ b0 : HProp, ~ ~ b0.1) o χ) b).1} -> A.1)
             (X0 : E)
             (inv_B : ((nchar_to_sub
                            (pr1
                               (P:=λ b : HProp,
                                         ((pr1 (P:=λ P : HProp, (is_classical P).1) o Oj) b).1)
                               o χ)).1 -> B.1.1) -> E -> B.1.1)
             (retr_B : Sect inv_B (E_to_χ_map (B.1) (χ:=χ)))
             (Y := inv_B (m o X) : E -> B.1.1)

    := cloture_fun χ (λ x, (hfiber m (Y x); X1 (Y x))) (λ e p, (E_to_Y'A _ _ closed0 _ X0 retr_B (e;p)).2)
:
         {b:E & ((nj.(O) (((χ b).1.1); IsHProp_IsTrunc (((χ b).1.2)) minus_two)).1.1)} -> {b : E & ((nj.(O) (hfiber m (Y b) ; X1 (Y b))).1.1)}.

  Lemma equalΠ2_restriction_χ
        (A : HSet)
        (B : SnType_j_Type)
        (m : A.1 -> B.1.1)
        (X1 : ∀ b : B.1.1, IsHProp (hfiber m b))
        (closed0 : closed' (m; X1))
        (E : Type)
        (χ : E -> J)
        (X : {b : E & ((pr1 (P:=λ b0 : HProp, ~ ~ b0.1) o χ) b).1} -> A.1)
        (X0 : E)
        (inv_B : ((nchar_to_sub
                            (pr1
                               (P:=λ b : HProp,
                                         ((pr1 (P:=λ P : HProp, (is_classical P).1) o Oj) b).1)
                               o χ)).1 -> B.1.1) -> E -> B.1.1)
        (retr_B : Sect inv_B (E_to_χ_map (B.1) (χ:=χ)))
        (Y := inv_B (m o X) : E -> B.1.1)
  : forall (b : {e : E & (χ e).1.1}), 
      (clE_to_clY'A _ _ closed0 _ X0 retr_B (b.1 ; Oj_unit (((χ (b.1)).1.1); IsHProp_IsTrunc (((χ (b.1)).1.2)) minus_two) (b.2))).2 = Oj_unit ({x : A.1 & m x = Y (b.1)}; X1 (Y (b.1))) ((E_to_Y'A _ _ closed0 _ X0 retr_B b).2).
  Proof.
    unfold clE_to_clY'A. intro b.
    pose (foo := cloture_fun_restriction χ (λ x, (hfiber m (Y x); X1 (Y x))) (λ e p, (E_to_Y'A _ _ closed0 _ X0 retr_B (e;p)).2) b).
    unfold Y, hfiber, composition in *.
    rewrite (existT_eta (A:=E) (P:=λ x, ((χ x) .1) .1) b).
    exact foo.
  Defined.

  Lemma ap_equalf (A B C:Type) (x y : C -> B) (a : A) eq (φ : A -> C): (equal_f _ (ap (x:=x) (y:=y) (λ (f : C -> B), λ (t:A), f (φ t)) eq)) a = equal_f _ eq (φ a).
    destruct eq; simpl. exact idpath.
  Qed.
  
  Definition closed_to_sheaf_inv
             (A : HSet)
             (B : SnType_j_Type)
             (m : {f : A.1 -> B.1.1 & ∀ b : B.1.1, IsHProp (hfiber f b)})
             (closed : closed' m)
             (E : Type)
             (χ : E -> J)
             (eq := (B.2) E χ)
  : ((nchar_to_sub (pr1 o χ)) .1 -> A .1) -> (E -> A .1).
    intros X X0.
    destruct ((B.2) E χ) as [inv_B retr_B sect_B adj_B].
    pose (X2:=(χ X0).2).
    (* apply (transport idmap  (j_is_nj (((χ X0) .1)))) in X2. *)
    destruct (closed (inv_B ((m.1)oX) X0)) as [inv_closed retr_closed sect_closed adj_closed].
    
    exact ((pr1 (P:=_) o inv_closed) ((((closure_naturality_fun _ _ (@clE_to_clY'A A B (m.1) (m.2) closed E χ X X0 inv_B retr_B (X0;X2))).2.1.2)))).
  Defined.

  Definition closed_to_sheaf_retr 
             (A : HSet)
             (B : SnType_j_Type)
             (m : {f : A.1 -> B.1.1 & ∀ b : B.1.1, IsHProp (hfiber f b)})
             (closed : closed' m)
             (E : Type)
             (χ : E -> J)
             (eq := (B.2) E χ)

  : Sect (@closed_to_sheaf_inv A B m closed E χ) (E_to_χ_map A (χ:=χ)).
    intro X.
    destruct m as [m Trm].
    apply path_forall; intro b.
    unfold closed_to_sheaf_inv, E_to_χ_map, nsub_to_char, composition, hfiber, Oj_equiv, Equivalences.internal_paths_rew in *; simpl in *.

    destruct (  (@projT2 (HSet)
         (fun T : HSet => Snsheaf_struct T)
         B) E χ) as [inv_B retr_B sect_B adj_B].


    destruct (closed (inv_B (λ t : {b0 : E & (pr1 (P:= (λ b1:HProp, ~ ~ (b1.1))) (χ b0)).1}, m (X t)) (b.1))) as [inv_closed retr_closed sect_closed adj_closed].

    pose (rew1 := equal_f _ (eissect _ (IsEquiv :=
                                        nj.(O_equiv)
                                             ({x : A.1 &
                                                   m x =
                                                   inv_B (λ t : {b0 : E & ((χ b0).1.1)}, m (X t)) (b.1)};
                Trm (inv_B (λ t : {b0 : E & ((χ b0).1.1)}, m (X t)) (b.1)))
                (nj.(O)
                   (nsub_to_char minus_one (A.1; (m; Trm))
                                 (inv_B (λ t : {b0 : E & ((χ b0).1.1)}, m (X t))
                                        (b.1))))) (λ x, x))).
    unfold Sect, E_to_χ_map, nsub_to_char, hfiber, Oj_equiv, composition in *; simpl in *.

    (** *) admit.
    (* rewrite (rew1 (χ b.1).2); clear rew1. *)

    (* pose (foo := (@equalΠ2_restriction_χ A B m Trm closed E χ X (Π1 b) inv_B retr_B b)). *)
    (* unfold clE_to_clY'A, E_to_Y'A, Oj_equiv, hfiber, composition in foo; simpl in foo. *)
    (* unfold Sect, E_to_χ_map, nsub_to_char, hfiber, Oj_equiv, composition in *; simpl in *. *)

    (* (* pose (bar := j_is_nj_unit ((χ b .1) .1) (b.2)). *) *)
    (* unfold Oj_unit, transport, Sect, E_to_χ_map, nsub_to_char, hfiber, Oj_equiv, composition in *; simpl in *. *)
    
    (* assert ((λ k : ~ ((χ b .1) .1) .1, k b .2) = (χ b .1) .2). *)
    (*   apply path_forall; intro x. *)
    (*   destruct ((χ b .1) .2 x). *)

    (* assert (fooo := transport (λ x,  match j_is_nj (χ b .1) .1 in (_ = a) return a with *)
    (*                                    | 1%path => x *)
    (*                                  end = *)
    (*                                  Oj_unit nj (((χ b .1) .1) .1; IsHProp_IsTrunc ((χ b .1) .1) .2 minus_two) *)
    (*                                         b .2) X0 bar). *)
    (* simpl in fooo. *)
    (* rewrite <- fooo in foo. *)
    
    (* apply transport with (x := Oj_unit nj ({x : A .1 | m x = inv_B (λ t, m (X t)) b .1}; *)
    (*                                       Trm (inv_B (λ t : {b : E | ((χ b) .1) .1}, m (X t)) b .1)) *)
    (*                                   (X b; inverse (equal_f (λ _, (B .1) .1) (retr_B (λ t, m (X t))) b))) *)
    (*                      (y:=_). *)
   
    (* exact (inverse foo). *)
    (* rewrite sect_closed. *)
    (* exact idpath. *)
  Defined.

  Definition closed_to_sheaf_sect
             (A : HSet)
             (B : SnType_j_Type)
             (m : {f : A.1 -> B.1.1 & ∀ b : B.1.1, IsHProp (hfiber f b)})
             (closed : closed' m)
             (E : Type)
             (χ : E -> J)
             (eq := (B.2) E χ)

  : Sect (E_to_χ_map A (χ:=χ)) (@closed_to_sheaf_inv A B m closed E χ).
    destruct m as [m Trm].
    intro X; unfold closed_to_sheaf_inv; simpl in *.
    apply path_forall; intro b.
    unfold E_to_χ_map, nsub_to_char, composition, hfiber, Oj_equiv in *; simpl in *.
        destruct ( (@projT2 (HSet)
         (fun T : HSet => Snsheaf_struct T)
         B) E χ) as [inv_B retr_B sect_B adj_B].
    destruct (closed (inv_B (λ t : {b0 : E & (pr1 (P:= (λ b1:HProp, ~ ~ (b1.1))) (χ b0)).1}, m (X (t.1))) b)) as [inv_closed retr_closed sect_closed adj_closed].

    (** *) admit.

    (* rewrite (equal_f _ (eissect _ (IsEquiv := *)
    (*                          nj.(O_equiv) *)
    (*                               ({x : Π1 A & *)
    (*                                     m x = *)
    (*                                     inv_B (λ t : {b0 : E & Π1 (Π1 (χ b0))}, m (X (Π1 t))) b}; *)
    (*                                Trm (inv_B (λ t : {b0 : E & Π1 (Π1 (χ b0))}, m (X (Π1 t))) b)) *)
    (*                               (nj.(O) *)
    (*                                     (nsub_to_char minus_one (Π1 A; (m; Trm)) *)
    (*                   (inv_B (λ t : {b0 : E & Π1 (Π1 (χ b0))}, m (X (Π1 t))) *)
    (*                      b)))) (λ x, x))). *)

    (* pose (foo := equal_f _ (sect_B (moX))).  *)
    (* set (Y := inv_B (m o (X o pr1) ) : E -> Π1 (Π1 B)). *)

    (* apply transport with *)
    (*   (x := Oj_unit nj ({x : A .1 | m x = Y b}; Trm (Y b)) (X b; inverse (foo b))) (y:=_). *)
  
    (* unfold E_to_χ_map, nsub_to_char, hfiber, Oj_equiv, Y, composition in *; simpl in *. *)
   
    (* pose (h := (λ e, (X e; inverse (foo e))) : ∀ e : E, {x : A .1 | m x = inv_B (λ t : {b : E | ((χ b) .1) .1}, m (X t .1)) e}). *)
    (* assert ((∀ (e : E) (X0 : ((χ e) .1) .1), *)
    (*       (X e; *)
    (*        inverse *)
    (*          (equal_f (λ _ : {b : E | ((χ b) .1) .1}, (B .1) .1) *)
    (*                   (retr_B (λ t : {b : E | ((χ b) .1) .1}, m (X t .1))) *)
    (*                   (e; X0))) = h e)). *)
    (*   intros; unfold h, foo. apply path_sigma' with (prf := idpath); simpl. *)
    (*   apply ap. *)
    (*   clear eq. specialize (adj_B (moX)). unfold composition in adj_B. *)
    (*   apply (transport (λ x:((λ (f : E -> (B .1) .1) (t : {b0 : E | ((χ b0) .1) .1}), f t .1) *)
    (*      (inv_B (λ t : {b0 : E | ((χ b0) .1) .1}, m (X t .1))) = *)
    (*    (λ t : {b0 : E | ((χ b0) .1) .1}, m (X t .1))), ((equal_f (λ _ : {b0 : E | ((χ b0) .1) .1}, (B .1) .1) x (e; X0)) = (equal_f (λ _ : E, (B .1) .1) (sect_B (λ t : E, m (X t))) e))) (inverse adj_B)). *)
    (*   clear adj_B. *)
    (*   exact (@ap_equalf {b0 : E | ((χ b0) .1) .1} ((B .1) .1) E (inv_B (λ t : {b : E | ((χ b) .1) .1}, (λ t0 : E, m (X t0)) t .1)) (λ t : E, m (X t)) (e;X0) (sect_B (λ t : E, m (X t))) pr1). *)

    (* exact (inverse (@cloture_fun_ E χ (λ x, (hfiber m (Y x); Trm (Y x))) (λ e p, Π2 (E_to_Y'A _ _ closed _ b retr_B (e;p))) (λ b, match j_is_nj (χ b) .1 in (_ = y) return y with | 1%path => (χ b) .2 end) h X0 b)). *)
    
    (* rewrite sect_closed. *)
    (* exact idpath. *)
  Defined.

  Definition closed_to_sheaf (A:HSet) (B:SnType_j_Type) (m : {f : A.1 -> B.1.1 & forall b, IsHProp (hfiber f b)})
  : closed' m  -> Snsheaf_struct A := λ x, λ E χ, isequiv_adjointify _ (@closed_to_sheaf_inv A B m x E χ) (@closed_to_sheaf_retr A B m x E χ) (@closed_to_sheaf_sect A B m x E χ).


  Definition mono_is_hfiber (T U : Type) (m : T -> U) (Monom : IsMono m) :
    ∀ b , IsHProp (hfiber m b).
    intro. apply IsHProp_IsTrunc.
    apply (IsMono_IsHProp_fibers Monom).
  Defined.

  Definition separated_to_sheaf_Type (T U: Type) (m : T -> U) (Monom : IsMono m) : Type  :=
    (cloture' (m; mono_is_hfiber Monom)).1.    
  
  Definition separated_to_sheaf_IsTrunc_Sn (T U : HSet) m Monom :
    IsHSet (@separated_to_sheaf_Type T.1 U.1 m Monom).
    apply (@trunc_sigma _ (fun P => _)).
    exact (U.2).
    intro a.
    apply (@trunc_succ _ _).
    exact ((nj.(O) (nsub_to_char minus_one (T.1; (m ; mono_is_hfiber Monom)) a)).1.2).
  Defined.
  
  Definition separated_to_sheaf (T:{T : HSet & separated T}) (U:SnType_j_Type) m Monom :
     Snsheaf_struct (@separated_to_sheaf_Type T.1.1 U.1.1 m Monom; @separated_to_sheaf_IsTrunc_Sn _ _ m Monom).
    pose (foo := closed_to_sheaf (separated_to_sheaf_Type (m:=m) Monom; (@separated_to_sheaf_IsTrunc_Sn _ _ m  Monom)) U).
    unfold separated_to_sheaf_Type in *; simpl in *.

    specialize (foo ((cloture' (m;mono_is_hfiber Monom)).2)).
    apply foo.
    apply (cloture_is_closed' (m; mono_is_hfiber Monom)).
  Defined.

  Definition IsMono_fromIm_inv {A B} (f : A -> B) (x y : Im f): x.1 = y.1 -> x=y.
    intro X.
    apply path_sigma with (p := X).
    apply allpath_hprop.
  Defined.
  
  Definition IsMono_fromIm {A B} (f : A -> B) : IsMono (fromIm (f:=f)). 
    intros x y; apply (isequiv_adjointify (ap (fromIm (f:=f))) (IsMono_fromIm_inv x y)).
    - intro a.
      destruct x as [x s]; destruct y as [y r]; simpl in *.
      destruct a; simpl in *.     unfold IsMono_fromIm_inv. simpl.
      destruct (allpath_hprop s r); simpl in *. 
      reflexivity.
    - intro a.
      unfold IsMono_fromIm_inv, allpath_hprop, center.
      destruct a, x as [x s]; simpl.
      destruct (istrunc_truncation minus_one (hfiber f x) s s) as [center contr].
      rewrite (contr idpath); reflexivity.
  Defined.

  Definition sheafification_Type (T:HSet) :=
    @separated_to_sheaf_Type (separated_Type T) 
                             (T.1 -> subuniverse_Type nj) (fromIm (f:=_)) 
                             (IsMono_fromIm (f:=_)).

  Definition sheafification_istrunc (T:HSet) : 
    IsHSet (sheafification_Type T).
    apply (separated_to_sheaf_IsTrunc_Sn (separated_Type T; separated_Type_is_Trunc_Sn (T:=T)) 
                              (T.1 -> subuniverse_Type nj; T_nType_j_Type_trunc T)).
  Defined.

  Definition sheafification_trunc (T:HSet) : HSet :=
    (sheafification_Type T ; sheafification_istrunc  (T:=T)). 

  Definition sheafification_ (T:HSet) : Snsheaf_struct (sheafification_trunc T) :=
    separated_to_sheaf ((separated_Type T; separated_Type_is_Trunc_Sn (T:=T)); @separated_Type_is_separated T) (T_nType_j_Type_sheaf T) (IsMono_fromIm (f:=_)).

  Definition sheafification (T:HSet) : SnType_j_Type :=
    ((sheafification_Type T ; sheafification_istrunc  (T:=T)); sheafification_ T).

  Definition sheafification_unit (T:HSet) : T.1 -> (sheafification T).1.1.
    intro X.
    exists ((fromIm (f:=λ t t' : T .1, O nj (t = t'; istrunc_paths (H:=T.2) T .1 minus_one t t'))) (separated_unit T X)).
    apply Oj_unit.
    exact (separated_unit T X ; idpath).
  Defined.

  Definition sheafification_equiv (P:HSet) (Q:SnType_j_Type) : IsEquiv (λ f : ((sheafification P) .1) .1 -> (Q .1) .1, f o sheafification_unit P).
    assert ((P.1 -> Q.1.1) -> ((sheafification P) .1) .1 -> (Q .1) .1).
    intros φ s.
  Admitted. 