Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.

Require Import path equiv truncation univalence sub_object_classifier limit_colimit.

Set Universe Polymorphism.
Global Set Primitive Projections.
Set Implicit Arguments.

Record subuniverse_struct n := Build_subuniverse_struct { 
  
  subuniverse_HProp : forall (T:Trunc n), HProp  ;
    
  O : Trunc n -> {T : Trunc n & (subuniverse_HProp T).1} ;

  O_unit : forall T, T.1 -> (O T).1.1;

  O_equiv : forall (P : Trunc n) (Q :{T : Trunc n & (subuniverse_HProp T).1}),
              IsEquiv (fun f : (O P).1.1 -> Q.1.1 => f ° (O_unit P)) 
}.

Section Reflective_Subuniverse.

  Variable n:trunc_index.

  Variable subU : subuniverse_struct n.
  
  Definition subuniverse_Type := 
  {T : Trunc n & Π1 (subU.(subuniverse_HProp) T)}.
  
  Definition subuniverse_Type_is_TruncSSn : IsTrunc (trunc_S n) subuniverse_Type.
    unfold subuniverse_Type.
    apply (@trunc_sigma _ (fun T => (subuniverse_HProp subU T) .1) _ (Tn_is_TSn (n:=n))).
    intro T. apply IsHProp_IsTrunc. apply (Π2 (subU.(subuniverse_HProp) T)).
  Defined.

  Definition O_rec (P : Trunc n) (Q : subuniverse_Type) :
    (P.1 -> Q.1.1) -> (subU.(O) P).1.1 -> Q.1.1 := 
    (@equiv_inv _ _ _ (subU.(O_equiv) _ _)).

  Definition O_rec_retr (P : Trunc n) (Q : subuniverse_Type) f
  : O_rec _ _ f ° subU.(O_unit) _ = f :=
    @eisretr _ _ _ (subU.(O_equiv) P Q) f.

  Definition O_rec_sect (P : Trunc n) (Q : subuniverse_Type) f :=
    @eissect _ _ _ (subU.(O_equiv) P Q) f.

  Instance O_sheaf_equiv (P : subuniverse_Type) : IsEquiv (subU.(O_unit) P.1).
  apply (isequiv_adjointify _ (O_rec P.1 P idmap)).
  - assert ((O_unit subU P .1) ° (O_rec P .1 P (λ x : (P .1) .1, x)) ° (O_unit subU P .1)
                               = idmap ° (O_unit subU P .1)).
    rewrite <- comp_assoc. unfold composition at 3. apply apf. exact (O_rec_retr P.1 P idmap).
    pose (f := @elim_E _ _ _ (subU.(O_equiv) P.1 (subU.(O) P.1)) 
                       ((O_unit subU P .1) ° (O_rec P .1 P (λ x : (P .1) .1, x))) idmap X). 
    intro x. eapply equal_f in f. exact f.
  - pose (f := O_rec_retr P.1 P idmap). 
    intro. eapply equal_f in f. exact f.
  Defined.

  Definition unique_subuniverse : forall (T T' : subuniverse_Type), Π1 T = Π1 T' -> T = T'. 
    intros. destruct T, T'. eapply (eq_dep_subset _ _ _ _ X). 
    Grab Existential Variables. intro. simpl. exact ((subuniverse_HProp subU a) .2).
  Defined.

  Definition O_sheaf (T:subuniverse_Type) : T = subU.(O) T.1.
    apply unique_subuniverse. apply truncn_unique.
    apply univalence_axiom.
    exact (BuildEquiv _ _ (subU.(O_unit) (Π1 T)) (O_sheaf_equiv _)).
  Defined.

  Definition O_invol : forall T, (O subU) ( Π1 ((O subU) T)) = O subU T.
    intro T; symmetry; apply O_sheaf.
  Defined.

  Definition subuniverse_struct_transport T U (f : (T.1 <~> U.1)%equiv) :
    (subU.(subuniverse_HProp) T).1 -> (subU.(subuniverse_HProp) U).1.
    apply univalence_axiom in f. apply truncn_unique in f. rewrite f.
    intro x; exact x.
  Defined.
  
  Definition subuniverse_iff_O (T:Trunc n) : 
    IsEquiv (subU.(O_unit) T) = Π1 (subU.(subuniverse_HProp) T).
    apply univalence_hprop. apply hprop_isequiv. apply (Π2 (subU.(subuniverse_HProp) T)).
    split.
    - exact (fun X => subuniverse_struct_transport _ _ (BuildEquiv _ _ _ (isequiv_inverse (H:=X))) (Π2 (subU.(O) T))). 
    - exact (fun X => O_sheaf_equiv (T;X)).
  Defined.

End Reflective_Subuniverse.

Section Reflective_Subuniverse_base_case.
  
  Instance _j (P:HProp) : IsHProp (not (not (Π1 P))).
  repeat (apply trunc_forall; intro). Defined.

  Definition j (P:HProp) := (not (not (Π1 P));_j _).

  Instance _is_classical (P:HProp) : IsHProp (Π1 (j P) -> Π1 P).
  apply (@trunc_forall _ _ (fun _ => P.1)). intro. exact (Π2 P). Defined.  
  
  Definition is_classical (P:HProp) := (Π1 (j P) -> Π1 P ; _is_classical (P:=P)).

  Definition Oj (P:HProp) : {P : HProp & Π1 (is_classical P)}.
    exists (j P). exact (λ X X0, X (λ X1, X1 X0)). Defined.
    
  Definition Oj_unit (P:HProp) : Π1 P -> Π1 (Π1 (Oj P)) := fun x k => k x.

  Definition Oj_equiv (P : Trunc minus_one) (Q : {T : Trunc minus_one & Π1 (is_classical T)}) :
      (Π1 P -> Π1 (Π1 Q)) -> Π1 (Π1 (Oj P)) -> Π1 (Π1 Q).
    intros f jp. apply (Π2 Q). intro notQ. apply jp. intro p. exact (notQ (f p)). Defined.
  
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
  Π1 (nchar_to_sub (Π1 (P:=_) ° Oj)).
  (* {P : HProp & j (Π1 P)} *)



(* Definition True_is_irr (x y : Unit) : x = y. *)
(*   destruct x, y. reflexivity. Defined. *)

(* Instance true_ishprop : IsHProp Unit. *)
(* intros x y. apply BuildContr with (center := True_is_irr x y).  *)
(* intro e. destruct e, x. reflexivity. *)

Definition Oj_J_Contr (χ:J) : Contr ((j χ.1).1).
  apply BuildContr with (center := χ.2).
  intro. apply allpath_hprop.
Defined.

Section Sheafification.

  Variable n0 : trunc_index.

  Definition n := trunc_S n0.

  Variable nj : subuniverse_struct n.

  Variable j_is_nj : forall P, (j P).1 = (nj.(O) (P.1; IsHProp_IsTrunc P.2 n0)).1.1.

  Variable j_is_nj_unit : forall P x ,
             transport idmap (j_is_nj P) (Oj_unit P x) = nj.(O_unit) (P.1; IsHProp_IsTrunc P.2 n0) x.

  Definition E_to_χ_map (T:Trunc (trunc_S n)) E (χ : E -> J) (f : E -> (Π1 T)) : 
    (nchar_to_sub (Π1 ° χ)).1 -> T.1 := f ° Π1.
            
  Definition Snsheaf_struct T := ∀ E (χ : E -> J), IsEquiv (E_to_χ_map T (E:=E) (χ:=χ)). 

  Definition SnType_j_Type := {T : Trunc (trunc_S n) & Snsheaf_struct T}.

  Definition Snsheaf_struct_is_HProp T : IsHProp (Snsheaf_struct T).
    repeat (apply trunc_forall; intro). 
  Defined.

  Definition nj_inter_f (A : Trunc n) (φ : A.1 -> Trunc n) : 
    (nj.(O) ({a:A.1 & (φ a).1}; trunc_sigma (H:= A.2) (H0 := fun a => (φ a).2))).1.1 ->
    (nj.(O) ({a:A.1 & (nj.(O) (φ a)).1.1}; trunc_sigma (H := A.2) (H0 := fun a => (nj.(O) (φ a)).1.2))).1.1.
    apply O_rec. intro. apply nj.(O_unit).
    exact (X.1;nj.(O_unit) _ X.2).
  Defined.

  Definition nj_inter_g (A : Trunc n) (φ : A.1 -> Trunc n) : 
    (nj.(O) ({a:A.1 & (nj.(O) (φ a)).1.1}; trunc_sigma (H := A.2) (H0 := fun a => (nj.(O) (φ a)).1.2))).1.1 ->
    (nj.(O) ({a:A.1 & (φ a).1}; trunc_sigma (H:= A.2) (H0 := fun a => (φ a).2))).1.1.
    apply O_rec. intro.
    (* destruct X as [a φa]. *)
    (* generalize φa; clear φa. apply O_rec. intro φa. *)
    generalize X.2. apply O_rec; intro φa.
    apply nj.(O_unit). exact (X.1;φa).
  Defined.

  (* This remains to be proved *)

  Instance nj_inter_equiv (A : Trunc n) (φ : A.1 -> Trunc n) : IsEquiv (nj_inter_f A φ).
  apply (isequiv_adjointify _ (nj_inter_g A φ)).
  - admit.
  - admit.
  Defined.

  Definition nj_inter (A : Trunc n) (φ : A.1 -> Trunc n) : 
    nj.(O) ({a:A.1 & (φ a).1}; trunc_sigma (H:= A.2) (H0 := fun a => (φ a).2)) =
    nj.(O) ({a:A.1 & (nj.(O) (φ a)).1.1}; trunc_sigma (H := A.2) (H0 := fun a => (nj.(O) (φ a)).1.2)).
    apply unique_subuniverse. apply truncn_unique.
    apply univalence_axiom. exact (BuildEquiv _ _ _ (nj_inter_equiv _ _)).
  Defined.

  Definition nj_fibers_composition A B C (f : A -> B) (g : B -> C) (c : C)
          (HB : ∀ b : B, IsTrunc n (hfiber f b)) (HC : ∀ c : C, IsTrunc n (hfiber g c))
  :
    nj.(O) (hfiber (g°f) c; function_trunc_compo n f g HB HC c) =
    nj.(O) ({ w :  hfiber g c &  (nj.(O) (hfiber f (Π1 w);(HB (Π1 w)))).1.1};
            trunc_sigma (H0:=fun a => (O nj (hfiber f a .1; HB a .1)).1 .2)).
    assert ((hfiber (g ° f) c; function_trunc_compo n f g HB HC c) =
            ({ w : (hfiber g c) & hfiber f (Π1 w) }; trunc_sigma)).
    apply truncn_unique. apply fibers_composition.
    apply (transport (fun X => O nj X = _) (id_sym X)). clear X.
    apply (nj_inter (hfiber g c; HC c) (fun w => (hfiber f w .1; HB w.1))).
  Defined.
    
  Definition type_j_f E (χ: E -> J) :
    (E -> nj.(subuniverse_Type)) -> Π1 (nchar_to_sub (Π1  ° χ))
    -> nj.(subuniverse_Type) := λ α e, α (Π1 e).


  Definition type_j_inv E (χ: E -> J) : (Π1 (nchar_to_sub (Π1  ° χ)) -> nj.(subuniverse_Type)) -> E -> nj.(subuniverse_Type) :=
  λ α e, let f := (Π2 (nchar_to_sub (Π1  ° α))) in
         let m := (Π2 (nchar_to_sub (Π1  ° χ))) in
         nj.(O) (nsub_to_char n ({b : _ &  Π1 (Π1 (α b))}; ((Π1 m) ° (Π1 f); function_trunc_compo n (Π1 f) (Π1 m) (Π2 f) (fun e => IsHProp_IsTrunc (Π2 m e) n0))) e).

  Instance nTjTiSnTjT_eq E (χ : E -> J) : IsEquiv (λ (f : E -> nj.(subuniverse_Type)) (t : {b : E & Π1 (Π1 (χ b))}), f (Π1 t)). 
  apply (isequiv_adjointify _ (type_j_inv (E:=E) (χ := χ))).
  - intro φ.
    unfold type_j_inv, composition. simpl. unfold nchar_to_sub, hfiber, composition in φ; simpl in φ.
    apply functional_extensionality_dep; intro x.
    rewrite (O_sheaf (φ x)).
    repeat apply ap.
    apply truncn_unique.
    eapply concat; try exact (hfiber_pi1 ( (λ t : _, Π1 (Π1 (φ t)))) x).
    symmetry. apply (hfiber_mono (Π1 ) (g:=Π1 )).
    intros X Y. apply subset_is_subobject. intro.
    exact (Π2 (Π1 (χ a))).
  - intro φ.
    unfold type_j_inv, composition. simpl.
    apply functional_extensionality_dep; intro x.
    rewrite (O_sheaf (φ x)).
    unfold nsub_to_char. simpl.
    assert ((hfiber
        (λ t : {b : {b : E | ((χ b) .1) .1} | ((φ b .1) .1) .1}, (t .1) .1) x;
     function_trunc_compo n pr1 pr1
       (nchar_to_sub_compat (λ t : {b : E | ((χ b) .1) .1}, (φ t .1) .1))
       (λ e : E,
        IsHProp_IsTrunc (nchar_to_sub_compat (λ t : E, (χ t) .1) e) n0) x) =
     (hfiber
        (λ t : {b : {b : E | ((φ b) .1) .1} | ((χ b .1) .1) .1}, (t .1) .1) x;
     function_trunc_compo n pr1 pr1
       (λ e : _,
        IsHProp_IsTrunc (nchar_to_sub_compat (λ t : _, (χ (t.1)) .1) e) n0) 
       (nchar_to_sub_compat (λ t : E, (φ t) .1)) x)).
    apply truncn_unique. apply (inter_symm (fun b => ((χ b) .1) .1) (fun b => ((φ b) .1) .1)).
    apply (transport (fun x => O nj x = _ ) (id_sym X)). clear X.
    pose (X := (nj_fibers_composition x (λ e : {b : E | ((φ b) .1) .1},
        IsHProp_IsTrunc
          (nchar_to_sub_compat (λ t : {b : E | ((φ b) .1) .1}, (χ t .1) .1) e)
          n0) (nchar_to_sub_compat (λ t : E, (φ t) .1)))). unfold composition in X.
    apply (transport (fun x => x = _) (id_sym X)). clear X.
  
    apply ap. apply truncn_unique. simpl. etransitivity.
    apply univalence_axiom. apply equiv_sigma_contr.
    intro. pose (f := j_is_nj (hfiber pr1 a .1; 
           (nchar_to_sub_compat (λ t : {b : E | ((φ b) .1) .1}, (χ t .1) .1)
              a .1))). 
    apply (transport (fun X => Contr X) f). 
    simpl.
    apply (transport (fun X => Contr (not (not X))) (id_sym (nhfiber_pi1 _ _))). 
    apply Oj_J_Contr.
    etransitivity. apply nhfiber_pi1. reflexivity.
  Defined.
    
  Lemma nType_j_Type_is_SnType_j_Type : Snsheaf_struct (nj.(subuniverse_Type) ;
                                                        @subuniverse_Type_is_TruncSSn _ nj).
  Proof.
    intros E χ. unfold E_to_χ_map, composition; simpl.
    exact (nTjTiSnTjT_eq _).
  Defined.

  Definition nType_j_Type_sheaf : SnType_j_Type :=
    ((nj.(subuniverse_Type); @subuniverse_Type_is_TruncSSn _ nj);nType_j_Type_is_SnType_j_Type).

  Instance dep_prod_SnType_j_Type_eq
          (A : Type)
          (B : A -> SnType_j_Type)
  : forall (E:Type) (χ : E -> J) (H := λ a, (Π2 (B a)) E χ), IsEquiv
      (λ (f : E -> ∀ a : A, Π1 (Π1 (B a))) (t : {b : E & Π1 (Π1 (χ b))}), f (Π1 t)).
  intros.   
  apply (isequiv_adjointify 
           _ (λ g e a, (@equiv_inv _ _ _ (H a) (λ x, g x a) e))).
  - intro φ.
    apply functional_extensionality_dep; intro x.
    apply functional_extensionality_dep; intro a.
    destruct (H a); simpl in *.
    clear eisadj; clear eissect.
    unfold nchar_to_sub, composition in equiv_inv; simpl.
    unfold Sect, nchar_to_sub, composition, E_to_χ_map, composition in eisretr.
    specialize (eisretr (λ x, φ x a)).
    exact (equal_f _ eisretr x).
  - intro φ.
    apply functional_extensionality_dep; intro x.
    apply functional_extensionality_dep; intro a.
    destruct (H a); simpl in *.
    clear eisadj; clear eisretr.
    unfold nchar_to_sub, composition in equiv_inv; simpl.
    unfold Sect, nchar_to_sub, composition, E_to_χ_map, composition in eissect.
    specialize (eissect (λ x, φ x a)).
    exact (equal_f _ eissect x).
  Defined.

  Definition dep_prod_SnType_j_Type : forall A (B : A -> SnType_j_Type) ,
                                   Snsheaf_struct (forall a, Π1 (Π1 (B a)); 
                    @trunc_forall _ A (fun a => Π1 (Π1 (B a))) (trunc_S n) (fun a => Π2 (Π1 (B a)))).
    intros. 
    exact (dep_prod_SnType_j_Type_eq _).
  Defined.

  Definition closed E (χ : E -> Trunc n) := forall e, IsEquiv (nj.(O_unit) (χ e)).
  
  Definition closed' E A (m : {f : A -> E & forall b:E, IsTrunc n (hfiber f b)}) := closed (nsub_to_char n (A;m)).

  Definition cloture E (χ : E -> Trunc n) : E -> Trunc n := Π1 ° nj.(O) ° χ.
  
  Definition cloture' E A (m : {f : A -> E & forall b:E, IsTrunc n (hfiber f b)}) :=
    nchar_to_sub (cloture (nsub_to_char n (A;m))).

  Definition cloture_is_closed (E :Type) (χ : E -> Trunc n) : closed (cloture χ).
    intro. apply O_sheaf_equiv.
  Defined.

  Lemma cloture_is_closed' (A:Type) (E:Type) (m : {f : A -> E & forall e:E, IsTrunc n (hfiber f e)}) : closed' (Π2 (cloture' m)).
    unfold closed', cloture'. 
    rewrite <- existT_eta.
    pose (f := cloture_is_closed (nsub_to_char n (A; m))). 
    rewrite <- (@nsub_eq_char_retr n _ (cloture (nsub_to_char n (A; m)))) in f.
    exact f.
  Defined.
             
  Definition δ (T:Trunc (trunc_S n)) : ((Π1 T)**(Π1 T)) -> Trunc n.
    intro x. exists (fst x = snd x). apply istrunc_paths.
    exact T.2.
  Defined.
(* := λ x:((Π1 T)**(Π1 T)), (fst x = snd x ; istrunc_paths with (H:=T.2)) *)

  Definition Δ T := (nchar_to_sub (δ T)).

  Definition clδ T := Π1  ° nj.(O) ° (δ T).

  Definition clΔ T := (nchar_to_sub (clδ T)).
  
  Definition separated T :=  ∀ E (χ : E -> J), IsMono (E_to_χ_map T (E:=E) (χ:=χ)).
  
  (**** from type to separated type ****)

  Definition separated_Type (T:Trunc (trunc_S n)) : Type :=
    Im (λ t : Π1 T, λ t', nj.(O) (t = t'; istrunc_paths (H:=Π2 T) (Π1 T) n t t')).
  
  Definition sheaf_is_separated (T : SnType_j_Type) : separated (Π1 T) :=
    fun E χ => equiv_is_mono (Π2 T E χ).

  Definition separated_Type_is_Trunc_Sn (T:Trunc (trunc_S n)) : IsTrunc (trunc_S n) (separated_Type T).
    unfold separated_Type; simpl.
    destruct T as [T TrT]; simpl in *.
    apply (@trunc_sigma _ (fun P => _)). 
    apply (@trunc_forall _ _ (fun P => _)). intro. 
    exact (@subuniverse_Type_is_TruncSSn _ nj).
    intro φ. exact (IsHProp_IsTrunc (istrunc_truncation _ _) n). 
  Defined.

  Definition E_to_χ_map_ap (T U:Trunc (trunc_S n)) E (χ : E -> J) (f : E -> (Π1 T))
             (g : Π1 T -> Π1 U) x y (e : x = y) : 
    apf g (ap (E_to_χ_map T (χ:=χ)) e) = ap (E_to_χ_map U (χ:=χ)) (apf g e).
    destruct e; reflexivity.
  Defined.

  Definition apf_Mono (T U:Type) (f: T -> U) (fMono : IsMonof f) X (x y : X -> T) (e e' : x = y) : 
    apf f e = apf f e' -> e = e'.
    intro. 
    rewrite <- (@eissect _ _ _ (fMono _ _ _) e). 
    rewrite <- (@eissect _ _ _ (fMono _ _ _) e'). exact (ap _ X0). 
  Defined.

  Instance separated_mono_is_separated_ (T U:Trunc (trunc_S n)) E χ g h (f: Π1 T -> Π1 U)
        (H:IsEquiv (ap (E_to_χ_map U (E:=E) (χ:=χ)) (x:=f ° g) (y:=f ° h))) (fMono : IsMonof f) : 
           IsEquiv (ap (E_to_χ_map T (E:=E) (χ:=χ)) (x:=g) (y:=h)).
  apply (isequiv_adjointify _ (fun X => @equiv_inv _ _ _ (fMono E g h) (@equiv_inv _ _ _ H (apf f X)))).
  - intro e. 
    apply (@apf_Mono _ _ _ fMono). 
    unfold equiv_inv.
    pose (E_to_χ_map_ap T U χ g f 
                        (@equiv_inv _ _ _ (fMono _ g h) (@equiv_inv _ _ _ H (apf f e)))).
    apply (transport (fun X => X = _) (id_sym p)). clear p.
    eapply concat; try exact (@eisretr _ _ _ H (apf f e)). 
    apply ap. apply (@eisretr _ _ _ (fMono _ _ _)).
  - intro e. 
    pose (E_to_χ_map_ap T U χ g f e).
    apply (transport (fun X => equiv_inv (equiv_inv X) = _) (id_sym p)).
    apply (transport (fun X => equiv_inv X = _) 
                     (id_sym ((@eissect _ _ _ H (apf f e))))).
    apply eissect.
  Defined.

  Definition separated_mono_is_separated (T U:Trunc (trunc_S n)) (H:separated U) (f: Π1 T -> Π1 U)
             (fMono : IsMonof f) : separated T
 :=
    fun E χ x y => separated_mono_is_separated_ _ (H E χ (f°x) (f°y)) fMono.

  Definition T_nType_j_Type_trunc (T:Trunc (trunc_S n)) : IsTrunc (trunc_S n) (Π1 T -> nj.(subuniverse_Type)).
    apply (@trunc_forall _ _ (fun P => _)). intro. 
    apply (@trunc_sigma _ (fun P => _)). apply Tn_is_TSn.
    intro. apply IsHProp_IsTrunc. exact (Π2 (subuniverse_HProp nj a0)).
  Defined.

  Definition T_nType_j_Type_isSheaf : forall T, Snsheaf_struct (Π1 T -> nj.(subuniverse_Type); 
                                                    T_nType_j_Type_trunc T).
    intro. 
    apply (dep_prod_SnType_j_Type (fun x:Π1 T => ((nj.(subuniverse_Type) ; @subuniverse_Type_is_TruncSSn _ nj);nType_j_Type_is_SnType_j_Type))).
  Defined.

  Definition T_nType_j_Type_sheaf T : SnType_j_Type :=  ((Π1 T -> nj.(subuniverse_Type); T_nType_j_Type_trunc T); T_nType_j_Type_isSheaf _).

  Definition separated_Type_is_separated (T:Trunc (trunc_S n)) : separated (separated_Type T; separated_Type_is_Trunc_Sn (T:=T)).
    apply (@separated_mono_is_separated 
              (separated_Type T;separated_Type_is_Trunc_Sn (T:=T)) 
              (Π1 T -> nj.(subuniverse_Type); T_nType_j_Type_trunc T) 
              (sheaf_is_separated (T_nType_j_Type_sheaf T))
              (Π1 )).
    rewrite IsMonof_isMono. intros x y. apply subset_is_subobject. intro.
    unfold squash. apply istrunc_truncation.
  Defined.

  Definition separation (T:Trunc (trunc_S n)) : {T : Trunc (trunc_S n) & separated T} :=
    ((separated_Type T ; separated_Type_is_Trunc_Sn (T:=T));separated_Type_is_separated (T:=T)).

  Definition separated_unit T :  Π1 T -> separated_Type T := toIm _.

  Definition kernel_pair_separated_is_clΔ T : Π1 (clΔ T) = 
    kernel_pair (toIm (λ t : Π1 T, λ t', nj.(O) (t = t'; istrunc_paths (H:=Π2 T) (Π1 T) n t t'))).
  Admitted.

  Definition separated_equiv : forall (P : Trunc (trunc_S n)) (Q :{T : Trunc (trunc_S n) & separated T}),
                                 IsEquiv (fun f : separated_Type P -> Π1 (Π1 Q) => 
                                           f ° (separated_unit P)).
  Abort.

  (**** From separated to sheaf ****)

  Definition closure_naturality_fun
             (E : Type)
             (F : Type)
             (A : Type)
             (m : A -> E)
             (Trm : forall b : E, IsTrunc n (hfiber m b))
             (Γ : F -> E)
  : {b : F & Π1 (Π1 (nj.(O) ( (hfiber m (Γ b) ; Trm (Γ b)))))} -> {b : F & hfiber (Π1 (P:=λ b0 : E, Π1 (cloture (nsub_to_char n (A; (m; Trm))) b0))) (Γ b)}
    := λ X, (Π1 X ; (((Γ (Π1 X) ; O_rec (hfiber m (Γ (Π1 X)); Trm (Γ (Π1 X)))
                        (nj.(O) (nsub_to_char n (A; (m; Trm)) (Γ (Π1 X))))
                        (λ Hb : Π1 (hfiber m (Γ (Π1 X)); Trm (Γ (Π1 X))),
                                nj.(O_unit) (nsub_to_char n (A; (m; Trm)) (Γ (Π1 X))) Hb) 
                        (Π2 X))) ; idpath)).

  Definition closure_naturality_inv
             (E : Type)
             (F : Type)
             (A : Type)
             (m : A -> E)
             (Trm : ∀ b : E, IsTrunc n (hfiber m b))
             (Γ : F -> E)
  : {b : F & hfiber (Π1 (P:=λ b0 : E, Π1 (cloture (nsub_to_char n (A; (m; Trm))) b0))) (Γ b)} -> {b : F & Π1 (Π1 (nj.(O) ( (hfiber m (Γ b) ; Trm (Γ b)))))}.
    intro X; exists (Π1 X).
    generalize (Π2 (Π1 (Π2 X))); apply O_rec; intro HHb; apply nj.(O_unit).
    destruct (Π2 (Π2 X)); exact HHb.
  Defined.

  Definition closure_naturality_retr
             (E : Type)
             (F : Type)
             (A : Type)
             (m : A -> E)
             (Trm : ∀ b : E, IsTrunc n (hfiber m b))
             (Γ : F -> E)
  : Sect (closure_naturality_inv Trm Γ) (closure_naturality_fun Trm Γ).
    intro X; unfold closure_naturality_fun, closure_naturality_inv; simpl.
    destruct X as [b Hb]; simpl.
    apply eq_dep_sumT with (prf := idpath); simpl.
    destruct Hb as [[b0 Hb0] eq]; simpl in *.
    destruct eq.

    pose (rew1 := equal_f _ (eissect _ (IsEquiv := (nj.(O_equiv) (nsub_to_char n (A; (m; Trm)) b0) (nj.(O) (existT (IsTrunc n) (hfiber m b0) (Trm b0))))) (λ x, x)) ( equiv_inv (IsEquiv := O_equiv nj (hfiber m b0; Trm b0)
                (O nj (nsub_to_char n (A; (m; Trm)) b0))) (λ t : hfiber m b0, O_unit nj (hfiber m b0; Trm b0) t) Hb0)).

    pose (rew2 := equal_f _ (eissect _ (IsEquiv := nj.(O_equiv) (hfiber m b0; Trm b0) (nj.(O) (nsub_to_char n (A; (m; Trm)) b0))) (λ x, x)) Hb0).

    unfold nsub_to_char, hfiber, composition in *; simpl in *.

    unfold O_rec; simpl.
    apply eq_dep_sumT with (prf := (eq_dep_sumT (λ x, _) _ (idpath b0) (rew1 @ rew2))). 
    destruct (rew1 @ rew2); simpl. reflexivity.
  Defined.

  Definition closure_naturality_sect
             (E : Type)
             (F : Type)
             (A : Type)
             (m : A -> E)
             (Trm : ∀ b : E, IsTrunc n (hfiber m b))
             (Γ : F -> E)
  : Sect (closure_naturality_fun Trm Γ) (closure_naturality_inv Trm Γ).
    intro X; unfold closure_naturality_fun; simpl.
    destruct X as [b Hb]; simpl.
    apply eq_dep_sumT with (prf := idpath); simpl.
    unfold O_rec.

    pose (rew1 := equal_f _ (eissect _ (IsEquiv := nj.(O_equiv) (hfiber m (Γ b); Trm (Γ b))
             (nj.(O) (nsub_to_char n (A; (m; Trm)) (Γ b)))) (λ x, x))
                         (equiv_inv (IsEquiv := O_equiv nj (nsub_to_char n (A; (m; Trm)) (Γ b))
          (O nj (hfiber m (Γ b); Trm (Γ b))))
        (λ Hb0 : hfiber m (Γ b),
         O_unit nj (nsub_to_char n (A; (m; Trm)) (Γ b)) Hb0) Hb)
         ).

    pose (rew2 := equal_f _ (eissect _ (IsEquiv := O_equiv nj (nsub_to_char n (A; (m; Trm)) (Γ b))
          (O nj (hfiber m (Γ b); Trm (Γ b)))) (λ x, x)) Hb).
    
    exact (rew1 @ rew2).
  Defined.

  Definition closure_naturality E F A (m : {f : A -> E & forall b:E, IsTrunc n (hfiber f b)}) (Γ : F -> E) :
    {b : F & Π1 (Π1 (nj.(O) ((hfiber (Π1 m) (Γ b)) ; (Π2 m) (Γ b))))} = {b : F & hfiber (Π1 (Π2 (cloture' m))) (Γ b)}.
    destruct m as [m Trm]; simpl.
    apply univalence_axiom.
    exists (closure_naturality_fun _ _).
    apply (isequiv_adjointify _ _ (closure_naturality_retr _ _) (closure_naturality_sect _ _)).
  Defined.

  Definition cloture_fun
        (E : Type)
        (P : E -> J)
        (Q : E -> Trunc n)
        (f : forall e:E, (P e).1.1 -> (Q e).1)
  : {e:E | (nj.(O) (Π1 (Π1 (P e)); IsHProp_IsTrunc (Π2 (Π1 (P e))) n0)).1.1} -> {e:E | (nj.(O) (Q e)).1.1}
    := (λ b, (Π1 b;
              O_rec (Π1 (Π1 (P (Π1 b))); IsHProp_IsTrunc (Π2 (Π1 (P (Π1 b)))) n0)
                    (nj.(O) (Q (Π1 b)))
                    (λ X2 : Π1 (Π1 (P (Π1 b))),
                            nj.(O_unit) (Q (Π1 b)) (f (b.1) X2))
                    (Π2 b))).
    
  Definition cloture_fun_restriction
        (E : Type)
        (P : E -> J)
        (Q : E -> Trunc n)
        (f : forall e:E, (P e).1.1 -> (Q e).1)
  :forall (e : {e:E | (P e).1.1}), Π2 (cloture_fun P Q f (Π1 e; nj.(O_unit) (Π1 (Π1 (P (Π1 e))); IsHProp_IsTrunc (Π2 (Π1 (P (Π1 e)))) n0) (Π2 e))) = nj.(O_unit) (Q (Π1 e)) ((f (Π1 e) (Π2 e)))
    := λ e, equal_f _ (eisretr _ (IsEquiv := (O_equiv nj (((P e .1) .1) .1; IsHProp_IsTrunc ((P e .1) .1) .2 n0) (O nj (Q e .1)))) (λ X, nj.(O_unit) _ (f _ X))) (e.2).

  Lemma cloture_fun_
        (E : Type)
        (P : E -> J)
        (Q : E -> Trunc n)
        (f : forall e:E, (P e).1.1 -> (Q e).1)
        (g : forall e:E, (nj.(O) (Π1 (Π1 (P e)); IsHProp_IsTrunc (Π2 (Π1 (P e))) n0)).1.1)
        (h : forall e:E, (Q e).1)
        (H : forall e:E, forall X:(P e).1.1, f e X = h e)
  : forall (e:E), Π2 (cloture_fun P Q f (e; g e)) = nj.(O_unit) (Q e) (h e).
    intro e.
    pose (foo := equal_f _ (eissect _ (IsEquiv := O_equiv nj (((P e) .1) .1; IsHProp_IsTrunc ((P e) .1) .2 n0)
          (O nj (Q e))) (λ _, O_unit nj (Q e) (h e))) (g e)); simpl in foo.
    assert ((λ X2 : ((P e) .1) .1, O_unit nj (Q e) (f e X2)) = (λ X2 : ((P e) .1) .1, O_unit nj (Q e) (h e))).
      apply functional_extensionality_dep; intro X2.
      rewrite <- H  with (X := X2).
      exact idpath.
    apply (transport _ foo).
    exact (equal_f _ (ap (equiv_inv (IsEquiv := O_equiv nj (((P e) .1) .1; IsHProp_IsTrunc ((P e) .1) .2 n0)
          (O nj (Q e)))) X) (g e)).
  Defined.

  Definition E_to_Y'A
             (A : Trunc (trunc_S n))
             (B : SnType_j_Type)
             (m : Π1 A -> Π1 (Π1 B))
             (X1 : ∀ b : Π1 (Π1 B), IsTrunc n (hfiber m b))
             (closed0 : closed' (m; X1))
             (E : Type)
             (χ : E -> J)
             (X : {b : E & Π1 ((Π1 (P:=λ b0 : HProp, ~ ~ Π1 b0) ° χ) b)} -> Π1 A)
             (X0 : E)
             (inv_B : (Π1
                         (nchar_to_sub
                            (Π1
                               (P:=λ b : HProp,
                                         Π1 ((Π1 (P:=λ P : HProp, Π1 (is_classical P)) ° Oj) b))
                               ° χ)) -> Π1 (Π1 B)) -> E -> Π1 (Π1 B))
             (retr_B : Sect inv_B (E_to_χ_map (Π1 B) (χ:=χ)))
             (Y := inv_B (m ° X) : E -> Π1 (Π1 B))
    := (λ b, (Π1 b ; (X b ; (id_sym (equal_f _ (retr_B (m°X)) b)))))  : {b : E & Π1 (Π1 (χ b))} -> {b : E & hfiber m (Y b)}.

  Definition clE_to_clY'A
             (A : Trunc (trunc_S n))
             (B : SnType_j_Type)
             (m : Π1 A -> Π1 (Π1 B))
             (X1 : ∀ b : Π1 (Π1 B), IsTrunc n (hfiber m b))
             (closed0 : closed' (m; X1))
             (E : Type)
             (χ : E -> J)
             (X : {b : E & Π1 ((Π1 (P:=λ b0 : HProp, ~ ~ Π1 b0) ° χ) b)} -> Π1 A)
             (X0 : E)
             (inv_B : (Π1
                         (nchar_to_sub
                            (Π1
                               (P:=λ b : HProp,
                                         Π1 ((Π1 (P:=λ P : HProp, Π1 (is_classical P)) ° Oj) b))
                               ° χ)) -> Π1 (Π1 B)) -> E -> Π1 (Π1 B))
             (retr_B : Sect inv_B (E_to_χ_map (Π1 B) (χ:=χ)))
             (Y := inv_B (m ° X) : E -> Π1 (Π1 B))

    := cloture_fun χ (λ x, (hfiber m (Y x); X1 (Y x))) (λ e p, Π2 (E_to_Y'A _ _ closed0 _ X0 retr_B (e;p)))
:
         {b:E & Π1 (Π1 (nj.(O) (Π1 (Π1 (χ b)); IsHProp_IsTrunc (Π2 (Π1 (χ b))) n0)))} -> {b : E & Π1 (Π1 (nj.(O) (hfiber m (Y b) ; X1 (Y b))))}.

  Lemma equalΠ2_restriction_χ
        (A : Trunc (trunc_S n))
        (B : SnType_j_Type)
        (m : Π1 A -> Π1 (Π1 B))
        (X1 : ∀ b : Π1 (Π1 B), IsTrunc n (hfiber m b))
        (closed0 : closed' (m; X1))
        (E : Type)
        (χ : E -> J)
        (X : {b : E & Π1 ((Π1 (P:=λ b0 : HProp, ~ ~ Π1 b0) ° χ) b)} -> Π1 A)
        (X0 : E)
        (inv_B : (Π1
                    (nchar_to_sub
                       (Π1
                          (P:=λ b : HProp,
                                    Π1 ((Π1 (P:=λ P : HProp, Π1 (is_classical P)) ° Oj) b))
                          ° χ)) -> Π1 (Π1 B)) -> E -> Π1 (Π1 B))
        (retr_B : Sect inv_B (E_to_χ_map (Π1 B) (χ:=χ)))
        (Y := inv_B (m ° X) : E -> Π1 (Π1 B))
  : forall (b : {e : E & Π1 (Π1 (χ e))}), 
      Π2 (clE_to_clY'A _ _ closed0 _ X0 retr_B (Π1 b ; nj.(O_unit) (Π1 (Π1 (χ (Π1 b))); IsHProp_IsTrunc (Π2 (Π1 (χ (Π1 b)))) n0) (Π2 b))) = O_unit nj ({x : Π1 A & m x = Y (Π1 b)}; X1 (Y (Π1 b))) (Π2 (E_to_Y'A _ _ closed0 _ X0 retr_B b)).
  Proof.
    unfold clE_to_clY'A. intro b.
    pose (foo := cloture_fun_restriction χ (λ x, (hfiber m (Y x); X1 (Y x))) (λ e p, Π2 (E_to_Y'A _ _ closed0 _ X0 retr_B (e;p))) b).
    unfold Y, hfiber, composition in *.
    rewrite (existT_eta (A:=E) (P:=λ x, ((χ x) .1) .1) b).
    apply foo.
  Defined.

  Lemma ap_equalf (A B C:Type) (x y : C -> B) (a : A) eq (φ : A -> C): (equal_f _ (ap (x:=x) (y:=y) (λ (f : C -> B), λ (t:A), f (φ t)) eq)) a = equal_f _ eq (φ a).
    destruct eq; simpl. exact idpath.
  Qed.
  
  Definition closed_to_sheaf_inv
             (A : Trunc (trunc_S n))
             (B : SnType_j_Type)
             (m : {f : Π1 A -> Π1 (Π1 B) & ∀ b : Π1 (Π1 B), IsTrunc n (hfiber f b)})
             (closed : closed' m)
             (E : Type)
             (χ : E -> J)
             (eq := (Π2 B) E χ)
  : ((nchar_to_sub (pr1 ° χ)) .1 -> A .1) -> (E -> A .1).
    intros X X0.
    destruct ((Π2 B) E χ) as [inv_B retr_B sect_B adj_B].
    pose (X2:=Π2 (χ X0)). apply (transport idmap  (j_is_nj (((χ X0) .1)))) in X2.
    destruct (closed (inv_B ((Π1 m)°X) X0)) as [inv_closed retr_closed sect_closed adj_closed].
    
    exact ((Π1 (P:=_) ° inv_closed) (Π2 (Π1 (Π2 (closure_naturality_fun _ _ (@clE_to_clY'A A B (Π1 m) (Π2 m) closed E χ X X0 inv_B retr_B (X0;X2))))))).
  Defined.

  Definition closed_to_sheaf_retr 
             (A : Trunc (trunc_S n))
             (B : SnType_j_Type)
             (m : {f : Π1 A -> Π1 (Π1 B) & ∀ b : Π1 (Π1 B), IsTrunc n (hfiber f b)})
             (closed : closed' m)
             (E : Type)
             (χ : E -> J)
             (eq := (Π2 B) E χ)

  : Sect (@closed_to_sheaf_inv A B m closed E χ) (E_to_χ_map A (χ:=χ)).
    intro X.
    destruct m as [m Trm].
    apply functional_extensionality_dep; intro b.
    unfold closed_to_sheaf_inv, E_to_χ_map, nsub_to_char, composition, hfiber, O_rec, Equivalences.internal_paths_rew in *; simpl in *.

    destruct (@projT2 (Trunc (trunc_S n))
         (fun T : Trunc (trunc_S n) => Snsheaf_struct T)
         B E χ) as [inv_B retr_B sect_B adj_B].

    destruct (closed (inv_B (λ t : {b0 : E & Π1 (Π1 (P:= (λ b1:HProp, ~ ~ (Π1 b1))) (χ b0))}, m (X t)) (Π1 b))) as [inv_closed retr_closed sect_closed adj_closed].

    pose (rew1 := equal_f _ (eissect _ (IsEquiv :=
                                        nj.(O_equiv)
                                             ({x : Π1 A &
                                                   m x =
                                                   inv_B (λ t : {b0 : E & Π1 (Π1 (χ b0))}, m (X t)) (Π1 b)};
                Trm (inv_B (λ t : {b0 : E & Π1 (Π1 (χ b0))}, m (X t)) (Π1 b)))
                (nj.(O)
                   (nsub_to_char n (Π1 A; (m; Trm))
                                 (inv_B (λ t : {b0 : E & Π1 (Π1 (χ b0))}, m (X t))
                                        (Π1 b))))) (λ x, x))).
    unfold Sect, E_to_χ_map, nsub_to_char, hfiber, O_rec, composition in *; simpl in *.
    rewrite rew1; clear rew1.

    pose (foo := (@equalΠ2_restriction_χ A B m Trm closed E χ X (Π1 b) inv_B retr_B b)).
    unfold clE_to_clY'A, E_to_Y'A, O_rec, hfiber, composition in foo; simpl in foo.
    unfold Sect, E_to_χ_map, nsub_to_char, hfiber, O_rec, composition in *; simpl in *.

    pose (bar := j_is_nj_unit ((χ b .1) .1) (b.2)).
    unfold Oj_unit, transport, Sect, E_to_χ_map, nsub_to_char, hfiber, O_rec, composition in *; simpl in *.
    
    assert ((λ k : ~ ((χ b .1) .1) .1, k b .2) = (χ b .1) .2).
      apply functional_extensionality_dep; intro x.
      destruct ((χ b .1) .2 x).

    assert (fooo := transport (λ x,  match j_is_nj (χ b .1) .1 in (_ = a) return a with
                                       | 1%path => x
                                     end =
                                     O_unit nj (((χ b .1) .1) .1; IsHProp_IsTrunc ((χ b .1) .1) .2 n0)
                                            b .2) X0 bar).
    simpl in fooo.
    rewrite <- fooo in foo.
    
    apply transport with (x := O_unit nj ({x : A .1 | m x = inv_B (λ t, m (X t)) b .1};
                                          Trm (inv_B (λ t : {b : E | ((χ b) .1) .1}, m (X t)) b .1))
                                      (X b; id_sym (equal_f (λ _, (B .1) .1) (retr_B (λ t, m (X t))) b)))
                         (y:=_).
   
    exact (id_sym foo).
    rewrite sect_closed.
    exact idpath.
  Defined.

  Definition closed_to_sheaf_sect
             (A : Trunc (trunc_S n))
             (B : SnType_j_Type)
             (m : {f : Π1 A -> Π1 (Π1 B) & ∀ b : Π1 (Π1 B), IsTrunc n (hfiber f b)})
             (closed : closed' m)
             (E : Type)
             (χ : E -> J)
             (eq := (Π2 B) E χ)

  : Sect (E_to_χ_map A (χ:=χ)) (@closed_to_sheaf_inv A B m closed E χ).
    destruct m as [m Trm].
    intro X; unfold closed_to_sheaf_inv; simpl in *.
    apply functional_extensionality_dep; intro b.
    unfold E_to_χ_map, nsub_to_char, composition, hfiber, O_rec in *; simpl in *.
    destruct (@projT2 (Trunc (trunc_S n))
         (fun T : Trunc (trunc_S n) => Snsheaf_struct T)
         B E χ) as [inv_B retr_B sect_B adj_B].
    destruct (closed (inv_B (λ t : {b0 : E & Π1 (Π1 (P:= (λ b1:HProp, ~ ~ (Π1 b1))) (χ b0))}, m (X (Π1 t))) b)) as [inv_closed retr_closed sect_closed adj_closed].

    rewrite (equal_f _ (eissect _ (IsEquiv :=
                             nj.(O_equiv)
                                  ({x : Π1 A &
                                        m x =
                                        inv_B (λ t : {b0 : E & Π1 (Π1 (χ b0))}, m (X (Π1 t))) b};
                                   Trm (inv_B (λ t : {b0 : E & Π1 (Π1 (χ b0))}, m (X (Π1 t))) b))
                                  (nj.(O)
                                        (nsub_to_char n (Π1 A; (m; Trm))
                      (inv_B (λ t : {b0 : E & Π1 (Π1 (χ b0))}, m (X (Π1 t)))
                         b)))) (λ x, x))).

    pose (foo := equal_f _ (sect_B (m°X))). 
    set (Y := inv_B (m ° (X ° pr1) ) : E -> Π1 (Π1 B)).

    apply transport with
      (x := O_unit nj ({x : A .1 | m x = Y b}; Trm (Y b)) (X b; id_sym (foo b))) (y:=_).
  
    unfold E_to_χ_map, nsub_to_char, hfiber, O_rec, Y, composition in *; simpl in *.
   
    pose (h := (λ e, (X e; id_sym (foo e))) : ∀ e : E, {x : A .1 | m x = inv_B (λ t : {b : E | ((χ b) .1) .1}, m (X t .1)) e}).
    assert ((∀ (e : E) (X0 : ((χ e) .1) .1),
          (X e;
           id_sym
             (equal_f (λ _ : {b : E | ((χ b) .1) .1}, (B .1) .1)
                      (retr_B (λ t : {b : E | ((χ b) .1) .1}, m (X t .1)))
                      (e; X0))) = h e)).
      intros; unfold h, foo. apply eq_dep_sumT with (prf := idpath); simpl.
      apply ap.
      clear eq; specialize (adj_B (m°X)); unfold composition in adj_B; rewrite adj_B; clear adj_B.
      exact (@ap_equalf {b0 : E | ((χ b0) .1) .1} ((B .1) .1) E (inv_B (λ t : {b : E | ((χ b) .1) .1}, (λ t0 : E, m (X t0)) t .1)) (λ t : E, m (X t)) (e;X0) (sect_B (λ t : E, m (X t))) pr1).

    exact (id_sym (@cloture_fun_ E χ (λ x, (hfiber m (Y x); Trm (Y x))) (λ e p, Π2 (E_to_Y'A _ _ closed _ b retr_B (e;p))) (λ b, match j_is_nj (χ b) .1 in (_ = y) return y with | 1%path => (χ b) .2 end) h X0 b)).
    
    rewrite sect_closed.
    exact idpath.
  Defined.

  Definition closed_to_sheaf (A:Trunc (trunc_S n)) (B:SnType_j_Type) (m : {f : (Π1 A) -> (Π1 (Π1 B)) & forall b, IsTrunc n (hfiber f b)})
  : closed' m  -> Snsheaf_struct A := λ x, λ E χ, isequiv_adjointify _ (@closed_to_sheaf_inv A B m x E χ) (@closed_to_sheaf_retr A B m x E χ) (@closed_to_sheaf_sect A B m x E χ).


  Definition mono_is_hfiber (T U : Type) (m : T -> U) (Monom : IsMono m) :
    ∀ b , IsTrunc n (hfiber m b).
    intro. apply IsHProp_IsTrunc.
    apply (IsMono_IsHProp_fibers Monom).
  Defined.

  Definition separated_to_sheaf_Type (T U: Type) (m : T -> U) (Monom : IsMono m) : Type  :=
    Π1 (cloture' (m; mono_is_hfiber Monom)).    
  
  Definition separated_to_sheaf_IsTrunc_Sn (T U : Trunc (trunc_S n)) m Monom :
    IsTrunc (trunc_S n) (@separated_to_sheaf_Type T.1 U.1 m Monom).
    apply (@trunc_sigma _ (fun P => _)).
    exact (U.2).
    intro a.
    apply (@trunc_succ _ _).
    exact (Π2 (Π1 (nj.(O) (nsub_to_char n (T.1; (m ; mono_is_hfiber Monom)) a)))).
  Defined.
  
  Definition separated_to_sheaf (T:{T : Trunc (trunc_S n) & separated T}) (U:SnType_j_Type) m Monom :
     Snsheaf_struct (@separated_to_sheaf_Type T.1.1 U.1.1 m Monom; @separated_to_sheaf_IsTrunc_Sn _ _ m Monom).
    pose (foo := closed_to_sheaf (separated_to_sheaf_Type (m:=m) Monom; (@separated_to_sheaf_IsTrunc_Sn _ _ m  Monom)) U).
    unfold separated_to_sheaf_Type in *; simpl in *.

    specialize (foo (Π2 (cloture' (m;mono_is_hfiber Monom)))).
    apply foo.

    apply cloture_is_closed'.
  Defined.

  Definition IsMono_fromIm_inv {A B} (f : A -> B) (x y : Im f): x.1 = y.1 -> x=y.
    intro X.
    rewrite existT_eta with (t:=x); rewrite existT_eta with (t:=y).
    apply eq_dep_sumT with (prf := X).
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

  Definition sheafification_Type (T:Trunc (trunc_S n)) :=
    @separated_to_sheaf_Type (separated_Type T) 
                             (T.1 -> nj.(subuniverse_Type)) (fromIm (f:=_)) 
                             (IsMono_fromIm (f:=_)).

  Definition sheafification_istrunc (T:Trunc (trunc_S n)) : 
    IsTrunc (trunc_S n) (sheafification_Type T).
    apply (separated_to_sheaf_IsTrunc_Sn (separated_Type T; separated_Type_is_Trunc_Sn (T:=T)) 
                              (T.1 -> nj.(subuniverse_Type); T_nType_j_Type_trunc T)).
  Defined.

  Definition sheafification_trunc (T:Trunc (trunc_S n)) : Trunc (trunc_S n) :=
    (sheafification_Type T ; sheafification_istrunc  (T:=T)). 

  Definition sheafification_ (T:Trunc (trunc_S n)) : Snsheaf_struct (sheafification_trunc T) :=
    separated_to_sheaf (separated_Type T; separated_Type_is_Trunc_Sn (T:=T)) (T_nType_j_Type_sheaf T) (IsMono_fromIm (f:=_)).

  Definition sheafification (T:Trunc (trunc_S n)) : SnType_j_Type :=
    ((sheafification_Type T ; sheafification_istrunc  (T:=T)); sheafification_ T).

  