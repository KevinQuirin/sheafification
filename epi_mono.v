Require Export Utf8_core.
Require Import HoTT TruncType.
Require Import hit.Connectedness hit.Truncations.

Set Universe Polymorphism.

Local Open Scope path_scope.
(* Local Open Scope equiv_scope. *)

Section Images.

  (* Definition 3 *)
  Definition Im {A B} (f : A -> B) := {b : B & Trunc (-1) (hfiber f b)}.

  Definition toIm {A B} (f : A -> B) : A -> Im f := fun a => (f a; tr (a;idpath)).

  Definition fromIm {A B} (f : A -> B) : Im f -> B := fun im => pr1 im.
  
End Images.

Section Embeddings.

  (* In this section, we define IsEmbedding two other way, then prove that they are all three equivalent *)
  Context `{fs: Funext}.

  Definition IsMono {A B : Type} (f : A -> B)
    := forall x y, IsEquiv (ap f (x:=x) (y:=y)).

  Definition IsMonof {A B : Type} (f : A -> B)
    := forall (X:Type) (x y : X -> A), IsEquiv (ap (fun u => f o u) (x:=x) (y:=y)).

  Lemma IsEmbedding_IsMono {A B : Type} (f : A -> B)
    : IsEmbedding f <-> IsMono f.
    split.
    - intros H x y.
      apply isequiv_fcontr. intro q.
      pose (Y := equiv_path_hfiber (x;1) (y;q^)); cbn in Y.
      simple refine (contr_equiv' (∃ q0 : x = y, 1 = ap f q0 @ q^) _).
      simple refine (equiv_functor_sigma_id _); intro a.
      pose (ff:= (equiv_inverse (BuildEquiv _ _ _ (isequiv_moveL_pV q 1 (ap f a))))).
      rewrite concat_1p in ff.
      exact (equiv_compose' (equiv_path_inverse q (ap f a)) ff).
      simple refine (@contr_equiv' ((x; 1) = (y; q^)) _ (equiv_inverse Y) _).
    - intros H b x y; simpl. pose (Y:=equiv_path_hfiber x y).
      simple refine (@contr_equiv' _ _ Y _).
      pose (fcontr_isequiv (ap f) (H x.1 y.1) (x.2@y.2^)).
      match goal with
      |[ i : Contr ?AA |- Contr ?BB ] => assert (X: AA <~> BB)
      end.
      simple refine (equiv_functor_sigma_id _); intro a.
      pose (ff:= (equiv_inverse (BuildEquiv _ _ _ (isequiv_moveL_pV y.2 (ap f a) x.2)))).
      exact (equiv_compose' (equiv_path_inverse (ap f a @ y.2) x.2) ff).
      simple refine (@contr_equiv' _ _ X _).
  Qed.
  
  Definition IsMonof_to_isMono {A B : Type} (f : A -> B) : IsMonof f -> IsMono f.
    intro H. intros x y.
    unfold IsMonof in H.
    specialize (H A). specialize (H (fun _ => x) (fun _ => y)).
    destruct H as [inv retr sect _]. 
    simple refine (isequiv_adjointify _ _ _ _).
    - intro H.
      simple refine (apD10 (f := λ _, x) (g := λ _, y) (inv _) _).
      apply path_forall; intro u; exact H. exact x.
    - intro u.
      etransitivity; try exact (ap10_ap_postcompose f (g:=(λ _ : A, x)) (g' := (λ _ : A, y)) (inv (path_forall (λ _ : A, f x) (λ _ : A, f y) (λ _ : A, u))) x)^.
      rewrite retr.
      unfold ap10. unfold path_forall.
      rewrite eisretr.
      reflexivity.
    - intro u. destruct u; simpl in *. 
      rewrite path_forall_1.
      apply (transport (fun u => ap10 u x = 1) (sect 1)^).
      reflexivity.
  Defined.

  Definition IsMono_to_IsMonof {A B : Type} (f : A -> B) : IsMono f -> IsMonof f.
    intro H.
    intros X a b.
    pose (φ := fun p => path_forall a b (fun x => equiv_inv (IsEquiv := H (a x) (b x)) (ap10 p x))).
    apply isequiv_adjointify with (g:= φ).
    - intro p.
      unfold φ.
      apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
      apply path_forall; intro u. 
      apply (transport (λ U, U = ap10 p u) (ap10_ap_postcompose f _ u)^).
      unfold ap10 at 1, path_forall. rewrite eisretr. rewrite eisretr. reflexivity.
    - intro p; unfold φ; destruct p. simpl.
      pose (foo := path_forall _ _ (fun y =>  (@eissect _ _ _ (H (a y) (a y)) idpath))).
      simpl in foo. rewrite foo.
      apply path_forall_1.
  Qed.

  
  Definition apf_Mono {T U : Type} (f: T -> U) (fMono : IsMonof f) X (x y : X -> T) (e e' : x = y) : 
    ap (fun u => f o u) e = ap (fun u => f o u) e' -> e = e'.
    intro. 
    rewrite <- (@eissect _ _ _ (fMono _ _ _) e). 
    rewrite <- (@eissect _ _ _ (fMono _ _ _) e'). exact (ap _ X0). 
  Defined.

  
  Lemma compose_equiv {A B C D:Type} (φ : A -> B) (u v : B -> C) (f : C -> D)
        (equiv_compose_φ : IsEquiv (ap (λ x, x o φ) (x:= f o u) (y := f o v)))
        (Mono_f : IsMono f)
    : IsEquiv (ap (λ x, x o φ) (x:=u) (y:=v)).
  Proof.
    pose (Monof_f := IsMono_to_IsMonof f Mono_f).
    unfold IsMonof in *; simpl in *.

    pose (e1 := (Monof_f B u v)).
    pose (e2 := (equiv_compose_φ)).
    pose (e3 := @isequiv_inverse _ _ _ (Monof_f A (u o φ) (v o φ))).

    assert (X: ((ap (λ u0 : A → C, f o u0))^-1 o (ap (λ x : B → D, x o φ) o (ap (λ u0 : B → C, f o u0) (x:=u) (y:=v)))) = (ap (λ x : B → C, x o φ))).
    apply path_forall; intro p.
    apply (@equiv_inj _ _ _ (Monof_f A (u o φ) (v o φ))). rewrite eisretr.
    destruct p; reflexivity.

    destruct X. exact (@isequiv_compose _ _ _ (@isequiv_compose _ _ _ e1 _ _ e2) _ _ e3).
  Qed.
  
End Embeddings.

Section Surjections.

  (* Some lemmas about surjections *)
  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  Lemma IsSurjection_toIm (X Y:Type) (f:X -> Y)
  : IsSurjection (toIm f).
    apply BuildIsSurjection.
    intros [b p]; generalize dependent p.
    apply Trunc_ind.
    intro a; apply istrunc_truncation.
    intros [a p].
    apply tr.
    exists a. apply path_sigma' with p.
    apply path_ishprop.
  Defined.

  Lemma epi_prod (W X Y Z:Type) (f:X -> Y) (g:W -> Z) (epif : IsSurjection f) (epig : IsSurjection g)
  : IsSurjection (λ x, (f (fst x), g (snd x))).
  Proof.
    apply BuildIsSurjection.
    intros [y z]. 
    specialize (epif y); specialize (epig z).
    generalize dependent (center _ (Contr_internal := epif)); apply Trunc_ind; intro x; try apply istrunc_truncation.
    generalize dependent (center _ (Contr_internal := epig)); apply Trunc_ind; intro w; try apply istrunc_truncation.
    apply tr.
    exists (x.1,w.1). simpl.
    apply path_prod; [exact x.2 | exact w.2].
  Qed.

  Lemma epi_two_out_of_three_1 (A B C:Type) (f:A -> B) (g:B -> C) (h : A -> C) (π : forall a,  g (f a) = h a)
  : IsSurjection f -> IsSurjection g -> IsSurjection h.
    intros Ef Eg.
    apply BuildIsSurjection.
    intros c. 
    generalize dependent (@center _ (Eg c)).
    apply Trunc_rec. intros [b p].
    generalize dependent (@center _ (Ef b)).
    apply Trunc_rec. intros [a q].
    apply tr.
    exists a.
    rewrite <- (π a).
    rewrite q.
    exact p.
  Qed.

  Lemma epi_two_out_of_three_2 (A B C:Type) (f:A -> B) (g:B -> C) (h : A -> C) (π : forall a,  g (f a) = h a)
  : IsSurjection f -> IsSurjection h -> IsSurjection g.
    intros Ef Eh.
    apply BuildIsSurjection.
    intros c. 
    generalize dependent (@center _ (Eh c)).
    apply Trunc_rec. intros [a p].  
    apply tr.
    exists (f a).
    exact ((π a) @ p).
  Qed.
    
       
  Definition IsEpi A B (f:A -> B)
    := forall C:Type, forall (x y : B -> C) , IsEquiv (ap (fun u => u o f) (x:=x) (y:=y)).

End Surjections.

