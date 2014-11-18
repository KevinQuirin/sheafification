Require Export Utf8_core.
Require Import HoTT TruncType.
Require Import hit.Connectedness hit.Truncations.
Require Import univalence lemmas.

Set Universe Polymorphism.
Set Implicit Arguments.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

Section Images.
  
  Definition Im {A B} (f : A -> B) := {b : B & Trunc (-1) (hfiber f b)}.

  Definition toIm {A B} (f : A -> B) : A -> Im f := fun a => (f a; tr (a;idpath)).

  Definition fromIm {A B} (f : A -> B) : Im f -> B := fun im => pr1 im.
  
End Images.

Section Embeddings.

  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  Definition IsMono (A B : Type) (f : A -> B) := forall x y, IsEquiv (ap f (x:=x) (y:=y)).

  Definition IsMonof (A B : Type) (f : A -> B) := forall (X:Type) (x y : X -> A), 
                                                    IsEquiv (ap (fun u => f o u) (x:=x) (y:=y)).

  Lemma IsEmbedding_IsMono (A B : Type) (f : A -> B)
  : IsEmbedding f <-> IsMono f.
    
    assert (forall b:B, forall x y:hfiber f b, (x=y) = (hfiber (ap f) (x.2 @ y.2^))).
    { intros u [x p] [y q]. simpl.
      etransitivity; try exact (L425 (x;p) (y;q)).
      apply path_universe_uncurried. unfold hfiber.
      exists ((λ r, (r.1; moveL_pV q (ap f r.1) p r.2)) : (∃ r : x = y, ap f r @ q = p) -> (∃ x0 : x = y, ap f x0 = p @ q ^)).
      apply isequiv_adjointify with (g := (λ r, (r.1; moveR_pM q p (ap f r.1) r.2)) : (∃ x0 : x = y, ap f x0 = p @ q ^) -> (∃ r : x = y, ap f r @ q = p)).
      - intros [r Ɣ]; apply @path_sigma' with (p:=1); simpl. destruct q; simpl. hott_simpl.
      - intros [r Ɣ]; apply @path_sigma' with (p:=1); simpl. destruct q; simpl. hott_simpl. }

    split.
    - intros H x y.
      apply isequiv_fcontr. intro q.
      pose (Y := X (f x) (x;1) (y;q^)). simpl in Y. hott_simpl. unfold hfiber in Y. rewrite <- Y.
      exact (H (f x) (x;1) (y;q^)).
    - intros H b x y; simpl. specialize (X b x y). rewrite X.
      exact (fcontr_isequiv (ap f) (H x.1 y.1) (x.2@y.2^)). 
  Qed.

  
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
      etransitivity; try exact (ap10_ap_postcompose f (g:=(λ _ : A, x)) (g' := (λ _ : A, y)) (inv (path_forall (λ _ : A, f x) (λ _ : A, f y) (λ _ : A, u))) x)^.
      rewrite retr.
      unfold ap10. unfold path_forall.
      rewrite eisretr.
      exact idpath.
    - intro u. destruct u; simpl in *. 
      rewrite path_forall_1.
      apply (transport (fun u => ap10 u x = 1) (sect 1)^).
      exact idpath.
  Defined.

  Definition IsMono_to_IsMonof (A B : Type) (f : A -> B) : IsMono f -> IsMonof f.
    intro H.
    intros X a b.
    pose (φ := fun p => path_forall a b (fun x => equiv_inv (IsEquiv := H (a x) (b x)) (ap10 p x))).
    apply isequiv_adjointify with (g:= φ).
    - intro p.
      unfold φ.
      apply (@equiv_inj _ _ _ (isequiv_ap10 _ _)).
      apply path_forall; intro u. 
      apply (transport (λ U, U = ap10 p u) (ap10_ap_postcompose f _ u)^).
      unfold ap10 at 1, path_forall. rewrite eisretr. rewrite eisretr. exact 1.
    - intro p; unfold φ; destruct p. simpl.
      pose (foo := path_forall _ _ (fun y =>  (@eissect _ _ _ (H (a y) (a y)) idpath))).
      simpl in foo. rewrite foo.
      apply path_forall_1.
  Qed.

End Embeddings.

Section Surjections.

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
    apply Trunc_ind; try (intro; apply istrunc_truncation). intros [b p].
    generalize dependent (@center _ (Ef b)).
    apply Trunc_ind; try (intro; apply istrunc_truncation). intros [a q].
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
    apply Trunc_ind; try (intro; apply istrunc_truncation). intros [a p].
  
    apply tr.

    exists (f a).
    exact ((π a) @ p).
  Qed.

  Lemma epi_two_out_of_three_3 (A B C:Type) (f:A -> B) (g:B -> C) (h : A -> C) (π : forall a,  g (f a) = h a)
  : IsSurjection g -> IsSurjection h -> IsSurjection f.
  Admitted.
            
  Definition IsEpi A B (f:A -> B)
    := forall C:Type, forall (x y : B -> C) , IsEquiv (ap (fun u => u o f) (x:=x) (y:=y)).

End Surjections.

