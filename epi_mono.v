Require Export Utf8_core.
Require Import HoTT TruncType.
Require Import hit.Connectedness hit.Truncations.
Require Import univalence lemmas.

Set Universe Polymorphism.
Set Implicit Arguments.

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

  Definition IsMono (A B : Type) (f : A -> B) := forall x y, IsEquiv (ap f (x:=x) (y:=y)).

  Definition IsMonof (A B : Type) (f : A -> B) := forall (X:Type) (x y : X -> A), 
                                                    IsEquiv (ap (fun u => f o u) (x:=x) (y:=y)).

  Lemma IsEmbedding_IsMono (A B : Type) (f : A -> B)
  : IsEmbedding f <-> IsMono f.
    
    assert (forall b:B, forall x y:hfiber f b, (x=y) <~> (hfiber (ap f) (x.2 @ y.2^))).
    { intros u [x p] [y q]. simpl.
      etransitivity; try exact (L425 (x;p) (y;q)).
      refine (equiv_adjointify _ _ _ _).
      - intro r.
        exists r.1.
        exact (moveL_pV q (ap f r.1) p r.2).
      - intro r. exists r.1.
        exact (moveR_pM q p (ap f r.1) r.2).
      - intros [r Ɣ]; apply @path_sigma' with (p:=1); simpl. destruct q; simpl. hott_simpl.
      - intros [r Ɣ]; apply @path_sigma' with (p:=1); simpl. destruct q; simpl. hott_simpl. }

    split.
    - intros H x y.
      apply isequiv_fcontr. intro q.
      pose (Y := X (f x) (x;1) (y;q^)). simpl in Y. hott_simpl. unfold hfiber in Y.
      refine (contr_equiv' ((x; 1) = (y; q^)) Y).
    - intros H b x y; simpl. specialize (X b x y).
      refine (contr_equiv' _ (equiv_inverse X)).
      exact (fcontr_isequiv (ap f) (H x.1 y.1) (x.2@y.2^)). 
  Qed.
  
  Definition IsMonof_to_isMono (A B : Type) (f : A -> B) : IsMonof f -> IsMono f.
    intro H. intros x y.
    unfold IsMonof in H.
    specialize (H A). specialize (H (fun _ => x) (fun _ => y)).
    destruct H as [inv retr sect _]. 
    refine (isequiv_adjointify _ _ _ _).
    - intro H.
      refine (apD10 (f := λ _, x) (g := λ _, y) (inv _) _).
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
      unfold ap10 at 1, path_forall. rewrite eisretr. rewrite eisretr. reflexivity.
    - intro p; unfold φ; destruct p. simpl.
      pose (foo := path_forall _ _ (fun y =>  (@eissect _ _ _ (H (a y) (a y)) idpath))).
      simpl in foo. rewrite foo.
      apply path_forall_1.
  Qed.

  
  Definition apf_Mono (T U:Type) (f: T -> U) (fMono : IsMonof f) X (x y : X -> T) (e e' : x = y) : 
    ap (fun u => f o u) e = ap (fun u => f o u) e' -> e = e'.
    intro. 
    rewrite <- (@eissect _ _ _ (fMono _ _ _) e). 
    rewrite <- (@eissect _ _ _ (fMono _ _ _) e'). exact (ap _ X0). 
  Defined.
  
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
       
  Definition IsEpi A B (f:A -> B)
    := forall C:Type, forall (x y : B -> C) , IsEquiv (ap (fun u => u o f) (x:=x) (y:=y)).

End Surjections.

