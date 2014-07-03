Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.

Require Import equiv truncation univalence sub_object_classifier.

Set Universe Polymorphism.
Global Set Primitive Projections.
Set Implicit Arguments.

Definition pullback (A B C : Type) (f : A -> C) (g : B -> C) := {a:A & {b: B & f a = g b}}.

Section Pullback.

  Variable A B C : Type.
  Variable f : A -> C.
  Variable g : B -> C.

  Variable S : Type.

  Definition pullback_inj : (S -> pullback f g) -> 
                            pullback (fun m : S -> A => f o m) (fun n : S -> B => g o n) :=
    fun h => (pr1 (P:=_) o h; ((fun x => pr1 (pr2 x)) o h ; 
                              path_forall _ _ (fun s => pr2 (pr2 (h s))))).


  Instance pullback_equiv : IsEquiv pullback_inj.
  apply (isequiv_adjointify pullback_inj (λ X s, (pr1 X s ;(pr1 (pr2 X) s ; ap10 (pr2 (pr2 X)) s)))).
  - intro P; destruct P as [m [n P]]. simpl. unfold pullback_inj, compose; simpl.
    apply path_sigma' with (p := idpath).
    simpl.
    apply path_sigma' with (p := idpath). 
    simpl. apply eissect.
  - intro P. apply path_forall. intro s. 
    rewrite <- eta_sigma.
    apply path_sigma' with (p := idpath); simpl.
    rewrite <- eta_sigma.
    apply path_sigma' with (p := idpath); simpl.
    unfold ap10, path_forall. rewrite eisretr.
    exact idpath.
  Defined.
  
  Definition pullback_proj : pullback f g -> {_:A & B} := 
    fun X => existT (fun _ => B) (pr1 X) (pr1 (pr2 X)).

End Pullback.

Section kernel_pair.

  Definition epimorphism A B (f : A -> B) := forall b, IsConnected minus_one (hfiber f b). 
  
  Definition kernel_pair A B (f : A -> B) := pullback f f.
  
  Definition inj1 A B (f : A -> B) : kernel_pair f -> A := pr1 (P:=_).
  Definition inj2 A B (f : A -> B) : kernel_pair f -> A := fun x => pr1 (P:=_) (pr2 (P:=_) x).

  Definition is_coequalizer A B (f g : A -> B) X (coequalizer : {m : B -> X & m o f =  m o g}) :=
    forall Y, IsEquiv (fun x : X -> Y => 
                         existT (fun m => m o f =  m o g) (x o pr1 coequalizer) (ap (fun u => x o u) (pr2 coequalizer))).
  
  Definition Im {A B} (f : A -> B) := {b : B & squash (hfiber f b)}.

  Definition toIm {A B} (f : A -> B) : A -> Im f := fun a => (f a; truncation_incl (a;idpath)).

  Definition fromIm {A B} (f : A -> B) : Im f -> B := fun im => pr1 im.
  
  Definition Im_coequalizes_kernel_pair A B (f : A -> B) : toIm f o inj1 (f:=f) = toIm f o inj2 (f:=f).
    apply path_forall; intro x.
    unfold toIm, inj1, inj2, compose. simpl.
    eapply (eq_dep_subset' (λ x, Truncation minus_one (∃ x0 : A, f x0 = x)) _ _ _ (pr2 (pr2 x))). 
  Defined.


  (* Definition IsEpi A B (f:A -> B) *)
  (* := forall C, IsEquiv (λ (u:B -> C), u o f). *)

  (* Definition epi_coeq_kernel_pair_eq A B (f:A -> B) (epi : IsEpi f) *)
  (* : f o inj1 (f:=f) = f o inj2 (f:=f). *)
  (*   apply path_forall; intro x. *)
  (*   exact x.2.2. *)
  (* Defined. *)

  (* Definition epi_coeq_kernel_pair A (epi : IsEpi (λ _:A, tt)) *)
  (* : is_coequalizer (λ _, tt ; epi_coeq_kernel_pair_eq epi). *)
  (*   intro Q. simpl. *)
  (*   apply isequiv_adjointify with (g := λ x, λ a, x.1 (equiv_inv (IsEquiv := epi A) idmap a)). *)
  (*   - intros [q eq]. *)
  (*     simpl. unfold compose. simpl. *)
  (*     unfold equiv_inv. *)
  (*     destruct (epi A) as [inv retr sect _]. *)
  (*     apply @path_sigma' with (p := path_forall _ _ (λ x, ap q (ap10 (retr idmap) x))). *)
  (*     simpl. *)
  (*     apply moveR_transport_p. *)
        
      
    

  (* Definition epi_coeq_kernel_pair A B (f:A -> B) (epi :IsEpi f) *)
  (* : is_coequalizer (f ; epi_coeq_kernel_pair_eq epi). *)
  (*   intro C. simpl. *)
  (*   assert ((∃ m : A → C, m o inj1 (f:=f) = m o inj2 (f:=f)) -> (B -> C)). *)
  (*   intros [m eq] b. *)
  (*   unfold inj1, inj2, compose in eq; simpl in eq. *)
  (*   unfold IsEpi in f. *)
  
  (* The proof below should be instead the proof that Im f is equivalent to the coequalizer of (kernel_pair f) *)

  (* Lemma Im_is_coeq_diag (A:Type)  *)
  (* : @is_coequalizer (A*A) A fst snd Unit (λ _, tt ; 1). *)
  (*   intros Q. *)

  (*   assert ((∃ m : A → Q, m o fst = m o snd) -> (Unit → Q)). *)
  (*   Focus 1. *)

  (*   intros [q eq] tt. *)
    
  (*   assert (eq_1 : (fst : Q*Q -> Q) o (λ a:A*A, (q (fst a), q (snd a))) = q o (fst : A*A -> A)). *)
  (*     apply path_forall; intro a. exact 1. *)
  (*   assert (eq_2 : ((snd : Q*Q -> Q) o (λ a:A*A, (q (fst a), q (snd a))) = q o (snd : A*A -> A))). *)
  (*     apply path_forall; intro a; exact 1. *)
  (*     (* unfold compose in *; simpl in *. *) *)

  (*   assert ((fst : Q*Q -> Q) = (snd : Q*Q -> Q)). *)
  (*     apply path_forall; intro x. *)

  (*     assert (eq_3 := eq_1 @ eq @ eq_2^). simpl in *. *)
  (*     assert (forall u:Q, {a:A & u = q a}). *)
  (*       intro u. *)
      
  (*     destruct x as [x y]. simpl in *. *)
  (*     apply ap10 in eq_1; apply ap10 in eq_2. unfold pointwise_paths in eq_1, eq_2. *)
      
  (*   assert (forall X:Type, forall f g:X -> Q, f=g). *)
  (*     intros X f g. *)
      

    

  Lemma Im_is_coequalizer_kernel_pair A B (f : A -> B) :
    is_coequalizer (toIm f;(Im_coequalizes_kernel_pair f)).
  Proof.
    intro Y; simpl.
    unfold toIm, compose. simpl.
    
    assert ((∃ m : A → Y,
            (λ x0 : kernel_pair f, m (inj1 x0)) =
            (λ x0 : kernel_pair f, m (inj2 x0))) -> (Im f -> Y)).
      intros [m p] [b q].
      unfold kernel_pair in p.
      unfold inj1, inj2, kernel_pair, pullback in p; simpl in p.
      unfold squash, hfiber in q.
      

    (* apply isequiv_adjointify with (g := X). *)
    
    (* unfold Im_coequalizes_kernel_pair, path_forall, composition.  *)
  Admitted.

End kernel_pair.
