Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import equivalence univalence sub_object_classifier epi_mono cech_nerve reflective_subuniverse.

Set Universe Polymorphism.
Global Set Primitive Projections.

(* Readability *)
Arguments trunc_arrow {H} {A} {B} {n} H0: simpl never.
Arguments trunc_sigma {A} {P} {n} H H0: simpl never.
Arguments istrunc_paths {A} {n} H x y: simpl never.
Arguments truncn_unique _ {n} A B H: simpl never.

Section Preliminary.

  Record Modality n := Build_Modality {
                               
                               underlying_subu : subuniverse_struct n ;
                               
                               subu_sigma : (forall (A:subuniverse_Type underlying_subu) (B:A.1.1 -> subuniverse_Type underlying_subu), (subuniverse_HProp underlying_subu ({x:A.1.1 & (B x).1.1} ; trunc_sigma (A.1.2) (λ x, (B x).1.2))).1)
                                              
                         }.

  Definition modal_contr_is_equiv n (mod : Modality n.+1) (subU := underlying_subu n.+1 mod) (X:Trunk n.+1) (Y : subuniverse_Type subU) (f : X.1 -> Y.1.1) (mod_contr_f : forall y, Contr (O subU (hfiber f y ; trunc_sigma (X.2) (λ x, trunc_succ (H := istrunc_paths (Y.1.2) (f x) y)))).1.1)
  : (O subU X).1.1 <~> Y.1.1.
    refine (BuildEquiv _ _ _ _).
    - apply O_rec; exact f.
    - pose (O_equiv subU X Y).
      admit.
      
  Defined.

End Preliminary.

Section LexModality.

  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  Definition IsLex {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod)
    := forall (A:Trunk (trunc_S n)), forall (x y:A.1),
         Contr ((O subU A).1.1) -> Contr ((O subU (existT (IsTrunc n.+1) (x = y) (@trunc_succ n _ (@istrunc_paths A.1 n A.2 x y)))).1.1).

  Lemma islex_compat_func {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) (X Y:Trunk n.+1) (f: X.1 -> Y.1) (y:Y.1)
  : forall a:{a:X.1 & f a = y}, (function_lift subU X Y f (O_unit subU _ a.1) = O_unit subU Y y).
    intros a. simpl.
    pose (foo := ap10 (O_rec_retr X (O subU Y) (λ x : X .1, O_unit subU Y (f x))) a.1). unfold compose in foo; simpl in foo.
    exact (transport (λ U, O_rec X (O subU Y) (λ x : X .1, O_unit subU Y (f x)) (O_unit subU X a.1) = O_unit subU Y U) a.2 foo).
  Defined.

  Lemma islex_to_hfibers_preservation {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) (islex : IsLex mod)
  : forall (X Y:Trunk n.+1) (f : X.1 -> Y.1) (y:Y.1), (O subU (existT (λ T, IsTrunc n.+1 T) (hfiber f y) (trunc_sigma X.2 (λ a, istrunc_paths (trunc_succ (H:=Y.2)) _ _)))).1.1 = {rx : (O subU X).1.1 & function_lift subU X Y f rx = O_unit subU Y y}.
    intros X Y f y.
    apply path_universe_uncurried.
    transparent assert (TrΣ : (IsTrunc n.+1 (∃ rx : ((O subU X).1).1, function_lift subU X Y f rx = O_unit subU Y y))).
    { apply trunc_sigma.
      exact (O subU X).1.2.
      intro a. apply istrunc_paths.
      refine trunc_succ. exact (O subU Y).1.2. }
    assert (modalsigma : (subuniverse_HProp subU ((∃ rx : ((O subU X).1).1, function_lift subU X Y f rx = O_unit subU Y y);
                                                  trunc_sigma (O subU X).1.2 (λ x, istrunc_paths (trunc_succ (H := (O subU Y).1.2)) _ _)
                                                 )).1).
    
    { pose (subu_sigma _ mod (O subU X)).
      transparent assert (B : (((O subU X).1).1 → subuniverse_Type (underlying_subu n.+1 mod))).
      intro rx.
      exists (function_lift subU X Y f rx = O_unit subU Y y ; istrunc_paths (trunc_succ (H := (O subU Y).1.2)) _ _).
      apply subuniverse_paths.
      
      pose subu_sigma. specialize (p0 (trunc_S n) mod (O subU X) B).
      apply p0. }

    refine (modal_contr_is_equiv n mod (hfiber f y;
                                        trunc_sigma X.2 (λ a : X.1, istrunc_paths trunc_succ (f a) y)) (((∃ rx : ((O subU X).1).1, function_lift subU X Y f rx = O_unit subU Y y);TrΣ);modalsigma) _ _) .
    - intros u.
      simpl.
      exists (O_unit subU _ u.1).
      apply islex_compat_func.
    - admit. 
      
      

    
  Defined.


  Lemma islex_to_hfibers_preservation_compat {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) (islex : IsLex mod)
  : forall (X Y:Trunk n.+1) (f: X.1 -> Y.1) (y:Y.1) (a:{a:X.1 & f a = y}),
      ((equiv_path _ _ (islex_to_hfibers_preservation mod islex X Y f y)) o (O_unit subU _)) a = (O_unit subU _ a.1; islex_compat_func mod X Y f y a).
    simpl. intros X Y f y a.
    unfold islex_to_hfibers_preservation; simpl.
    unfold modal_contr_is_equiv.
    rewrite transport_path_universe_uncurried.
    unfold compose; simpl.
    pose (rew := λ P Q f, ap10 (O_rec_retr (n:=n.+1) (subU := subU) P Q f)).
    unfold compose in rew. rewrite rew; clear rew.
    reflexivity.
  Qed.

End LexModality.