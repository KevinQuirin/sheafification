(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)


Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import epi_mono reflective_subuniverse modalities.
Require Import nat_lemmas.
Require Import kernel_pair.
Require Import sheaf_base_case.
Require Import sheaf_def_and_thm.
Require Import sheaf_induction.

Set Universe Polymorphism.
Global Set Primitive Projections. 
Set Implicit Arguments.

Local Open Scope path_scope.
(* Local Open Scope equiv_scope. *)
Local Open Scope type_scope.

(* Readability *)
Arguments trunc_arrow {H} {A} {B} {n} H0: simpl never.
Arguments trunc_sigma {A} {P} {n} H H0: simpl never.
Arguments trunc_forall {H} {A} {P} {n} H0: simpl never. 
Arguments istrunc_paths {A} {n} H x y: simpl never.
Arguments isequiv_functor_sigma {A P B Q} f {H} g {H0}: simpl never.
                        
Section Sheafification.

  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  
  Local Definition n0 := sheaf_def_and_thm.n0.
  Local Definition n := sheaf_def_and_thm.n.
  Local Definition mod_nj := sheaf_def_and_thm.mod_nj.
  Local Definition nj := sheaf_def_and_thm.nj.
  Local Definition j_is_nj := sheaf_def_and_thm.j_is_nj.
  Local Definition j_is_nj_unit := sheaf_def_and_thm.j_is_nj_unit.
  Local Definition islex_mod_nj := sheaf_def_and_thm.islex_mod_nj.
  Local Definition islex_nj := sheaf_def_and_thm.islex_nj.
  Local Definition lex_compat := sheaf_def_and_thm.lex_compat.

  Definition mod_O1 := sheafification_modality.
  Definition O1 := underlying_subu _ mod_O1.

  Transparent n0.
  
  Lemma nnnn_nn (P:hProp) : (~ ~ ~ ~ P) -> ~ ~ P.
  Proof.
    intros nnnnp np.
    apply nnnnp.
    intros nnp.
    exact (nnp np).
  Defined.

  Lemma nn_to_O (P:hProp) 
    :(O subuniverse_Prop P) -> good_sheafification_Type (BuildhSet P).
  Proof.
    intro Op.
    
    
    
    pose (O_rec _ O1 (BuildhSet P) (O O1 (BuildhSet P))). cbn in t.
    

  Goal forall (P:hProp), Type.
  Proof.
    intro P.
    assert (IsHSet (P+~P)).
    { apply trunc_succ. refine (ishprop_sum _ _ _).
      intros p np; exact (np p). }
    transparent assert (f : ((P+~P) -> (O O1 (BuildhSet Bool)))).
    { intro p; case p.
      exact (λ _, O_unit O1 (BuildhSet Bool) True). exact (λ _, O_unit O1 (BuildhSet Bool) False). }
      
    assert (IsHProp (P+~P)).
    { refine (ishprop_sum _ _ _).
      intros p np; exact (np p). }

    assert (φ: (O subuniverse_Prop (BuildhProp (P + ~P))) -> good_sheafification_Type (BuildhSet (P + ~P))).
    { cbn. intro t. 
      unfold good_sheafification_Type; cbn.
      refine (exist _ _ _).
      intro t'.
      refine (Build_subuniverse_Type _ _ _ _).
      unfold subuniverse_Type.
      assert ((λ T : Type, IsHProp T) (t = O_unit subuniverse_Prop (P ∨ ~ P; X0) t')).
      apply istrunc_paths.
      apply trunc_arrow.
      apply trunc_succ. apply hprop_Empty.
      exists (O subuniverse_Prop ((t = O_unit subuniverse_Prop ((P+~P;X0)) t');X1)).1.
      exact (O subuniverse_Prop (t = O_unit subuniverse_Prop (P ∨ ~ P; X0) t'; X1)).2.

      revert t. cbn.
      pose (O_rec_dep (mod := modality_Prop) ((P+~P;X0))).
      transparent assert (sh: (((O (underlying_subu (-1) modality_Prop) (P ∨ ~ P; X0)).1).1
                               → subuniverse_Type (underlying_subu (-1) modality_Prop))).
      { intro t. cbn in *.
        refine (exist _ _ _). refine (exist _ _ _).
        exact (not
     (not
        (Trunc (trunc_S minus_two)
           (@sig
              (sum (@trunctype_type (trunc_S minus_two) P)
                 (not (@trunctype_type (trunc_S minus_two) P)))
              (fun
                 a : sum (@trunctype_type (trunc_S minus_two) P)
                       (not (@trunctype_type (trunc_S minus_two) P)) =>
               @paths
                 (forall
                    _ : sum (@trunctype_type (trunc_S minus_two) P)
                          (not (@trunctype_type (trunc_S minus_two) P)),
                  @sig (Trunk sheaf_def_and_thm.n)
                    (fun T : Trunk sheaf_def_and_thm.n =>
                     forall
                       _ : not
                             (not
                                (@proj1_sig Type
                                   (fun T0 : Type =>
                                    IsTrunc sheaf_def_and_thm.n T0) T)),
                     @proj1_sig Type
                       (fun T0 : Type => IsTrunc sheaf_def_and_thm.n T0) T))
                 (fun
                    t' : sum (@trunctype_type (trunc_S minus_two) P)
                           (not (@trunctype_type (trunc_S minus_two) P)) =>
                  @Oj fs
                    (@exist Type (IsTrunc sheaf_induction.n)
                       (@paths
                          (sum (@trunctype_type (trunc_S minus_two) P)
                             (not (@trunctype_type (trunc_S minus_two) P))) a
                          t')
                       (@istrunc_paths
                          (sum (@trunctype_type (trunc_S minus_two) P)
                             (not (@trunctype_type (trunc_S minus_two) P)))
                          sheaf_induction.n X a t')))
                 (fun
                    t' : sum (@trunctype_type (trunc_S minus_two) P)
                           (not (@trunctype_type (trunc_S minus_two) P)) =>
                  @exist (Trunk sheaf_def_and_thm.n)
                    (fun T : Trunk sheaf_def_and_thm.n =>
                     forall
                       _ : not
                             (not
                                (@proj1_sig Type
                                   (fun T0 : Type =>
                                    IsTrunc sheaf_def_and_thm.n T0) T)),
                     @proj1_sig Type
                       (fun T0 : Type => IsTrunc sheaf_def_and_thm.n T0) T)
                    (@j fs
                       (@exist Type
                          (fun T : Type => IsTrunc (trunc_S minus_two) T)
                          (@paths
                             (not
                                (not
                                   (sum
                                      (@trunctype_type (trunc_S minus_two) P)
                                      (not
                                         (@trunctype_type 
                                            (trunc_S minus_two) P))))) t
                             (@Oj_unit fs
                                (@exist Type (IsTrunc (trunc_S minus_two))
                                   (sum
                                      (@trunctype_type (trunc_S minus_two) P)
                                      (not
                                         (@trunctype_type 
                                            (trunc_S minus_two) P))) X0) t'))
                          (@istrunc_paths
                             (not
                                (not
                                   (sum
                                      (@trunctype_type (trunc_S minus_two) P)
                                      (not
                                         (@trunctype_type 
                                            (trunc_S minus_two) P)))))
                             (trunc_S minus_two)
                             (@trunc_arrow fs
                                (not
                                   (sum
                                      (@trunctype_type (trunc_S minus_two) P)
                                      (not
                                         (@trunctype_type 
                                            (trunc_S minus_two) P)))) Empty
                                (trunc_S (trunc_S minus_two))
                                (@trunc_succ (trunc_S minus_two) Empty
                                   hprop_Empty)) t
                             (@Oj_unit fs
                                (@exist Type (IsTrunc (trunc_S minus_two))
                                   (sum
                                      (@trunctype_type (trunc_S minus_two) P)
                                      (not
                                         (@trunctype_type 
                                            (trunc_S minus_two) P))) X0) t'))))
                    (fun
                       (X1 : not
                               (not
                                  (not
                                     (not
                                        (@paths
                                           (not
                                              (not
                                                 (sum
                                                  (@trunctype_type
                                                  (trunc_S minus_two) P)
                                                  (not
                                                  (@trunctype_type
                                                  (trunc_S minus_two) P)))))
                                           t
                                           (@Oj_unit fs
                                              (@exist Type
                                                 (IsTrunc (trunc_S minus_two))
                                                 (sum
                                                  (@trunctype_type
                                                  (trunc_S minus_two) P)
                                                  (not
                                                  (@trunctype_type
                                                  (trunc_S minus_two) P))) X0)
                                              t'))))))
                       (X2 : not
                               (@paths
                                  (not
                                     (not
                                        (sum
                                           (@trunctype_type
                                              (trunc_S minus_two) P)
                                           (not
                                              (@trunctype_type
                                                 (trunc_S minus_two) P))))) t
                                  (@Oj_unit fs
                                     (@exist Type
                                        (IsTrunc (trunc_S minus_two))
                                        (sum
                                           (@trunctype_type
                                              (trunc_S minus_two) P)
                                           (not
                                              (@trunctype_type
                                                 (trunc_S minus_two) P))) X0)
                                     t'))) =>
                     X1
                       (fun
                          X3 : not
                                 (not
                                    (@paths
                                       (not
                                          (not
                                             (sum
                                                (@trunctype_type
                                                  (trunc_S minus_two) P)
                                                (not
                                                  (@trunctype_type
                                                  (trunc_S minus_two) P)))))
                                       t
                                       (@Oj_unit fs
                                          (@exist Type
                                             (IsTrunc (trunc_S minus_two))
                                             (sum
                                                (@trunctype_type
                                                  (trunc_S minus_two) P)
                                                (not
                                                  (@trunctype_type
                                                  (trunc_S minus_two) P))) X0)
                                          t'))) => 
                           X3 X2)))))))).
        refine (trunc_arrow _).
        cbn.
        refine (nnnn_nn _).}

      specialize (s sh).