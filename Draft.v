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

  Lemma nnem (P:hProp) : ~ ~ (P + ~ P).
  Proof.
    intros f; apply f.
    apply inr. intro p.
    apply f. apply inl. exact p.
  Defined.
    
  
  Lemma nnnn_nn (P:hProp) : (~ ~ ~ ~ P) -> ~ ~ P.
  Proof.
    intros nnnnp np.
    apply nnnnp.
    intros nnp.
    exact (nnp np).
  Defined.

  Lemma O_to_nn (P:hProp) 
    :good_sheafification_Type (BuildhSet P) -> (O subuniverse_Prop P).
  Proof.
    intros [u p].
    revert p. apply O_rec. apply Trunc_rec.
    intros [a p]. cbn in *.
    apply O_unit. exact a.
  Defined.

  

  Lemma nn_to_O (P:hProp) 
    :(O subuniverse_Prop P) -> good_sheafification_Type (BuildhSet P).
  Proof.
    intro np.
    refine (exist _ _ _).
    - intro p.
      unfold sheaf_induction.nj, sheaf_def_and_thm.nj. cbn.
      refine (Build_subuniverse_Type _ subuniverse_Prop (BuildTruncType _ (O_unit subuniverse_Prop _ p = np)) _).
      refine (istrunc_paths _ _ _).
      refine (subuniverse_paths _ _ _ (O_unit subuniverse_Prop P p) np).
    - cbn.
      revert np.
      transparent assert (sh: (O subuniverse_Prop P
                               → subuniverse_Type subuniverse_Prop)).
      { intro np.
        refine (Build_subuniverse_Type _ subuniverse_Prop (BuildhProp (@trunctype_type (trunc_S minus_two)
     (@st (trunc_S minus_two) (@subuniverse_Prop fs)
        (@O (trunc_S minus_two) (@subuniverse_Prop fs)
           (@BuildTruncType (trunc_S minus_two)
              (Trunc (trunc_S minus_two)
                 (@sig (@trunctype_type (trunc_S minus_two) P)
                    (fun a : @trunctype_type (trunc_S minus_two) P =>
                     @paths
                       (forall _ : @trunctype_type (trunc_S minus_two) P,
                        @subuniverse_Type sheaf_def_and_thm.n
                          (@subuniverse_Prop fs))
                       (fun t' : @trunctype_type (trunc_S minus_two) P =>
                        @O sheaf_def_and_thm.n (@subuniverse_Prop fs)
                          (@BTT
                             (@paths (@trunctype_type (trunc_S minus_two) P)
                                a t')
                             (@istrunc_paths
                                (@trunctype_type (trunc_S minus_two) P)
                                sheaf_induction.n
                                (fun
                                   x
                                    y : @trunctype_type (trunc_S minus_two) P
                                 =>
                                 @trunc_succ minus_two
                                   (@paths
                                      (@trunctype_type (trunc_S minus_two) P)
                                      x y)
                                   (@istrunc_paths
                                      (@trunctype_type (trunc_S minus_two) P)
                                      minus_two
                                      (@istrunc_trunctype_type
                                         (trunc_S minus_two) P) x y)) a t')))
                       (fun p : @trunctype_type (trunc_S minus_two) P =>
                        Build_subuniverse_Type (trunc_S minus_two)
                          (@subuniverse_Prop fs)
                          (@BuildTruncType (trunc_S minus_two)
                             (@paths
                                (@trunctype_type (trunc_S minus_two)
                                   (@st (trunc_S minus_two)
                                      (@subuniverse_Prop fs)
                                      (@O (trunc_S minus_two)
                                         (@subuniverse_Prop fs) P)))
                                (@O_unit (trunc_S minus_two)
                                   (@subuniverse_Prop fs) P p) np)
                             (@istrunc_paths
                                (@trunctype_type (trunc_S minus_two)
                                   (@st (trunc_S minus_two)
                                      (@subuniverse_Prop fs)
                                      (@O (trunc_S minus_two)
                                         (@subuniverse_Prop fs) P)))
                                (trunc_S minus_two)
                                (fun
                                   x
                                    y : @trunctype_type 
                                          (trunc_S minus_two)
                                          (@st (trunc_S minus_two)
                                             (@subuniverse_Prop fs)
                                             (@O (trunc_S minus_two)
                                                (@subuniverse_Prop fs) P)) =>
                                 @trunc_succ minus_two
                                   (@paths
                                      (@trunctype_type 
                                         (trunc_S minus_two)
                                         (@st (trunc_S minus_two)
                                            (@subuniverse_Prop fs)
                                            (@O (trunc_S minus_two)
                                               (@subuniverse_Prop fs) P))) x
                                      y)
                                   (@istrunc_paths
                                      (@trunctype_type 
                                         (trunc_S minus_two)
                                         (@st (trunc_S minus_two)
                                            (@subuniverse_Prop fs)
                                            (@O (trunc_S minus_two)
                                               (@subuniverse_Prop fs) P)))
                                      minus_two
                                      (@istrunc_trunctype_type
                                         (trunc_S minus_two)
                                         (@st (trunc_S minus_two)
                                            (@subuniverse_Prop fs)
                                            (@O (trunc_S minus_two)
                                               (@subuniverse_Prop fs) P))) x
                                      y))
                                (@O_unit (trunc_S minus_two)
                                   (@subuniverse_Prop fs) P p) np))
                          (@subuniverse_paths (trunc_S minus_two)
                             (@subuniverse_Prop fs) ua fs
                             (@O (trunc_S minus_two) (@subuniverse_Prop fs) P)
                             (@O_unit (trunc_S minus_two)
                                (@subuniverse_Prop fs) P p) np)))))
              (istrunc_truncation (trunc_S minus_two)
                 (@sig (@trunctype_type (trunc_S minus_two) P)
                    (fun a : @trunctype_type (trunc_S minus_two) P =>
                     @paths
                       (forall _ : @trunctype_type (trunc_S minus_two) P,
                        @subuniverse_Type sheaf_def_and_thm.n
                          (@subuniverse_Prop fs))
                       (fun t' : @trunctype_type (trunc_S minus_two) P =>
                        @O sheaf_def_and_thm.n (@subuniverse_Prop fs)
                          (@BTT
                             (@paths (@trunctype_type (trunc_S minus_two) P)
                                a t')
                             (@istrunc_paths
                                (@trunctype_type (trunc_S minus_two) P)
                                sheaf_induction.n
                                (fun
                                   x
                                    y : @trunctype_type (trunc_S minus_two) P
                                 =>
                                 @trunc_succ minus_two
                                   (@paths
                                      (@trunctype_type (trunc_S minus_two) P)
                                      x y)
                                   (@istrunc_paths
                                      (@trunctype_type (trunc_S minus_two) P)
                                      minus_two
                                      (@istrunc_trunctype_type
                                         (trunc_S minus_two) P) x y)) a t')))
                       (fun p : @trunctype_type (trunc_S minus_two) P =>
                        Build_subuniverse_Type (trunc_S minus_two)
                          (@subuniverse_Prop fs)
                          (@BuildTruncType (trunc_S minus_two)
                             (@paths
                                (@trunctype_type (trunc_S minus_two)
                                   (@st (trunc_S minus_two)
                                      (@subuniverse_Prop fs)
                                      (@O (trunc_S minus_two)
                                         (@subuniverse_Prop fs) P)))
                                (@O_unit (trunc_S minus_two)
                                   (@subuniverse_Prop fs) P p) np)
                             (@istrunc_paths
                                (@trunctype_type (trunc_S minus_two)
                                   (@st (trunc_S minus_two)
                                      (@subuniverse_Prop fs)
                                      (@O (trunc_S minus_two)
                                         (@subuniverse_Prop fs) P)))
                                (trunc_S minus_two)
                                (fun
                                   x
                                    y : @trunctype_type 
                                          (trunc_S minus_two)
                                          (@st (trunc_S minus_two)
                                             (@subuniverse_Prop fs)
                                             (@O (trunc_S minus_two)
                                                (@subuniverse_Prop fs) P)) =>
                                 @trunc_succ minus_two
                                   (@paths
                                      (@trunctype_type 
                                         (trunc_S minus_two)
                                         (@st (trunc_S minus_two)
                                            (@subuniverse_Prop fs)
                                            (@O (trunc_S minus_two)
                                               (@subuniverse_Prop fs) P))) x
                                      y)
                                   (@istrunc_paths
                                      (@trunctype_type 
                                         (trunc_S minus_two)
                                         (@st (trunc_S minus_two)
                                            (@subuniverse_Prop fs)
                                            (@O (trunc_S minus_two)
                                               (@subuniverse_Prop fs) P)))
                                      minus_two
                                      (@istrunc_trunctype_type
                                         (trunc_S minus_two)
                                         (@st (trunc_S minus_two)
                                            (@subuniverse_Prop fs)
                                            (@O (trunc_S minus_two)
                                               (@subuniverse_Prop fs) P))) x
                                      y))
                                (@O_unit (trunc_S minus_two)
                                   (@subuniverse_Prop fs) P p) np))
                          (@subuniverse_paths (trunc_S minus_two)
                             (@subuniverse_Prop fs) ua fs
                             (@O (trunc_S minus_two) (@subuniverse_Prop fs) P)
                             (@O_unit (trunc_S minus_two)
                                      (@subuniverse_Prop fs) P p) np)))))))))) _).
        auto with typeclass_instances.
        apply subu_struct. }
      refine (O_rec_dep (mod := modality_Prop) _ sh _).1.
      intro a; subst sh; cbn.
      apply O_unit. cbn.
      apply tr.
      exists a.
      cbn.
      apply path_forall; intro t.
      apply unique_subuniverse. apply path_trunctype. cbn.
      Transparent O_unit. Transparent O. unfold O_unit, O; cbn; unfold Oj_unit; cbn.
      refine (equiv_iff_hprop _ _).
      + intro p. apply path_forall; intro np.
        destruct (np a).
      + intros p q.
        exact (q (path_ishprop (A := P) a t)).
  Defined.
  
  Goal forall (P:hProp), Type.
  Proof.
   
    Transparent O_equiv.
    
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

    pose (O_rec _ O1 (BuildhSet (P+~P)) (O O1 (BuildhSet Bool)) f (nn_to_O (nnem P))).
    unfold O_rec, O, O_equiv in t.
    unfold sheaf_induction.n in t. unfold sheaf_def_and_thm.n in t. unfold sheaf_def_and_thm.n0 in t.




    
    unfold O_rec, O, O_equiv in t.
