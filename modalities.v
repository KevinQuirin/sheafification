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
Arguments trunc_succ {n} {A} H _ _: simpl never.
          

Section Preliminary.

  Record Modality n := Build_Modality {
                               
                               underlying_subu : subuniverse_struct n ;
                               
                               subu_sigma : (forall (A:subuniverse_Type underlying_subu) (B:A.1.1 -> subuniverse_Type underlying_subu), (subuniverse_HProp underlying_subu ({x:A.1.1 & (B x).1.1} ; trunc_sigma (A.1.2) (λ x, (B x).1.2))).1)
                                              
                         }.

  
  Context `{ua: Univalence}.
  Context `{fs: Funext}.


  Definition O_rec_dep {n} {mod : Modality n} (subU := underlying_subu n mod)
             (A:Trunk n) (B: (O subU A).1.1 -> subuniverse_Type subU) (g : forall (a:A.1), (B (O_unit subU A a)).1.1)
  : {f : forall (z:(O subU A).1.1), (B z).1.1 & forall a:A.1, f (O_unit subU A a) = g a}.
    apply subuniverse_sigma. exact ua. exact fs.
    apply subu_sigma.
  Defined.
  
  Definition modal_contr_is_equiv n (mod : Modality n.+1) (subU := underlying_subu n.+1 mod) (X:Trunk n.+1) (Y : subuniverse_Type subU) (f : X.1 -> Y.1.1) (mod_contr_f : forall y, Contr (O subU (hfiber f y ; trunc_sigma (X.2) (λ x, trunc_succ (istrunc_paths (Y.1.2) (f x) y)))).1.1)
  : (O subU X).1.1 <~> Y.1.1.
    refine (equiv_adjointify _ _ _ _).
    - apply O_rec; exact f.
    - intro y.
      destruct (mod_contr_f y) as [c _]. simpl in *.
      revert c; apply O_rec; intros [c p].
      apply O_unit; exact c.
    - intro x.
      destruct (mod_contr_f x) as [c Tc]. simpl in *. clear Tc.
      revert c.
      transparent assert (sheaf_family : (((O subU
           (hfiber f x;
           trunc_sigma X.2
                       (λ x0 : X.1, trunc_succ (istrunc_paths (Y.1).2 (f x0) x)))).1).1 -> subuniverse_Type subU)).
      intro c.
      repeat refine (exist _ _ _).
      exact (O_rec X Y f
                   (O_rec
                      (hfiber f x;
                       trunc_sigma X.2
                                   (λ x0 : X.1, trunc_succ (istrunc_paths (Y.1).2 (f x0) x))) 
                      (O subU X) (λ X0 : hfiber f x, O_unit subU X X0.1) c) = x).
      apply istrunc_paths.
      apply trunc_succ. exact Y.1.2.
      apply subuniverse_paths.

      refine (O_rec_dep (hfiber f x;
           trunc_sigma X.2
                       (λ x0 : X.1, trunc_succ (istrunc_paths (Y.1).2 (f x0) x))) sheaf_family _).1.
      unfold sheaf_family; clear sheaf_family.
      intros [c p]. simpl.
      assert (p0 := ap10 (O_rec_retr (hfiber f x;
        trunc_sigma X.2
                    (λ x0 : X.1, trunc_succ (istrunc_paths (Y.1).2 (f x0) x))) (O subU X) (λ X0 : hfiber f x, O_unit subU X X0.1)) (c;p)).

      apply (transport (λ U, O_rec X Y f U = x) p0^); clear p0.
      exact ((ap10 (O_rec_retr X Y f) c) @ p).
    - intro x. destruct (mod_contr_f (O_rec X Y f x)) as [c Tc]. simpl in *.
      transparent assert (cc : ((O subU
               (hfiber f (O_rec X Y f x);
               trunc_sigma X.2
                 (λ x0 : X.1,
                         trunc_succ (istrunc_paths (Y.1).2 (f x0) (O_rec X Y f x))))).1).1).
      { clear Tc; clear c. revert x.
        pose proof (@O_rec_dep (n.+1) mod X (λ x, (O subU
       (hfiber f (O_rec X Y f x);
       trunc_sigma X.2
         (λ x0 : X.1,
                 trunc_succ (istrunc_paths (Y.1).2 (f x0) (O_rec X Y f x))))))).
        simpl in X0.
        refine (X0 _).1.
        intro x. simpl.
        apply O_unit. exists x.
        exact (ap10 (O_rec_retr X Y f) x)^. }
      Opaque O_rec_dep.
      simpl in cc.
      specialize (Tc cc). rewrite Tc.
      unfold cc. clear Tc; clear cc; clear c; simpl.
      fold subU.
      revert x.

      transparent assert (sheaf_family : ((O subU X).1.1 -> subuniverse_Type subU)).
      intro x. repeat refine (exist _ _ _).
      exact (O_rec
               (hfiber f (O_rec X Y f x);
                trunc_sigma X.2
                            (λ x0 : X.1, trunc_succ (istrunc_paths (Y.1).2 (f x0) (O_rec X Y f x))))
               (O subU X) (λ X0 : hfiber f (O_rec X Y f x), O_unit subU X X0.1)
               ((O_rec_dep X
                           (λ x0 : ((O subU X).1).1,
                                   O subU
                                     (hfiber f (O_rec X Y f x0);
                                      trunc_sigma X.2
                                                  (λ x1 : X.1,
                                                          trunc_succ (istrunc_paths (Y.1).2 (f x1) (O_rec X Y f x0)))))
                           (λ x0 : X.1,
                                   O_unit subU
                                          (hfiber f (O_rec X Y f (O_unit subU X x0));
                                           trunc_sigma X.2
                                                       (λ x1 : X.1,
                                                               trunc_succ
                                                                 (istrunc_paths (Y.1).2 (f x1)
                                                                                (O_rec X Y f (O_unit subU X x0)))))
                                          (x0; (ap10 (O_rec_retr X Y f) x0)^))).1 x) = x).
      apply istrunc_paths.
      apply trunc_succ. exact (O subU X).1.2.
      apply subuniverse_paths.
      
      refine (O_rec_dep X sheaf_family _).1.
      unfold sheaf_family in *; simpl in *; clear sheaf_family.
      intro x. simpl. 
      rewrite ((O_rec_dep X
         (λ x0 : ((O subU X).1).1,
          O subU
            (hfiber f (O_rec X Y f x0);
            trunc_sigma X.2
              (λ x1 : X.1,
               trunc_succ (istrunc_paths (Y.1).2 (f x1) (O_rec X Y f x0)))))
         (λ x0 : X.1,
          O_unit subU
            (hfiber f (O_rec X Y f (O_unit subU X x0));
            trunc_sigma X.2
              (λ x1 : X.1,
               trunc_succ
                 (istrunc_paths (Y.1).2 (f x1)
                    (O_rec X Y f (O_unit subU X x0)))))
            (x0; (ap10 (O_rec_retr X Y f) x0)^))).2 x).
      fold subU.
      exact (ap10 (O_rec_retr (hfiber f (O_rec X Y f (O_unit subU X x));
                               trunc_sigma X.2
                                           (λ x0 : X.1,
                                                   trunc_succ
                                                     (istrunc_paths (Y.1).2 (f x0) (O_rec X Y f (O_unit subU X x))))) (O subU X) (λ X0 : hfiber f (O_rec X Y f (O_unit subU X x)), O_unit subU X X0.1)) (x; (ap10 (O_rec_retr X Y f) x)^)).
  Defined.

  Definition O_contr n (mod : Modality n.+1) (subU := underlying_subu n.+1 mod) {X Y: Trunk n.+1} (f : X.1 -> Y.1)
    := forall y, Contr (O subU (hfiber f y ; trunc_sigma (X.2) (λ x, trunc_succ (istrunc_paths (Y.2) (f x) y)))).1.1.

  Definition O_unit_contr n (mod : Modality n.+1) (subU := underlying_subu n.+1 mod) (X:Trunk n.+1)
  : @O_contr n mod X (O subU X).1 (O_unit subU X).
    intros y.
  Admitted.
  
End Preliminary.

Section LexModality.

  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  Definition IsLex {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod)
    := forall (A:Trunk (trunc_S n)), forall (x y:A.1),
         Contr ((O subU A).1.1) -> Contr ((O subU (existT (IsTrunc n.+1) (x = y) (@trunc_succ n _ (@istrunc_paths A.1 n A.2 x y)))).1.1).

  Definition IsLex_contr_fibers {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) (islex : IsLex mod) {A B:Trunk n.+1} (f : A.1 -> B.1) (contrA : Contr (O subU A).1.1) (contrB : Contr (O subU B).1.1)
  : forall y:B.1, Contr (O subU (existT (λ T, IsTrunc n.+1 T) (hfiber f y) (trunc_sigma A.2 (λ a, istrunc_paths (trunc_succ (B.2)) _ _)))).1.1.
  Proof.
    intro y.
    destruct contrA as [a Ta], contrB as [b Tb].
    refine (BuildContr _ _ _).
    - generalize dependent a.
      transparent assert (modal_family : ((O subU A).1.1 -> subuniverse_Type subU)).
      { intro a.
        repeat refine (exist _ _ _).
        exact ((∀ y0 : ((O subU A).1).1, a = y0)
   → ((O subU
         (hfiber f y;
         trunc_sigma A.2
                     (λ a0 : A.1, istrunc_paths (trunc_succ B.2) (f a0) y))).1).1).
        apply trunc_arrow.
        exact _.2.
        apply subuniverse_arrow. exact ua. }
      
      refine (O_rec_dep A modal_family _).1.
      unfold modal_family; clear modal_family.
      intros a Ta.
  Admitted.
      
      

    

  Lemma islex_compat_func {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) (X Y:Trunk n.+1) (f: X.1 -> Y.1) (y:Y.1)
  : forall a:{a:X.1 & f a = y}, (function_lift subU X Y f (O_unit subU _ a.1) = O_unit subU Y y).
    intros a. simpl.
    pose (foo := ap10 (O_rec_retr X (O subU Y) (λ x : X .1, O_unit subU Y (f x))) a.1). 
    exact (transport (λ U, O_rec X (O subU Y) (λ x : X .1, O_unit subU Y (f x)) (O_unit subU X a.1) = O_unit subU Y U) a.2 foo).
  Defined.

  Lemma islex_to_hfibers_preservation {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) (islex : IsLex mod)
  : forall (X Y:Trunk n.+1) (f : X.1 -> Y.1) (y:Y.1), (O subU (existT (λ T, IsTrunc n.+1 T) (hfiber f y) (trunc_sigma X.2 (λ a, istrunc_paths (trunc_succ (Y.2)) _ _)))).1.1 = {rx : (O subU X).1.1 & function_lift subU X Y f rx = O_unit subU Y y}.
    intros X Y f y.
    apply path_universe_uncurried.
    transparent assert (TrΣ : (IsTrunc n.+1 (∃ rx : ((O subU X).1).1, function_lift subU X Y f rx = O_unit subU Y y))).
    { apply trunc_sigma.
      exact (O subU X).1.2.
      intro a. apply istrunc_paths.
      apply trunc_succ. exact (O subU Y).1.2. }
    assert (modalsigma : (subuniverse_HProp subU ((∃ rx : ((O subU X).1).1, function_lift subU X Y f rx = O_unit subU Y y);
                                                  trunc_sigma (O subU X).1.2 (λ x, istrunc_paths (trunc_succ ((O subU Y).1.2)) _ _)
                                                 )).1).
    
    { pose (subu_sigma _ mod (O subU X)).
      transparent assert (B : (((O subU X).1).1 → subuniverse_Type (underlying_subu n.+1 mod))).
      intro rx.
      exists (function_lift subU X Y f rx = O_unit subU Y y ; istrunc_paths (trunc_succ ( (O subU Y).1.2)) _ _).
      apply subuniverse_paths.
      
      pose subu_sigma. specialize (p0 (trunc_S n) mod (O subU X) B).
      apply p0. }

    refine (modal_contr_is_equiv n mod (hfiber f y;
                                        trunc_sigma X.2 (λ a : X.1, istrunc_paths (trunc_succ Y.2) (f a) y)) (((∃ rx : ((O subU X).1).1, function_lift subU X Y f rx = O_unit subU Y y);TrΣ);modalsigma) _ _); simpl.
    - intros u.
      exists (O_unit subU _ u.1).
      apply islex_compat_func.
    - intros [u p]. fold subU.
      assert (tr_hfiber : IsTrunc n.+1 (hfiber f y)).
      { apply trunc_sigma. exact X.2.
        intro a.
        apply istrunc_paths. apply trunc_succ. exact Y.2. }
      assert (tr_Ohfiber : IsTrunc n.+1 (∃ rx : ((O subU X).1).1, function_lift subU X Y f rx = O_unit subU Y y)).
      { apply trunc_sigma. exact _.1.2. intro a.
        apply istrunc_paths. apply trunc_succ. exact _.1.2. }
      match goal with
        |[|- Contr ((O subU (hfiber ?X (u;p); _)).1).1] => set (foo  := X) end.
      pose (@IsLex_contr_fibers n mod islex (hfiber f y; (trunc_sigma X.2
                                                                      (λ a : X.1, istrunc_paths (trunc_succ Y.2) (f a) y))) (∃ rx : ((O subU X).1).1, function_lift subU X Y f rx = O_unit subU Y y; tr_Ohfiber) foo). simpl in i.

      assert (trunc_sigma
                  (trunc_sigma X.2
                     (λ a : X.1, istrunc_paths (trunc_succ Y.2) (f a) y))
                  (λ a : hfiber f y,
                   istrunc_paths (trunc_succ tr_Ohfiber) (foo a) (u;p)) = trunc_sigma
           (trunc_sigma X.2
              (λ a : X.1, istrunc_paths (trunc_succ Y.2) (f a) y))
           (λ x : hfiber f y,
            trunc_succ
              (istrunc_paths TrΣ
                 (O_unit subU X x.1; islex_compat_func mod X Y f y x) 
                 (u; p)))).
      apply path_ishprop.

      apply (transport (λ U, Contr ((O subU (hfiber foo (u;p); U))).1.1) X0). clear X0.
      admit.
      (* refine (i _ _ _); unfold foo; clear i; clear foo. *)
      (* + clear tr_Ohfiber; clear tr_hfiber. *)
        
      

  Defined.


  Lemma islex_to_hfibers_preservation_compat {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) (islex : IsLex mod)
  : forall (X Y:Trunk n.+1) (f: X.1 -> Y.1) (y:Y.1) (a:{a:X.1 & f a = y}),
      ((equiv_path _ _ (islex_to_hfibers_preservation mod islex X Y f y)) o (O_unit subU _)) a = (O_unit subU _ a.1; islex_compat_func mod X Y f y a).
    simpl. intros X Y f y a.
    unfold islex_to_hfibers_preservation; simpl.
    unfold modal_contr_is_equiv.
    unfold equiv_adjointify.
    rewrite transport_path_universe_uncurried.

    pose (rew := λ P Q f, ap10 (O_rec_retr (n:=n.+1) (subU := subU) P Q f)).
    rewrite rew; clear rew.
    reflexivity.
  Qed.

End LexModality.
