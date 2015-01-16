Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import equivalence univalence lemmas sub_object_classifier epi_mono cech_nerve reflective_subuniverse.

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

  Definition hprop_stability {n} {mod : Modality n} (subU := underlying_subu n mod) (P:HProp) (t : IsTrunc n P.1)
  : IsHProp (O subU (P.1;t)).1.1.
    apply hprop_allpath.
    intros x.
    transparent assert (modf : ((O subU (P.1;t)).1.1 -> subuniverse_Type subU)).
    { intro y.
      refine (exist _ _ _).
      exists (x = y).
      apply istrunc_paths.
      apply trunc_succ. exact _.2.
      refine (subuniverse_paths (((O subU (P.1; t))) : subuniverse_Type subU) x y). }
    refine (O_rec_dep _ modf _).1.
    intro y. unfold modf; clear modf; simpl.
    revert x.
    transparent assert (modf : ((O subU (P.1;t)).1.1 -> subuniverse_Type subU)).
    { intro x.
      refine (exist _ _ _).
      exists (x = O_unit subU _ y).
      apply istrunc_paths.
      apply trunc_succ. exact _.2.
      refine (subuniverse_paths (((O subU (P.1; t))) : subuniverse_Type subU) x (O_unit subU _ y)). }
    refine (O_rec_dep _ modf _).1.
    intros x. unfold modf; clear modf; simpl in *.
    apply ap. refine (path_ishprop x y). exact P.2.
  Defined.
  
  Definition modal_contr_modal_is_equiv n (mod : Modality n.+1) (subU := underlying_subu n.+1 mod) (X:Trunk n.+1) (Y : subuniverse_Type subU) (f : X.1 -> Y.1.1) (mod_contr_f : forall y, Contr (O subU (hfiber f y ; trunc_sigma (X.2) (λ x, trunc_succ (istrunc_paths (Y.1.2) (f x) y)))).1.1)
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
      exact ua.
      exact fs.

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
      apply subuniverse_paths. exact ua. exact fs.
      
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

  Lemma is_modal_IsTrunc
        (n p: trunc_index)
        (mod : Modality (n.+1))
        (subU := underlying_subu _ mod)
        (trunc_prop : forall (T : subuniverse_Type subU), IsTrunc (n.+1) (IsTrunc p T.1.1))
  : forall (T : subuniverse_Type subU), (subuniverse_HProp subU (existT (IsTrunc n.+1) (IsTrunc p T.1.1) (trunc_prop T))).1.
    induction p.
    - intros T.
      rewrite <- subuniverse_iff_O; [idtac | exact ua | exact fs].
      refine (isequiv_adjointify _ _ _ _).
      + intro X.
        refine (@contr_inhabited_hprop (T.1.1) _ _).
        apply hprop_allpath. intros x y.
        transparent assert (sheaf : (subuniverse_Type subU)).
        { refine (exist _ _ _).
          refine (exist _ (x=y) _).
          apply istrunc_paths. apply trunc_succ. exact T.1.2.
          apply subuniverse_paths. exact ua. exact fs. }
        revert X.
        apply (O_rec _ sheaf).
        intros [c pc]. unfold sheaf. simpl.
        apply hprop_allpath.
        intros u v. exact ((pc u)^ @ (pc v)).

        revert X. apply O_rec.
        simpl.
        intros. exact (center _ X).
      + intro X. simpl.
        refine (path_ishprop _ _).
        transparent assert (hp : HProp).
        { exists (Contr (T.1.1)).
          apply hprop_trunc. }
        apply (hprop_stability (mod:=mod) hp (trunc_prop T)).
      + intro X. simpl.
        refine (path_ishprop _ _).
    - simpl in *. intros T.
      rewrite <- subuniverse_iff_O.
      refine (isequiv_adjointify _ _ _ _).
      + intro X.
        assert (trunc_pr : ∀ T : subuniverse_Type subU,
                             IsTrunc n.+1 (IsTrunc p (T.1).1)).
        intro S. apply IsHProp_IsTrunc. apply hprop_trunc.
        unfold IsTrunc in *.
        intros x y.
        simpl in *.
        transparent assert (sheaf : (subuniverse_Type subU)).
        { repeat refine (exist _ _ _).
          exact (x = y).
          apply istrunc_paths. apply trunc_succ. exact T.1.2.
          apply subuniverse_paths. exact ua. exact fs. }
        specialize (IHp trunc_pr sheaf).
        unfold sheaf in *; clear sheaf. simpl in IHp.
        
        rewrite <- subuniverse_iff_O in IHp.
        apply (equiv_inv (IsEquiv := IHp)).
        revert X. apply O_rec.
        intros X. apply O_unit. exact (X x y). exact ua. exact fs.
      + intro X. simpl.
        refine (path_ishprop _ _).
        transparent assert (hp : HProp).
        { exists (IsTrunc p.+1 (T.1).1).
          apply hprop_trunc. }
        apply (hprop_stability (mod:=mod) hp (trunc_prop T)).
      + intro X. simpl.
        refine (path_ishprop _ _).
      + exact ua.
      + exact fs.
  Defined.

  Lemma O_unit_O_contr_fibers {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) (X:Trunk n.+1) (Tr : forall x, IsTrunc n.+1 (hfiber (O_unit subU X) x))
  : forall x, Contr (O subU (hfiber (O_unit subU X) x; Tr x)).1.1.
    intros x.
    refine (BuildContr _ _ _).
    revert x.
    apply O_rec_dep.
    Opaque O_rec_dep.
    intro a. apply O_unit. simpl. exists a. reflexivity.
    intro y. simpl.
    revert y.
    transparent assert (shf : ((((O subU (hfiber (O_unit subU X) x; Tr x)).1).1 -> subuniverse_Type subU))).
    { intro y. refine (exist _ _ _).
      exists ((O_rec_dep X
    (λ z : ((O (underlying_subu n.+1 mod) X).1).1,
     O subU (hfiber (O_unit subU X) z; Tr z))
    (λ a : X.1,
     O_unit subU
       (hfiber (O_unit subU X) (O_unit (underlying_subu n.+1 mod) X a);
       Tr (O_unit (underlying_subu n.+1 mod) X a)) 
       (a; 1))).1 x = y).
      apply istrunc_paths. apply trunc_succ. exact _.2.
      apply subuniverse_paths. exact ua. exact fs. }
    refine (O_rec_dep (hfiber (O_unit subU X) x; Tr x) shf _).1.
    unfold shf; clear shf; simpl.
    intros [y p]. destruct p.
    match goal with
      |[|- ?XX.1 _ = _] => exact (XX.2 y)
    end.
  Defined.
  
End Preliminary.

Section LexModality.

  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  Definition IsLex {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod)
    := forall (A:Trunk (trunc_S n)), forall (x y:A.1),
         Contr ((O subU A).1.1) -> Contr ((O subU (existT (IsTrunc n.+1) (x = y) (@trunc_succ n _ (@istrunc_paths A.1 n A.2 x y)))).1.1).

  Lemma IsHProp_IsLex {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod)
  : IsHProp (IsLex mod).
    refine trunc_forall.
  Defined.

  Lemma O_contr_sigma {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) {A : Trunk n.+1} {B : A.1 -> Trunk n.+1}
        (contrA : Contr (O subU A).1.1)
        (contrB : forall a, Contr (O subU (B a)).1.1)
        (trΣ : IsTrunc n.+1 {a:A.1 & (B a).1})
  : Contr (O subU ({a:A.1 & (B a).1};trΣ)).1.1.
    refine (BuildContr _ _ _).
    - generalize (center (O subU A).1.1).
      apply O_rec; intro a.
      generalize (center (O subU (B a)).1.1).
      apply O_rec; intro b.
      apply O_unit.
      exists a. exact b.
    - transparent assert (shf : (((O subU (∃ a : A.1, (B a).1; trΣ)).1).1 -> subuniverse_Type subU)).
      { intro y. refine (exist _ _ _).
        exists (O_rec A (O subU (∃ a : A.1, (B a).1; trΣ))
   (λ a : A.1,
    O_rec (B a) (O subU (∃ a0 : A.1, (B a0).1; trΣ))
      (O_unit subU (∃ a0 : A.1, (B a0).1; trΣ) o exist (pr1 o B) a)
      (center ((O subU (B a)).1).1)) (center ((O subU A).1).1) = y).
        apply istrunc_paths; apply trunc_succ; exact _.2.
        apply subuniverse_paths; [exact ua | exact fs]. }
      refine (O_rec_dep _ shf _).1.
      unfold shf; clear shf; intros [a b]; simpl.

      assert (X : (center ((O subU A).1).1) = O_unit subU A a) by apply contr.
      rewrite X; clear X.
      pose (rew := λ P Q f, ap10 (O_rec_retr (n:=n.+1) (subU:=subU) P Q f)).
      rewrite rew.

      assert (X : (center ((O subU (B a)).1).1) = O_unit subU (B a) b) by apply contr.
      rewrite X; clear X.
      rewrite rew.
      reflexivity.
  Qed.
                                                                     
  Definition IsLex_contr_fibers {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) (islex : IsLex mod) {A B:Trunk n.+1} (f : A.1 -> B.1) (contrA : Contr (O subU A).1.1) (contrB : Contr (O subU B).1.1)
  : forall y:B.1, Contr (O subU (existT (λ T, IsTrunc n.+1 T) (hfiber f y) (trunc_sigma A.2 (λ a, istrunc_paths (trunc_succ (B.2)) _ _)))).1.1.
  Proof.
    intro y.
    apply (λ C1 C2, @O_contr_sigma _ mod A (λ x, (f x = y; istrunc_paths (trunc_succ B.2) _ _)) C1 C2 (trunc_sigma A.2 (λ a : A.1, istrunc_paths (trunc_succ B.2) (f a) y))).
    exact contrA.
    intro a.
    assert (rew : trunc_succ (istrunc_paths B.2 (f a) y) = istrunc_paths (trunc_succ B.2) (f a) y) by apply path_ishprop.
    rewrite <- rew; clear rew.
    exact (islex B (f a) y contrB).
  Qed.

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
      apply subuniverse_paths. exact ua. exact fs.
      
      pose subu_sigma. specialize (p0 (trunc_S n) mod (O subU X) B).
      apply p0. }

    refine (modal_contr_modal_is_equiv n mod (hfiber f y;
                                        trunc_sigma X.2 (λ a : X.1, istrunc_paths (trunc_succ Y.2) (f a) y)) (((∃ rx : ((O subU X).1).1, function_lift subU X Y f rx = O_unit subU Y y);TrΣ);modalsigma) _ _); simpl.
    - exact (square_fiber_map (f:=f)
                              (O_rec X (O subU Y) (O_unit subU Y o f))
                              (O_unit subU X)
                              (O_unit subU Y)
                              (λ a, (ap10 (O_rec_retr X (O subU Y) (O_unit subU Y o f)) a)^)
                              (b:=y)).
    - intros [rx p]. fold subU.
      pose (T' :=
              {z : (hfiber (O_unit subU X) rx) &
                   (square_fiber_map (f:=(O_unit subU X))
                               (O_unit subU Y)
                               f
                               (O_rec X (O subU Y) (O_unit subU Y o f))
                               (λ a, (ap10 (O_rec_retr X (O subU Y) (O_unit subU Y o f)) a))
                               (b:=rx) z) = (y;p^)}).
      assert (TrT': IsTrunc n.+1 T').
      { unfold T'.
        refine (trunc_sigma (n:=n.+1) _ _).
        refine (trunc_sigma _ _). exact X.2. intro a.
        apply istrunc_paths; apply trunc_succ; exact _.2.
        intro a.
        apply istrunc_paths; apply trunc_succ.
        refine (trunc_sigma _ _). exact Y.2. intro b.
        apply istrunc_paths; apply trunc_succ; exact _.2. }

      pose (oT' := O subU (T';TrT')).
      refine (contr_equiv' oT'.1.1 _).
      apply function_lift_equiv'. exact fs. apply equiv_inverse. simpl.
      unfold T', hfiber, square_fiber_map; simpl.
      hott_simpl.
      (* This is done in https://github.com/HoTT/HoTT/blob/master/contrib/old/FiberSequences.v  by three_by_three *)

      admit.

      unfold oT', T'. simpl.
      unfold IsLex in islex.
      assert (Tr_fibηX : forall rx, IsTrunc n.+1 (hfiber (O_unit subU X) rx)).
      { intros rxx. refine (trunc_sigma _ _).
        exact _.2.
        intro a. apply istrunc_paths; apply trunc_succ; exact _.2. }
      assert (Tr_fibηY : IsTrunc n.+1 (hfiber (O_unit subU Y) (O_rec X (O subU Y) (O_unit subU Y o f) rx))).
      { refine (trunc_sigma _ _).
        exact _.2.
        intro a. apply istrunc_paths; apply trunc_succ; exact _.2. }
      
      assert (rew :trunc_sigma (Tr_fibηX rx)
                  (λ a : ∃ x : X.1, O_unit subU X x = rx,
                   istrunc_paths (trunc_succ Tr_fibηY)
                     (square_fiber_map (f:=(O_unit subU X))
                        (O_unit subU Y) f
                        (O_rec X (O subU Y) (O_unit subU Y o f))
                        (λ a0 : X.1,
                         ap10 (O_rec_retr X (O subU Y) (O_unit subU Y o f))
                              a0) (b:=rx) a) (y; p^)) = TrT'). apply path_ishprop.
      rewrite <- rew; clear rew.
      apply (λ C1 C2, IsLex_contr_fibers mod islex
                               (hfiber (O_unit subU X) rx;Tr_fibηX rx)
                               (B := (hfiber (O_unit subU Y) (O_rec X (O subU Y) (O_unit subU Y o f) rx); Tr_fibηY))
                               (f := square_fiber_map (f:=(O_unit subU X)) (O_unit subU Y) f
                                                 (O_rec X (O subU Y) (O_unit subU Y o f))
                                                 (λ a : X.1, ap10 (O_rec_retr X (O subU Y) (O_unit subU Y o f)) a)
                                                 (b:=rx))
                               C1
                               C2
                               (y;p^)

           ).

      assert (Trr : (∀ x : ((O (underlying_subu n.+1 mod) X).1).1,
            IsTrunc n.+1
                    (∃ x0 : X.1, O_unit (underlying_subu n.+1 mod) X x0 = x))).
      { intro x. refine (trunc_sigma _ _).
        exact _.2. intro a.
        apply istrunc_paths; apply trunc_succ; exact _.2. }
      pose (i := O_unit_O_contr_fibers mod X Trr rx). unfold hfiber in i.
      assert (rew : Trr rx = Tr_fibηX rx) by apply path_ishprop. rewrite <- rew; clear rew.
      exact i.

      assert (Trr : ∀ x : ((O (underlying_subu n.+1 mod) Y).1).1,
                      IsTrunc n.+1 (hfiber (O_unit (underlying_subu n.+1 mod) Y) x)).
      { intro x. refine (trunc_sigma _ _).
        exact _.2. intro a.
        apply istrunc_paths; apply trunc_succ; exact _.2. }
      pose (i := O_unit_O_contr_fibers mod Y Trr (O_rec X (O subU Y) (O_unit subU Y o f) rx)).
      assert (rew : Trr (O_rec X (O subU Y) (O_unit subU Y o f) rx) = Tr_fibηY) by apply path_ishprop. rewrite <- rew; clear rew.
      exact i.      
  Defined.

 
  Lemma islex_to_hfibers_preservation_compat {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) (islex : IsLex mod)
  : forall (X Y:Trunk n.+1) (f: X.1 -> Y.1) (y:Y.1) (a:{a:X.1 & f a = y}),
      ((equiv_path _ _ (islex_to_hfibers_preservation mod islex X Y f y)) o (O_unit subU _)) a = (O_unit subU _ a.1; islex_compat_func mod X Y f y a).
    simpl. intros X Y f y a.
    unfold islex_to_hfibers_preservation; simpl.
    unfold modal_contr_modal_is_equiv.
    unfold equiv_adjointify.
    rewrite transport_path_universe_uncurried.

    pose (rew := λ P Q f, ap10 (O_rec_retr (n:=n.+1) (subU := subU) P Q f)).
    rewrite rew; clear rew.
    unfold square_fiber_map.
    apply path_sigma' with 1. simpl. unfold islex_compat_func.
    simpl.
    Unset Printing Notations.
    pose (p := @transport_paths_FlFr).
    rewrite p.
    Set Printing Notations.
    rewrite ap_const.
    hott_simpl.
  Qed.

End LexModality.
