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
          

Module Type Modality (subU : subuniverse_struct).
  Export subU.
  
  Parameter subu_sigma : forall sf:subu_family@{a}, (forall (A:Trunk@{i' i a} n) (modA : (subuniverse_HProp@{a i' i} sf A).1) (B:A.1 -> Trunk@{j' i a} n) (modB : forall a, (subuniverse_HProp@{a j' i} sf (B a)).1), (subuniverse_HProp@{a k' i} sf (({x:A.1 & (B x).1} ; trunc_sigma@{i i w i} (A.2) (λ x, (B x).2)) : Trunk@{k' i a} n)).1).
  Check subu_sigma@{a i' i j' k' w}.

  
  Parameter islex : forall sf:subu_family@{a}, forall (A:Trunk@{i' i a} n), forall (x y:A.1),
                      Contr ((O@{a i' i} sf A).1) -> Contr ((O@{a i' i} sf (existT (IsTrunc n) (x = y) ((@istrunc_paths A.1 n (trunc_succ A.2) x y)))).1).
  Check islex@{a i' i}.
End Modality.

Module Modality_theory (subU : subuniverse_struct) (mod : Modality subU).
  Export subU.
  Export mod.
  Module Export subU_RSProp := Reflective_Subuniverse subU.

  Section Preliminary.

    Definition ua := subU_RSProp.ua.
    Definition fs := subU_RSProp.fs.
  (* Context `{ua: Univalence}. *)
  (* Context `{fs: Funext}. *)

  Definition O_rec_dep 
             (A:Trunk n) (B: (O sf A).1 -> subuniverse_Type ) (g : forall (a:A.1), (B (O_unit sf A a)).1.1)
  : {f : forall (z:(O sf A).1), (B z).1.1 & forall a:A.1, f (O_unit sf A a) = g a}.
    apply subuniverse_sigma.
    intros A' B'.
    refine (subu_sigma _ _ _ _ _).
    exact A'.2.
    intro a; exact (B' a).2.
  Defined.
  
  Definition modal_contr_is_equiv (X:Trunk n) (Y : subuniverse_Type) (f : X.1 -> Y.1.1) (mod_contr_f : forall y, Contr (O sf (hfiber f y ; trunc_sigma (X.2) (λ x, (istrunc_paths (trunc_succ (Y.1.2)) (f x) y)))).1)
  : (O sf X).1 <~> Y.1.1.
    refine (equiv_adjointify _ _ _ _).
    - apply O_rec; [exact Y.2 | exact f].
    - intro y.
      destruct (mod_contr_f y) as [c _]. simpl in *.
      revert c; apply O_rec; [apply subuniverse_O | intros [c p]].
      apply O_unit; exact c.
    - intro x.
      destruct (mod_contr_f x) as [c Tc]. simpl in *. clear Tc.
      revert c.
      transparent assert (sheaf_family : (((O sf (hfiber f x;
        trunc_sigma X.2
          (λ x0 : X.1, istrunc_paths (trunc_succ (Y.1).2) (f x0) x))).1) -> subuniverse_Type)).
      intro c.
      refine (exist _ _ _).
      refine (exist _ (O_rec X Y.1 Y.2 f
                   (O_rec
                      (hfiber f x;
        trunc_sigma X.2
          (λ x0 : X.1, istrunc_paths (trunc_succ (Y.1).2) (f x0) x)) 
                      (O sf X) (subuniverse_O sf _) (λ X0 : hfiber f x, O_unit sf X X0.1) c) = x) _).
      apply istrunc_paths.
      apply trunc_succ. exact Y.1.2.
      apply subuniverse_paths.

      refine (O_rec_dep (hfiber f x;
        trunc_sigma X.2
          (λ x0 : X.1, istrunc_paths (trunc_succ (Y.1).2) (f x0) x)) sheaf_family _).1.
      unfold sheaf_family; clear sheaf_family.
      intros [c p]. simpl.
      assert (p0 := ap10 (O_rec_retr (hfiber f x;
        trunc_sigma X.2
          (λ x0 : X.1, istrunc_paths (trunc_succ (Y.1).2) (f x0) x)) (O sf X) (subuniverse_O sf _) (λ X0 : hfiber f x, O_unit sf X X0.1)) (c;p)).

      apply (transport (λ U, O_rec X Y.1 Y.2 f U = x) p0^); clear p0.
      exact ((ap10 (O_rec_retr X Y.1 Y.2 f) c) @ p).
    - intro x. destruct (mod_contr_f (O_rec X Y.1 Y.2 f x)) as [c Tc]. simpl in *.
      transparent assert (cc : ((O
               sf (hfiber f (O_rec X Y.1 Y.2 f x);
     trunc_sigma X.2
       (λ x0 : X.1, istrunc_paths (trunc_succ (Y.1).2) (f x0) (O_rec X Y.1 Y.2 f x)))).1)).
      { clear Tc; clear c. revert x.
        pose proof (@O_rec_dep  X (λ x, (O sf
       (hfiber f (O_rec X Y.1 Y.2 f x);
     trunc_sigma X.2
       (λ x0 : X.1, istrunc_paths (trunc_succ (Y.1).2) (f x0) (O_rec X Y.1 Y.2 f x))); subuniverse_O sf _))).
        simpl in X0.
        refine (X0 _).1.
        intro x. simpl.
        apply O_unit. exists x.
        exact (ap10 (O_rec_retr X Y.1 Y.2 f) x)^. }
      Opaque O_rec_dep.
      simpl in cc.
      specialize (Tc cc). rewrite Tc.
      unfold cc. clear Tc; clear cc; clear c; simpl.
      revert x.

      transparent assert (sheaf_family : ((O sf X).1 -> subuniverse_Type)).
      intro x.
      refine (exist _ _ _).
      refine (exist _ (O_rec
               (hfiber f (O_rec X Y.1 Y.2 f x);
     trunc_sigma X.2
       (λ x0 : X.1, istrunc_paths (trunc_succ (Y.1).2) (f x0) (O_rec X Y.1 Y.2 f x)))
               (O sf X) (subuniverse_O sf _) (λ X0 : hfiber f (O_rec X Y.1 Y.2 f x), O_unit sf X X0.1)
               ((O_rec_dep X
         (λ x0 : ((O sf X)).1,
          (O sf
            (hfiber f (O_rec X Y.1 Y.2 f x0);
            trunc_sigma X.2
              (λ x1 : X.1,
               istrunc_paths (trunc_succ (Y.1).2) (f x1) (O_rec X Y.1 Y.2 f x0))); subuniverse_O sf _))
         (λ x0 : X.1,
          O_unit sf
            (hfiber f (O_rec X Y.1 Y.2 f (O_unit sf X x0));
            trunc_sigma X.2
              (λ x1 : X.1,
               istrunc_paths (trunc_succ (Y.1).2) (f x1)
                 (O_rec X Y.1 Y.2 f (O_unit sf X x0))))
            (x0; (ap10 (O_rec_retr X Y.1 Y.2 f) x0)^))).1 x) = x) _).
      apply istrunc_paths.
      apply trunc_succ. exact (O sf X).2.
      simpl.
      refine (subuniverse_paths (O sf X; subuniverse_O sf X) _ _).
      
      refine (O_rec_dep X sheaf_family _).1.
      unfold sheaf_family in *; simpl in *; clear sheaf_family.
      intro x. simpl. 
      rewrite ((O_rec_dep X
         (λ x0 : ((O sf X)).1,
          (O sf
            (hfiber f (O_rec X Y.1 Y.2 f x0);
            trunc_sigma X.2
              (λ x1 : X.1,
               istrunc_paths (trunc_succ (Y.1).2) (f x1) (O_rec X Y.1 Y.2 f x0))); subuniverse_O sf _))
         (λ x0 : X.1,
          O_unit sf
            (hfiber f (O_rec X Y.1 Y.2 f (O_unit sf X x0));
            trunc_sigma X.2
              (λ x1 : X.1,
               istrunc_paths (trunc_succ (Y.1).2) (f x1)
                 (O_rec X Y.1 Y.2 f (O_unit sf X x0))))
            (x0; (ap10 (O_rec_retr X Y.1 Y.2 f) x0)^))).2 x).
      exact (ap10 (O_rec_retr (hfiber f (O_rec X Y.1 Y.2 f (O_unit sf X x));
     trunc_sigma X.2
       (λ x0 : X.1,
        istrunc_paths (trunc_succ (Y.1).2) (f x0) (O_rec X Y.1 Y.2 f (O_unit sf X x)))) (O sf X) (subuniverse_O sf _) (λ X0 : hfiber f (O_rec X Y.1 Y.2 f (O_unit sf X x)), O_unit sf X X0.1)) (x; (ap10 (O_rec_retr X Y.1 Y.2 f) x)^)).
  Defined.

  Definition O_contr {X Y: Trunk n} (f : X.1 -> Y.1)
    := forall y, Contr (O sf (hfiber f y ; trunc_sigma (X.2) (λ x, (istrunc_paths ((trunc_succ Y.2)) (f x) y)))).1.

  Definition O_unit_contr (X:Trunk n)
  : @O_contr X (O sf X) (O_unit sf X).
    intros y.
  Admitted.
  
  End Preliminary.

  Definition IsLex_contr_fibers  {A B:Trunk n} (f : A.1 -> B.1) (contrA : Contr (O sf A).1) (contrB : Contr (O sf B).1)
  : forall y:B.1, Contr (O sf (existT (λ T, IsTrunc n T) (hfiber f y) (trunc_sigma A.2 (λ a, istrunc_paths (trunc_succ (B.2)) _ _)))).1.
  Proof.
    intro y.
    destruct contrA as [a Ta], contrB as [b Tb].
    refine (BuildContr _ _ _).
    - generalize dependent a.
      transparent assert (modal_family : ((O sf A).1 -> subuniverse_Type )).
      { intro a.
        refine (exist _ _ _).
        refine (exist _ ((∀ y0 : ((O sf A)).1, a = y0)
               → ((O sf
                     (hfiber f y;
                      trunc_sigma A.2
                                  (λ a0 : A.1, istrunc_paths (trunc_succ B.2) (f a0) y)))).1) _).
        apply trunc_arrow.
        exact _.2.
        exact (subuniverse_arrow (∀ y0 : ((O sf A)).1, a = y0) ((O sf
             (hfiber f y;
             trunc_sigma A.2
               (λ a0 : A.1, istrunc_paths (trunc_succ B.2) (f a0) y))); subuniverse_O sf _)). }
      
      refine (O_rec_dep A modal_family _).1.
      unfold modal_family; clear modal_family.
      intros a Ta.
  Admitted.
      
  Lemma islex_compat_func (X Y:Trunk n) (f: X.1 -> Y.1) (y:Y.1)
  : forall a:{a:X.1 & f a = y}, (function_lift X Y f (O_unit sf _ a.1) = O_unit sf Y y).
    intros a. simpl.
    pose (foo := ap10 (O_rec_retr X (O sf Y) (subuniverse_O sf _) (λ x : X .1, O_unit sf Y (f x))) a.1). 
    exact (transport (λ U, O_rec X (O sf Y) (subuniverse_O sf _)  (λ x : X .1, O_unit sf Y (f x)) (O_unit sf X a.1) = O_unit sf Y U) a.2 foo).
  Defined.

  Lemma islex_to_hfibers_preservation 
  : forall (X Y:Trunk n) (f : X.1 -> Y.1) (y:Y.1), (O sf (existT (λ T, IsTrunc n T) (hfiber f y) (trunc_sigma X.2 (λ a, istrunc_paths (trunc_succ (Y.2)) _ _)))).1 = {rx : (O sf X).1 & function_lift X Y f rx = O_unit sf Y y}.
    intros X Y f y.
    apply path_universe_uncurried.
    transparent assert (TrΣ : (IsTrunc n (∃ rx : ((O sf X)).1, function_lift X Y f rx = O_unit sf Y y))).
    { apply trunc_sigma.
      exact (O sf X).2.
      intro a. apply istrunc_paths.
      apply trunc_succ. exact (O sf Y).2. }
    assert (modalsigma : (subuniverse_HProp sf ((∃ rx : ((O sf X)).1, function_lift X Y f rx = O_unit sf Y y);
                                                  trunc_sigma (O sf X).2 (λ x, istrunc_paths (trunc_succ ((O sf Y).2)) _ _)
                                                 )).1).
    
    { pose (subu_sigma sf (O sf X)).
      transparent assert (B : (((O sf X)).1 → subuniverse_Type)).
      intro rx.
      exists (function_lift X Y f rx = O_unit sf Y y ; istrunc_paths (trunc_succ ( (O sf Y).2)) _ _).
      refine (subuniverse_paths (O sf Y; subuniverse_O sf _) _ _).
      apply (subu_sigma sf (O sf X) (subuniverse_O sf _) (pr1 o B)).
      intro a. exact (B a).2. }

    refine (modal_contr_is_equiv (hfiber f y;
                                        trunc_sigma X.2 (λ a : X.1, istrunc_paths (trunc_succ Y.2) (f a) y)) (((∃ rx : ((O sf X)).1, function_lift X Y f rx = O_unit sf Y y);TrΣ);modalsigma) _ _); simpl.
    - intros u.
      exists (O_unit sf _ u.1).
      apply islex_compat_func.
    - intros [u p]. 
      assert (tr_hfiber : IsTrunc n (hfiber f y)).
      { apply trunc_sigma. exact X.2.
        intro a.
        apply istrunc_paths. apply trunc_succ. exact Y.2. }
      assert (tr_Ohfiber : IsTrunc n (∃ rx : ((O sf X)).1, function_lift X Y f rx = O_unit sf Y y)).
      { apply trunc_sigma. exact _.2. intro a.
        apply istrunc_paths. apply trunc_succ. exact _.2. }
      match goal with
        |[|- Contr ((O sf (hfiber ?X (u;p); _)).1)] => set (foo  := X) end.
      pose (@IsLex_contr_fibers (hfiber f y; (trunc_sigma X.2
                                                                      (λ a : X.1, istrunc_paths (trunc_succ Y.2) (f a) y))) (∃ rx : ((O sf X)).1, function_lift X Y f rx = O_unit sf Y y; tr_Ohfiber) foo). simpl in i.

      assert (trunc_sigma
                  (trunc_sigma X.2
                     (λ a : X.1, istrunc_paths (trunc_succ Y.2) (f a) y))
                  (λ a : hfiber f y,
                   istrunc_paths (trunc_succ tr_Ohfiber) (foo a) (u;p)) = trunc_sigma
           (trunc_sigma X.2
              (λ a : X.1, istrunc_paths (trunc_succ Y.2) (f a) y))
           (λ x : hfiber f y,
            istrunc_paths (trunc_succ TrΣ)
              (O_unit sf X x.1; islex_compat_func X Y f y x) 
              (u; p))).
      apply path_ishprop.

      apply (transport (λ U, Contr ((O sf (hfiber foo (u;p); U))).1) X0). clear X0.
      admit.
      (* refine (i _ _ _); unfold foo; clear i; clear foo. *)
      (* + clear tr_Ohfiber; clear tr_hfiber. *)
        
      

  Defined.


  Lemma islex_to_hfibers_preservation_compat 
  : forall (X Y:Trunk n) (f: X.1 -> Y.1) (y:Y.1) (a:{a:X.1 & f a = y}),
      ((equiv_path _ _ (islex_to_hfibers_preservation X Y f y)) o (O_unit sf _)) a = (O_unit sf _ a.1; islex_compat_func X Y f y a).
    simpl. intros X Y f y a.
    unfold islex_to_hfibers_preservation; simpl.
    unfold modal_contr_is_equiv.
    unfold equiv_adjointify.
    rewrite transport_path_universe_uncurried.

    pose (rew := λ P Q modQ f, ap10 (O_rec_retr P Q modQ f)).
    unfold O_rec.
    rewrite rew; clear rew.
    reflexivity.
  Qed.

End Modality_theory.
