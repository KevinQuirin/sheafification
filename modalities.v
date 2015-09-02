Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import reflective_subuniverse.

Set Universe Polymorphism.
Global Set Primitive Projections.

Local Open Scope path_scope.

(* Readability *)
Arguments trunc_arrow {H} {A} {B} {n} H0: simpl never.
Arguments trunc_sigma {A} {P} {n} H H0: simpl never.
Arguments istrunc_paths {A} {n} H x y: simpl never.
Arguments trunc_succ {n} {A} H _ _: simpl never.
          
Arguments O {n} subU T.
Arguments O_unit {n} subU T a.
Arguments subuniverse_Type {n} subU.

Section Preliminary.
  
  (* Defiinition 10, (v) *)
  Record Modality n := Build_Modality {
                               
                               underlying_subu : subuniverse_struct n ;
                               
                               subu_sigma : forall (A:subuniverse_Type underlying_subu) (B:A -> subuniverse_Type underlying_subu), IsSubu n underlying_subu (BuildTruncType n {x:A & B x})
                                            }.

  
  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  (* Proposition 11 *)
  Definition O_rec_dep {n} {mod : Modality n} (subU := underlying_subu n mod)
             (A:TruncType n) (B: (O subU A) -> subuniverse_Type subU) (g : forall (a:A), (B (O_unit subU A a)))
  : {f : forall (z:(O subU A)), (B z) & forall a:A, f (O_unit subU A a) = g a}.
    apply subuniverse_sigma. exact ua. exact fs.
    apply subu_sigma.
  Defined.

  (* Proposition 16, for HProps *)
  Definition hprop_stability {n} {mod : Modality n} (subU := underlying_subu n mod) (P:hProp) (t : IsTrunc n P)
  : IsHProp (O subU (@BuildTruncType n P t)).
    apply hprop_allpath.
    intros x.
    transparent assert (modf : ((O subU (@BuildTruncType n P t)) -> subuniverse_Type subU)).
    { intro y.
      refine (Build_subuniverse_Type _ subU (BuildTruncType n (x=y)) _). }
    refine (O_rec_dep _ modf _).1.
    intro y. unfold modf; clear modf; simpl.
    revert x.
    transparent assert (modf : ((O subU (@BuildTruncType n P t)) -> subuniverse_Type subU)).
    { intro x.
      refine (Build_subuniverse_Type _ subU (BuildTruncType n (x=O_unit subU _ y)) _). }
    refine (O_rec_dep _ modf _).1.
    intros x. unfold modf; clear modf; simpl in *.
    apply ap. refine (path_ishprop x y). 
  Defined.
  
  (* Lemma 13 *)
  Definition modal_contr_modal_is_equiv n (mod : Modality n.+1) (subU := underlying_subu n.+1 mod) (X:TruncType n.+1) (Y : subuniverse_Type subU) (f : X -> Y) (mod_contr_f : forall y, Contr (O subU (BuildTruncType (n.+1) (hfiber f y))))
  : (O subU X) <~> Y.
    refine (equiv_adjointify _ _ _ _).
    - apply O_rec; exact f.
    - intro y.
      destruct (mod_contr_f y) as [c _]. 
      revert c. apply O_rec; intros [c p]. 
      apply O_unit; exact c.
    - intro x.
      destruct (mod_contr_f x) as [c Tc].
      cbn in *. clear Tc.
      revert c.
      pose (sheaf_family := λ c, (Build_subuniverse_Type _ subU (BuildTruncType (n.+1) (O_rec (n.+1) subU X Y f
                   (O_rec (n.+1) subU 
                      (BuildTruncType (n.+1) (hfiber f x)) 
                      (O subU X) (λ X0 : hfiber f x, O_unit subU X X0.1) c) = x)) _)).
      refine (O_rec_dep (BuildTruncType (n.+1) (hfiber f x)) sheaf_family _).1.
      unfold sheaf_family; clear sheaf_family.
      intros [c p]. simpl.
      assert (p0 := ap10 (O_rec_retr (n.+1) subU (BuildTruncType (n.+1) (hfiber f x)) (O subU X) (λ X0 : hfiber f x, O_unit subU X X0.1)) (c;p)).

      apply (transport (λ U, O_rec (n.+1) subU X Y f U = x) p0^); clear p0.
      exact ((ap10 (O_rec_retr (n.+1) subU X Y f) c) @ p).
    - intro x. destruct (mod_contr_f (O_rec (n.+1) subU X Y f x)) as [c Tc]. simpl in *.
      transparent assert (cc : (O subU
               (BuildTruncType (n.+1) (hfiber f (O_rec (n.+1) subU X Y f x))))).
      { clear Tc; clear c. revert x.
        pose proof (@O_rec_dep (n.+1) mod X (λ x, (O subU
               (BuildTruncType (n.+1) (hfiber f (O_rec (n.+1) subU X Y f x)))))).
        simpl in X0.
        refine (X0 _).1.
        intro x. simpl.
        apply O_unit. exists x.
        exact (ap10 (O_rec_retr (n.+1) subU X Y f) x)^. }
      Opaque O_rec_dep.
      simpl in cc.
      specialize (Tc cc). rewrite Tc.
      unfold cc. clear Tc; clear cc; clear c; simpl.
      fold subU.
      revert x.
      pose (sheaf_family := λ x, (Build_subuniverse_Type (n.+1) subU
                                   (BuildTruncType (n.+1) (O_rec n.+1 subU
     {|
     trunctype_type := hfiber f (O_rec n.+1 subU X Y f x);
     istrunc_trunctype_type := trunc_sigma (istrunc_trunctype_type X)
                                 (λ a : X,
                                  istrunc_paths
                                    (trunc_succ (istrunc_trunctype_type Y))
                                    (f a) (O_rec n.+1 subU X Y f x)) |}
     (O subU X)
     (λ X0 : hfiber f (O_rec n.+1 subU X Y f x),
      O_unit subU X (let (proj1_sig, _) := X0 in proj1_sig))
     ((O_rec_dep X
         (λ x0 : O subU X,
          O subU
            {|
            trunctype_type := hfiber f (O_rec n.+1 subU X Y f x0);
            istrunc_trunctype_type := trunc_sigma (istrunc_trunctype_type X)
                                        (λ a : X,
                                         istrunc_paths
                                           (trunc_succ
                                              (istrunc_trunctype_type Y))
                                           (f a) (O_rec n.+1 subU X Y f x0)) |})
         (λ x0 : X,
          O_unit subU
            {|
            trunctype_type := hfiber f
                                (O_rec n.+1 subU X Y f (O_unit subU X x0));
            istrunc_trunctype_type := trunc_sigma (istrunc_trunctype_type X)
                                        (λ a : X,
                                         istrunc_paths
                                           (trunc_succ
                                              (istrunc_trunctype_type Y))
                                           (f a)
                                           (O_rec n.+1 subU X Y f
                                              (O_unit subU X x0))) |}
            (x0; (ap10 (O_rec_retr n.+1 subU X Y f) x0)^))).1 x) = x)) _)).
      refine (O_rec_dep X sheaf_family _).1.
      unfold sheaf_family in *; simpl in *; clear sheaf_family.
      intro x. simpl. 
      rewrite ((O_rec_dep X
         (λ x0 : O subU X,
          O subU
            {|
            trunctype_type := hfiber f (O_rec n.+1 subU X Y f x0);
            istrunc_trunctype_type := trunc_sigma (istrunc_trunctype_type X)
                                        (λ a : X,
                                         istrunc_paths
                                           (trunc_succ
                                              (istrunc_trunctype_type Y))
                                           (f a) (O_rec n.+1 subU X Y f x0)) |})
         (λ x0 : X,
          O_unit subU
            {|
            trunctype_type := hfiber f
                                (O_rec n.+1 subU X Y f (O_unit subU X x0));
            istrunc_trunctype_type := trunc_sigma (istrunc_trunctype_type X)
                                        (λ a : X,
                                         istrunc_paths
                                           (trunc_succ
                                              (istrunc_trunctype_type Y))
                                           (f a)
                                           (O_rec n.+1 subU X Y f
                                              (O_unit subU X x0))) |}
            (x0; (ap10 (O_rec_retr n.+1 subU X Y f) x0)^))).2 x).
      fold subU.
      exact (ap10 (O_rec_retr (n.+1) subU (BuildTruncType (n.+1) (hfiber f (O_rec (n.+1) subU X Y f (O_unit subU X x)))) (O subU X) (λ X0 : (hfiber f (O_rec (n.+1) subU X Y f (O_unit subU X x))), O_unit subU X X0.1)) (x; (ap10 (O_rec_retr (n.+1) subU X Y f) x)^)).
  Defined.

  (* Lemma 15 *)
  Lemma O_unit_O_contr_fibers {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) (X:TruncType n.+1) (Tr : forall x, IsTrunc n.+1 (hfiber (O_unit subU X) x))
  : forall x, Contr (O subU (@BuildTruncType (n.+1) (hfiber (O_unit subU X) x) (Tr x))).
    intros x.
    refine (BuildContr _ _ _).
    revert x.
    apply O_rec_dep.
    Opaque O_rec_dep.
    intro a. apply O_unit. simpl. exists a. reflexivity.
    intro y. simpl.
    revert y.
    transparent assert (shf : ((((O subU (@BuildTruncType (n.+1) (hfiber (O_unit subU X) x) (Tr x)))) -> subuniverse_Type subU))).
    { intro y.
      refine (Build_subuniverse_Type _ subU (BuildTruncType _ ((O_rec_dep X
      (λ z : O (underlying_subu n.+1 mod) X,
       O subU
         {|
         trunctype_type := hfiber (O_unit subU X) z;
         istrunc_trunctype_type := Tr z |})
      (λ a : X,
       O_unit subU
         {|
         trunctype_type := hfiber (O_unit subU X)
                             (O_unit (underlying_subu n.+1 mod) X a);
         istrunc_trunctype_type := Tr (O_unit (underlying_subu n.+1 mod) X a) |}
         (a; 1))).1 x = y)) _). }
    refine (O_rec_dep (@BuildTruncType (n.+1) (hfiber (O_unit subU X) x) (Tr x)) shf _).1.
    unfold shf; clear shf; simpl.
    intros [y p]. destruct p.
    match goal with
      |[|- ?XX.1 _ = _] => exact (XX.2 y)
    end.
  Defined.
  
  Global Instance is_modal_IsTrunc
        (n p: trunc_index)
        (mod : Modality (n.+1))
        (subU := underlying_subu _ mod)
        (trunc_prop : forall (T : subuniverse_Type subU), IsTrunc (n.+1) (IsTrunc p T))
        (T : subuniverse_Type subU)
    : IsSubu (n.+1) subU (@BuildTruncType (n.+1) (IsTrunc p T) (trunc_prop T)).
  Proof.
    revert T.
    induction p.
    - intros T.
      rewrite <- subuniverse_iff_O; [idtac | exact ua | exact fs].
      refine (isequiv_adjointify _ _ _ _).
      + intro X.
        refine (@contr_inhabited_hprop T _ _).
        apply hprop_allpath. intros x y.
        pose (sheaf := Build_subuniverse_Type (n.+1) subU (BuildTruncType _ (x=y)) _).
        revert X.
        apply (O_rec (n.+1) subU _ sheaf).
        intros [c pc]. unfold sheaf; clear sheaf. simpl.
        apply hprop_allpath.
        intros u v. exact ((pc u)^ @ (pc v)).
        revert X. apply O_rec.
        simpl.
        intros. exact (center _ X).
      + intro X. simpl.
        refine (path_ishprop _ _).
        transparent assert (hp : hProp).
        { exists (Contr (T)).
          apply hprop_trunc. }
        apply (hprop_stability (mod:=mod) hp (trunc_prop T)).
      + intro X. simpl.
        refine (path_ishprop _ _).
    - simpl in *. intros T.
      rewrite <- subuniverse_iff_O.
      refine (isequiv_adjointify _ _ _ _).
      + intro X.
        assert (trunc_pr : ∀ T : subuniverse_Type subU,
                             IsTrunc n.+1 (IsTrunc p T)).
        intro S. apply (@trunc_leq -1 (n.+1) tt _ _).
        simpl in *.
        intros x y.
        pose (sheaf := Build_subuniverse_Type (n.+1) subU (BuildTruncType (n.+1) (x=y)) _).
        specialize (IHp trunc_pr sheaf).
        unfold sheaf in *; clear sheaf. simpl in IHp.
        
        rewrite <- subuniverse_iff_O in IHp.
        apply (equiv_inv (IsEquiv := IHp)).
        revert X. apply O_rec.
        intros X. apply O_unit. exact (X x y). exact ua. exact fs.
      + intro X. simpl.
        refine (path_ishprop _ _).
        transparent assert (hp : hProp).
        { exists (IsTrunc p.+1 T).
          apply hprop_trunc. }
        apply (hprop_stability (mod:=mod) hp (trunc_prop T)).
      + intro X. simpl.
        refine (path_ishprop _ _).
      + exact ua.
      + exact fs.
  Defined.

  (* Section III.B : if [A] and [B] are modal and [f:A -> B], then [IsEquiv f] is modal *)
  Lemma is_modal_IsEquiv
        (n p: trunc_index)
        (mod : Modality (n.+1))
        (subU := underlying_subu _ mod)
        (trunc_prop : forall (A B : subuniverse_Type subU) (f:A -> B), IsTrunc (n.+1) (IsEquiv f))
  : forall (A B : subuniverse_Type subU) (f: A -> B), IsSubu (n.+1) subU (BuildTruncType (n.+1) (IsEquiv f)).
    intros A B f.
    rewrite <- subuniverse_iff_O.
    refine (isequiv_adjointify _ _ _ _).
    - intro H.
      refine (isequiv_adjointify _ _ _ _).
      + intro x. revert H.
        apply O_rec. intro H. simpl in H.
        exact (f^-1 x).
      + intro X.
        revert H. simpl.
        pose (shf := λ H, Build_subuniverse_Type (n.+1) subU (BuildTruncType (n.+1) (f
     (O_rec n.+1 subU
        {|
        trunctype_type := IsEquiv f;
        istrunc_trunctype_type := trunc_prop A B f |} A
        (λ H0 : IsEquiv f, f^-1 X) H) = X)) _).
        refine (O_rec_dep _ shf _).1.
        unfold shf; clear shf; simpl.
        intro H.
        pose (rew := λ P Q f, ap10 (O_rec_retr (n.+1) subU P Q f)).
        rewrite rew. rewrite eisretr. reflexivity.
      + intro X.
        revert H; simpl.
        pose (shf := λ H, Build_subuniverse_Type (n.+1) subU (BuildTruncType (n.+1) (O_rec n.+1 subU
                                                                                           {|
                                                                                             trunctype_type := IsEquiv f;
                                                                                             istrunc_trunctype_type := trunc_prop A B f |} A
                                                                                           (λ H0 : IsEquiv f, f^-1 (f X)) H = X)) _).
        
        refine (O_rec_dep _ shf _).1.
        unfold shf; clear shf; simpl.
        intro H.
        pose (rew := λ P Q f, ap10 (O_rec_retr (n.+1) subU P Q f)).
        rewrite rew. rewrite eissect. reflexivity.
    - intro X.
      refine (path_ishprop _ _).
      transparent assert (hp : hProp).
      { exists (IsEquiv f). apply hprop_isequiv. }
      exact (hprop_stability (mod := mod) hp (trunc_prop A B f)).
    - intro X.
      refine (path_ishprop _ _).
    - exact ua. - exact fs.
  Qed.
  
  
End Preliminary.

Section LexModality.

  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  Definition IsLex {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod)
    := forall (A:TruncType (trunc_S n)), forall (x y:A),
         Contr (O subU A) -> Contr (O subU (BuildTruncType (n.+1) (x=y))).

  Lemma IsHProp_IsLex {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod)
  : IsHProp (IsLex mod).
    refine trunc_forall.
  Defined.

  Lemma O_contr_sigma {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) {A : TruncType n.+1} {B : A -> TruncType n.+1}
        (contrA : Contr (O subU A))
        (contrB : forall a, Contr (O subU (B a)))
        (trΣ : IsTrunc n.+1 {a:A & (B a)})
  : Contr (O subU (BuildTruncType _ {a:A & (B a)})).
    refine (BuildContr _ _ _).
    - generalize (center (O subU A)).
      apply O_rec; intro a.
      generalize (center (O subU (B a))).
      apply O_rec; intro b.
      apply O_unit.
      exists a. exact b.
    - transparent assert (shf : ((O subU (BuildTruncType _ {a:A & (B a)})) -> subuniverse_Type subU)).
      { intro y. refine (Build_subuniverse_Type _ subU (BuildTruncType _ (O_rec n.+1 subU A
     (O subU
        {| trunctype_type := ∃ a : A, B a; istrunc_trunctype_type := trΣ |})
     (λ a : A,
      O_rec n.+1 subU (B a)
        (O subU
           {|
           trunctype_type := ∃ a0 : A, B a0;
           istrunc_trunctype_type := trΣ |})
        (λ b : B a,
         O_unit subU
           {|
           trunctype_type := ∃ a0 : A, B a0;
           istrunc_trunctype_type := trΣ |} (a; b)) 
        (center (O subU (B a)))) (center (O subU A)) = y))  _). }
      refine (O_rec_dep _ shf _).1.
      unfold shf; clear shf; intros [a b]; simpl.

      assert (X : (center (O subU A)) = O_unit subU A a) by apply contr.
      rewrite X; clear X.
      pose (rew := λ P Q f, ap10 (O_rec_retr (n.+1) (subU) P Q f)).
      rewrite rew.

      assert (X : (center (O subU (B a))) = O_unit subU (B a) b) by apply contr.
      rewrite X; clear X.
      rewrite rew.
      reflexivity.
  Qed.

  (* Lemma 14 *)
  Definition IsLex_contr_fibers {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) (islex : IsLex mod) {A B:TruncType n.+1} (f : A -> B) (contrA : Contr (O subU A)) (contrB : Contr (O subU B))
  : forall y:B, Contr (O subU (BuildTruncType (n.+1) (hfiber f y))).
  Proof.
    intro y.
    refine (@O_contr_sigma _ mod A (λ x, (BuildTruncType _ (f x = y))) _ _ _).
    (* exact contrA. *)
    intro a.
    (* assert (rew : trunc_succ (istrunc_paths B.2 (f a) y) = istrunc_paths (trunc_succ B.2) (f a) y) by apply path_ishprop. *)
    (* rewrite <- rew; clear rew. *)
    exact (islex B (f a) y contrB).
  Qed.

  Lemma islex_compat_func {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) (X Y:TruncType n.+1) (f: X -> Y) (y:Y)
  : forall a:{a:X & f a = y}, (function_lift _ subU X Y f (O_unit subU _ a.1) = O_unit subU Y y).
    intros a. simpl.
    pose (foo := ap10 (O_rec_retr _ subU X (O subU Y) (λ x : X, O_unit subU Y (f x))) a.1). 
    exact (transport (λ U, O_rec _ subU X (O subU Y) (λ x : X, O_unit subU Y (f x)) (O_unit subU X a.1) = O_unit subU Y U) a.2 foo).
  Defined.

  (* Proposition 12 *)
  Lemma islex_to_hfibers_preservation {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) (islex : IsLex mod)
  : forall (X Y:TruncType n.+1) (f : X -> Y) (y:Y), trunctype_type (@st _ subU (O subU (BuildTruncType _ (hfiber f y)))) = {rx : (O subU X) & function_lift _ subU X Y f rx = O_unit subU Y y}.
    intros X Y f y.
    apply path_universe_uncurried.
    refine (modal_contr_modal_is_equiv _
                                       mod
                                       (BuildTruncType _ (hfiber f y))
                                       (Build_subuniverse_Type _ subU (BuildTruncType (n.+1) (∃ rx : O subU X, function_lift n.+1 subU X Y f rx = O_unit subU Y y)) _)
                                       _ _).
    exact (subu_sigma _ mod (O subU X) (λ rx, Build_subuniverse_Type _ subU (BuildTruncType _ (function_lift n.+1 subU X Y f rx = O_unit subU Y y)) _)).
    cbn.
    - exact (@functor_hfiber _ _ _ _
               f
               (O_rec _ subU X (O subU Y) (O_unit subU Y o f))
               (O_unit subU X)
               (O_unit subU Y)
               (λ a, (ap10 (O_rec_retr _ subU X (O subU Y) (O_unit subU Y o f)) a)^)
               y
            ).
    - intros [rx p]. fold subU.
      pose (T' :=
              {z : (hfiber (O_unit subU X) rx) &
                   (@functor_hfiber _ _ _ _
                                    (O_unit subU X)
                                    (O_unit subU Y)
                                    f
                                    (O_rec _ subU X (O subU Y) (O_unit subU Y o f))
                                    (λ a, (ap10 (O_rec_retr _ subU X (O subU Y) (O_unit subU Y o f)) a))
                                    rx) z = (y;p^)}).
      assert (TrT': IsTrunc n.+1 T').
      { unfold T'.
        refine (trunc_sigma (n:=n.+1) _ _). }

      pose (oT' := O subU (BuildTruncType _ T')).
      refine (contr_equiv' oT' _).
      apply function_lift_equiv'. exact fs. apply equiv_inverse. simpl.
      unfold T', hfiber, functor_hfiber; simpl.
      apply equiv_path.
      pose
        (q := @hfiber_functor_hfiber _ _ _ _
                                     f
                                     (O_rec _ subU X (O subU Y) (O_unit subU Y o f))
                                     (O_unit subU X)
                                     (O_unit subU Y)
                                     (λ a, (ap10 (O_rec_retr _ subU X (O subU Y) (O_unit subU Y o f)) a)^)
                                     y
                                     rx
                                     p).
      etransitivity; try exact (path_universe_uncurried q). clear q.
      apply path_universe_uncurried.
      apply equiv_functor_sigma_id. intro a.
      unfold functor_hfiber.
      match goal with
      |[|- functor_sigma _ ?pp _ = _ <~> functor_sigma _ ?qq _ = _ ]
       => assert (rew: pp = qq)
      end.
      funext. hott_simpl.
      destruct rew.
      apply equiv_path; reflexivity.
      unfold oT', T'. simpl.
      unfold IsLex in islex.      
      assert (rew :trunc_sigma
                                            (istrunc_trunctype_type
                                               {|
                                               trunctype_type := hfiber
                                                  (O_unit subU X) rx;
                                               istrunc_trunctype_type := trunc_sigma
                                                  (istrunc_trunctype_type X)
                                                  (λ 
                                                  a : X,
                                                  istrunc_paths
                                                  (trunc_succ
                                                  (istrunc_trunctype_type
                                                  (O subU X)))
                                                  (O_unit subU X a) rx) |})
                                            (λ
                                             a : {|
                                                 trunctype_type := hfiber
                                                  (O_unit subU X) rx;
                                                 istrunc_trunctype_type := trunc_sigma
                                                  (istrunc_trunctype_type X)
                                                  (λ 
                                                  a : X,
                                                  istrunc_paths
                                                  (trunc_succ
                                                  (istrunc_trunctype_type
                                                  (O subU X)))
                                                  (O_unit subU X a) rx) |},
                                             istrunc_paths
                                               (trunc_succ
                                                  (istrunc_trunctype_type
                                                  {|
                                                  trunctype_type := hfiber
                                                  (O_unit subU Y)
                                                  (O_rec n.+1 subU X
                                                  (O subU Y)
                                                  (O_unit subU Y o f) rx);
                                                  istrunc_trunctype_type := trunc_sigma
                                                  (istrunc_trunctype_type Y)
                                                  (λ 
                                                  a0 : Y,
                                                  istrunc_paths
                                                  (trunc_succ
                                                  (istrunc_trunctype_type
                                                  (O subU Y)))
                                                  (O_unit subU Y a0)
                                                  (O_rec n.+1 subU X
                                                  (O subU Y)
                                                  (λ 
                                                  x : X, 
                                                  O_unit subU Y (f x)) rx)) |}))
                                               (functor_hfiber
                                                  (λ 
                                                  a0 : X,
                                                  ap10
                                                  (O_rec_retr n.+1 subU X
                                                  (O subU Y)
                                                  (λ 
                                                  x : X, 
                                                  O_unit subU Y (f x))) a0)
                                                  rx a) 
                                               (y; p^)) = TrT') by apply path_ishprop.
      rewrite <- rew; clear rew.
      refine (IsLex_contr_fibers mod
                                 islex
                                 (BuildTruncType _ (hfiber (O_unit subU X) rx))
                                 (B := BuildTruncType _ (hfiber (O_unit subU Y) (O_rec _ subU X (O subU Y) (O_unit subU Y o f) rx)))
                                 (f:= functor_hfiber
                                        (λ a : X,
                                               ap10
                                                 (O_rec_retr n.+1 subU X 
                                                             (O subU Y) (λ x : X, O_unit subU Y (f x)))
                                                 a) rx)
                                 _ _
                                 (y;p^)).

      exact (O_unit_O_contr_fibers mod X _ rx).
      exact (O_unit_O_contr_fibers mod Y _ (O_rec _ subU X (O subU Y) (O_unit subU Y o f) rx)).
  Defined.

  (* Proposition 12 *) 
  Lemma islex_to_hfibers_preservation_compat {n:trunc_index} (mod:Modality (trunc_S n)) (subU := underlying_subu (trunc_S n) mod) (islex : IsLex mod)
  : forall (X Y:TruncType n.+1) (f: X -> Y) (y:Y) (a:{a:X & f a = y}),
      ((equiv_path _ _ (islex_to_hfibers_preservation mod islex X Y f y)) o (O_unit subU _)) a = (O_unit subU _ a.1; islex_compat_func mod X Y f y a).
    simpl. intros X Y f y a.
    unfold islex_to_hfibers_preservation; simpl.
    unfold modal_contr_modal_is_equiv.
    unfold equiv_adjointify.
    rewrite transport_path_universe_uncurried.
    cbn.
    pose (rew := λ P Q f, ap10 (O_rec_retr (n.+1) subU P Q f)). 
    rewrite rew; clear rew.
    apply path_sigma' with 1. simpl. unfold islex_compat_func.
    simpl.
    rewrite transport_paths_FlFr.
    rewrite ap_const.
    hott_simpl.
  Qed.

End LexModality.
