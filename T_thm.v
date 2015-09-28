(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import T.

Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
Local Open Scope type_scope.

Definition tp_foo {A B} (f: A -> B) (Mono_f : IsMono f) (a b:A) (p:f a = f b)
  : tp a b p = ap t (equiv_inv (ap (x:=a) (y:=b) f) (IsEquiv := Mono_f a b) p).
Proof.
  path_via (tp a b ((ap (x:=a) (y:=b) f) (equiv_inv (ap (x:=a) (y:=b) f) (IsEquiv := Mono_f a b) p))).
  apply ap. symmetry; apply eisretr.
  generalize (equiv_inv (ap (x:=a) (y:=b) f) (IsEquiv := Mono_f a b) p).
  intro q. destruct q. cbn. apply tp_1.
Defined.

Definition tp_bar {A B} (f: A -> B) (Mono_f : IsMono f) 
  : IsMono (t: A -> T f).
Proof.
  intros a b.

  transparent assert (Cover : (T f -> Type)).
  { refine (T_rec _ _ _ _).
    intro e; exact (a=e).
    intros x y p. cbn.

    destruct (equiv_inv _ (IsEquiv := Mono_f x y)). exact p.
    reflexivity.

    intros x. cbn.

    match goal with
    |[|- match ?XX in (_=y) return _ with
         |_ => _
         end _ = _] => assert (1 = XX)
    end.
    symmetry; apply moveR_equiv_V. reflexivity.

    destruct X. reflexivity. }

  transparent assert (encode : (forall e:T f, forall q:t a = e, Cover e)).
  { exact (λ e, λ q, transport Cover q 1). }

  transparent assert (decode : (forall e:T f, forall q:Cover e, t a = e)).
  { refine (T_ind _ _ _ _).
    intros e q. cbn in q. exact (ap t q).
    intros x y p.
    cbn.
    apply path_forall; intro u.
    pose (i := ap (x:=x) (y:=y) f).
    pose (i' := equiv_inv (ap (x:=x) (y:=y) f) (IsEquiv := Mono_f x y)).
    
    path_via (transport (λ w : T f, Cover w → t a = w) (tp x y (i (i' p))) 
                        (λ q : a = x, ap t q) u).
    apply (ap (λ U, (transport (λ w : T f, Cover w → t a = w) (tp x y U) 
                               (λ q : a = x, ap t q) u))).
    symmetry; apply eisretr.
    generalize (i' p). intro q.
    destruct q; cbn.
    exact (ap10 (transport2 (λ w : T f, Cover w → t a = w) (tp_1 x) (λ q : a = x, ap t q)) u).
    intro x; cbn.
    match goal with
    |[|- _ @ path_forall ?ff = _] =>
     (* pose proof ff *)
     assert (r: ((ap10 (transport2 (λ w : T f, Cover w → t a = w) (tp_1 x) (λ q : a = x, ap t q)))) = ff)
    end.
    2:destruct r.
    2:unfold path_forall, ap10; rewrite eissect.
    2:apply concat_Vp.
    apply path_forall; intro u. cbn in *.
    rewrite ap_V.
    apply moveL_Vp.
    match goal with
    |[|- _ = match ?foo as _ in (_ = y) return _ with |_ => _ end 1 u ] =>
     transparent assert (r: (foo = 1))
    end.
    exact (eissect (ap f) (IsEquiv := Mono_f x x) 1).

    unfold equiv_inv.
    pose (apD (λ U, match
     U as p
     in (_ = y)
     return
       (f x = f y
        → ∀ u0 : a = y,
          transport (λ w : T f, Cover w → t a = w) 
            (tp x y (ap f p)) (λ q : a = x, ap t q) u0 = 
          ap t u0)
   with
   | 1 =>
       λ (_ : f x = f x) (u0 : a = x),
       ap10
         (transport2 (λ w : T f, Cover w → t a = w) 
            (tp_1 x) (λ q : a = x, ap t q)) u0
               end 1 u) r^).
    cbn in p.
    rewrite <- p; clear p.
    rewrite transport_paths_FlFr.
    cbn.
    rewrite ap_const. rewrite concat_p1.
    apply whiskerR.
    rewrite ap_V. rewrite inv_V.
    match goal with
    |[|- ap _ ?ff = _] => assert (X: ff = ap (ap f) r)
    end.
    unfold r.
    exact (eisadj (ap f) (IsEquiv := Mono_f x x) 1).
    rewrite X; clear X.
    match goal with
    |[|- ap ?gg (ap ?ff ?rr) = _] =>
     rewrite <- (ap_compose ff gg rr)
    end.
    reflexivity. }
    
  transparent assert (X: (forall e, IsEquiv (encode e))).
  { 
    (* refine (T_ind _ _ _ _); try (intros; apply path_ishprop). *)
    intro e.
    refine (isequiv_adjointify _ _ _).
    exact (decode e).
    revert e.
    refine (T_ind _ _ _ _).
    intros e x; destruct x; reflexivity.

    intros x y p; cbn.
    pose (i := ap (x:=x) (y:=y) f).
    pose (i' := equiv_inv (ap (x:=x) (y:=y) f) (IsEquiv := Mono_f x y)).
    match goal with
    |[|- transport ?PP (?ff p) ?gg = _] =>
     path_via (transport PP (ff (i (i' p))) gg);
       [ apply (ap (λ U:t x = t y, transport PP U gg)); apply ap; symmetry; apply eisretr | ]
    end.

    generalize (i' p). intro q.
    destruct q. cbn.
    match goal with
    |[|- transport ?PP _ ?gg = _] =>
     exact (transport2 PP (tp_1 x) gg)
    end.

    intro e; cbn.
    apply moveR_Vp.
    rewrite ap_V. rewrite ap_V. apply moveR_Vp.

    pose (r:= (eissect _ (IsEquiv := Mono_f e e) 1)).

    pose (p := apD (λ U, match
     U as p in (_ = y)
     return
       (f e = f y
        → transport (λ w : T f, Sect (decode w) (encode w)) 
            (tp e y (ap f p))
            (λ x : a = e,
             match
               x as p1 in (_ = y0) return (encode (t y0) (ap t p1) = p1)
             with
             | 1 => 1
             end) =
          (λ x : a = y,
           match
             x as p1 in (_ = y0) return (encode (t y0) (ap t p1) = p1)
           with
           | 1 => 1
           end))
   with
   | 1 =>
       λ _ : f e = f e,
       transport2 (λ w : T f, Sect (decode w) (encode w)) 
         (tp_1 e)
         (λ x : a = e,
          match x as p0 in (_ = y) return (encode (t y) (ap t p0) = p0) with
          | 1 => 1
          end)
   end 1) r^).
    rewrite <- p; clear p.
    cbn.
    rewrite transport_paths_FlFr.
    rewrite ap_const. rewrite concat_p1. rewrite concat_p1.
    apply whiskerR.
    rewrite ap_V. rewrite inv_V.
    match goal with
    |[|- _ = ap _ (ap _ ?ff)] =>
     assert (X: ff = ap (ap f) r)
    end.
    unfold r.
    exact (eisadj (ap f) (IsEquiv := Mono_f e e) 1).
    rewrite X; clear X.
    match goal with
    |[|- _ = ap ?gg (ap ?ff ?rr)] =>
     rewrite <- (ap_compose ff gg rr)
    end.
    match goal with
    |[|- _ = ap ?gg (ap ?ff ?rr)] =>
     rewrite <- (ap_compose ff gg rr)
    end. reflexivity. 
    intro x. destruct x. cbn. reflexivity. }

  unfold encode in X. cbn in X.
  pose (I := X (t b)).
  

  
  refine (isequiv_adjointify _ _ _).
  exact (λ q : t a = t b, transport Cover q 1).
  intro x.
  exact (eissect _ (IsEquiv := I) x).
  intro x.
  exact (eisretr _ (IsEquiv := I) x).
Defined.


    
    

Definition tp_id (A:Type)
  : T (idmap : A -> A) <~> A.
Proof.
  refine (equiv_adjointify _ _ _ _).
  - refine (T_rec _ _ _ _).
    exact idmap.
    intros a b. exact idmap.
    intro a; cbn. reflexivity.
  - exact t.
  - intro a. reflexivity.
  - refine (T_ind _ _ _ _).
    intro a. cbn. reflexivity.
    intros a b p. cbn.
    destruct p.
    exact (transport2 (λ w : T idmap,
                            t (T_rec A idmap (λ (a0 b : A) (x : a0 = b), x) (λ a0 : A, 1) w) = w)
                      (tp_1 a) 1).
    intro a.
    cbn.
    rewrite concat_Vp. reflexivity.
Defined.

    