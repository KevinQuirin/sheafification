(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import Forall_ Equivalences_ epi_mono reflective_subuniverse modalities OPaths.
Require Import nat_lemmas.
Require Import sheaf_base_case.
Require Import sheaf_def_and_thm.
Require Import Limit.
Require Import sheaf_induction.

Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
(* Local Open Scope equiv_scope. *)
Local Open Scope type_scope.

(* Readability *)
Arguments trunc_arrow {H} {A} {B} {n} {H0}: simpl never.
Arguments trunc_sigma {A} {P} {n} {H H0}: simpl never.
Arguments trunc_forall {H} {A} {P} {n} {H0}: simpl never. 
Arguments istrunc_paths {A} {n} {H} x y: simpl never.
Arguments isequiv_functor_sigma {A P B Q} f {H} g {H0}: simpl never.

Module Export T.

  Private Inductive T {A B:Type} (f: A -> B) : Type :=
  | t : A -> (T f).

  Arguments t {A B f} a.

  Axiom tp : forall {A B f} (a b:A), f a = f b -> @t A B f a = @t A B f b.

  Axiom tp_1 : forall {A B f} (a:A), @tp A B f a a 1 = 1.

  Definition T_ind {A B:Type} {f:A -> B} (P : T f -> Type)
             (t' : forall a, P (t a))
             (tp' : forall a b p, transport P (tp a b p) (t' a) = t' b)
             (tp_1' : forall a, (transport2 P (tp_1 a) (t' a))^ @ tp' a a 1 = 1)
    : forall w, P w
    := fun w => match w with
                |t a => fun _ => t' a
                end tp_1'.

  Axiom T_ind_beta_tp : forall {A B:Type} {f:A -> B} (P : T f -> Type)
                               (t' : forall a, P (t a))
                               (tp' : forall a b p, transport P (tp a b p) (t' a) = t' b)
                               (tp_1' : forall a, (transport2 P (tp_1 a) (t' a))^ @ tp' a a 1 = 1)
                               a b p,
      apD (T_ind P t' tp' tp_1') (tp a b p) = tp' a b p.
  
End T.

Definition T_rec {A B:Type} {f:A -> B} (P:Type)
           (t': A -> P)
           (tp' : forall (a b:A) (p:f a = f b), t' a = t' b)
           (tp_1' : forall a, tp' a a 1 = 1)
  : T f -> P.
Proof.
  refine (T_ind _ t' (fun a b p => transport_const _ _ @ tp' a b p)  _).
  intro a.
  exact ((concat_p_pp (p:= (transport2 (λ _ : T f, P) (tp_1 a) (t' a))^)  (q:= transport_const (tp a a 1) (t' a)) (r:= tp' a a 1))
           @ whiskerR (moveR_Vp _ _ _ (transport2_const (A:=T f) (B:= P) (tp_1 a) (t' a))) (tp' a a 1)
           @ concat_1p _
           @ (tp_1' a)).
Defined.

Definition T_rec_beta_tp {A B:Type} {f:A -> B} (P:Type)
           (t': A -> P)
           (tp' : forall (a b:A) (p:f a = f b), t' a = t' b)
           (tp_1' : forall a, tp' a a 1 = 1)
           a b p
  : ap (T_rec P t' tp' tp_1') (tp a b p) = tp' a b p.
Proof.
Admitted.






Section Foo.

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

  Local Open Scope Opath_scope.

  (* Definition BTT (T:Type) `{Tr: IsTrunc n T} := @BuildTruncType n T Tr. *)

  Definition mu_modal_paths_func_univ_func
             (T : TruncType (trunc_S n))
             (a : T)
             (b : T)
             (p : ((clδ T) (a, b)))
             (t : T)
    : O nj (BTT (t = a)) -> O nj (BTT (t = b))
    := λ q, q °@ p.

  Definition mu_modal_paths_func_univ_inv
             (T : TruncType (trunc_S n))
             (a : T)
             (b : T)
             (p : ((clδ T) (a, b)))
             (t : T)
    : O nj (BTT (t = b)) -> O nj (BTT (t = a))
    := λ q, q °@ p°^.
  
  Lemma mu_modal_paths_func_univ_eq
        (T : TruncType (trunc_S n))
        (a : T)
        (b : T)
        (p : (clδ T (a, b)))
        (t : T)
    : (Sect (mu_modal_paths_func_univ_inv T a b p t) (mu_modal_paths_func_univ_func T a b p t))
      /\ (Sect (mu_modal_paths_func_univ_func T a b p t) (mu_modal_paths_func_univ_inv T a b p t)).
           split.
           - intro x.
             unfold mu_modal_paths_func_univ_inv, mu_modal_paths_func_univ_func, δ; simpl.
             rewrite Oconcat_pp_p.
             rewrite Oconcat_Vp.
             apply Oconcat_p1.
           - intro x. unfold mu_modal_paths_func_univ_inv, mu_modal_paths_func_univ_func, δ.
             rewrite Oconcat_pp_p.
             rewrite Oconcat_pV.
             apply Oconcat_p1.
  Qed.

  Definition Omono_sep (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B)
    : Type.
  Proof.
    pose (separated_nj_paths B sepB).
    exact (forall x y:A, IsEquiv (O_rec n nj (BTT (x=y)) (Build_subuniverse_Type n nj (BTT (f x = f y)) (i (f x) (f y))) (ap f))).
  Defined.

  Lemma fooo_Cover (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B) (Omono_f : Omono_sep A B sepB f) (a:A)
    : Trunc (n.+1) (T f) -> subuniverse_Type nj.
  Proof.
    refine (Trunc_rec _).
    apply subuniverse_Type_is_TruncTypeSn. exact ua. 
    refine (T_rec _ _ _ _).
    intro e; exact (O nj (BTT (a=e))).
    intros x y p. cbn.
    generalize (equiv_inv _ (IsEquiv := Omono_f x y) p).
    
    intro q.
    apply unique_subuniverse.
    apply path_trunctype.
    refine (equiv_adjointify (λ r, r °@ q) (λ r, r °@ q°^) _ _).
    abstract (intro u; rewrite Oconcat_pp_p; rewrite Oconcat_Vp; apply Oconcat_p1).
    abstract (intro u; rewrite Oconcat_pp_p; rewrite Oconcat_pV; apply Oconcat_p1).

    

    intros x. cbn.
    pose (hh := isequiv_unique_subuniverse).
    apply moveR_equiv_M. cbn.
    rewrite concat_1p, concat_p1. cbn.
    match goal with
    |[|- ap _ ?pp = _] => assert (r: 1 = pp)
    end.
    2: destruct r; reflexivity.

    apply moveL_equiv_M; cbn.
    apply moveL_equiv_M; cbn.
    apply path_equiv; cbn.
    apply path_forall; intro r.
    match goal with
    |[|- ?ff r = r °@ ?gg] =>
     revert r;
       refine (O_rec_dep _ (λ r, Build_subuniverse_Type n nj
                                                        (BuildTruncType _ (ff r = r °@ gg))
                                                        _) _).1
    end.
    intro r; cbn.
    destruct r.
    pose (rr := @Oconcat_1p); unfold Oidpath in rr; rewrite rr; clear rr.
    apply moveL_equiv_V.
    unfold function_lift.
    pose (rr :=λ P Q f, ap10 (O_rec_retr n nj P Q f)). rewrite rr; clear rr.
    reflexivity. exact ua. exact fs.
  Defined.

  Lemma fooo_encode (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B) (Omono_f : Omono_sep A B sepB f) (a:A)
    : forall e:Trunc (n.+1) (T f), O nj (BTT ((tr o t) a = e)) -> fooo_Cover A B sepB f Omono_f a e.
  Proof.
    intros e q. exact (Otransport (fooo_Cover A B sepB f Omono_f a) q °1).
  Defined.

  Axiom admitt : forall X, X.

  Opaque O_rec_dep.

  Lemma fooo_decode (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B) (Omono_f : Omono_sep A B sepB f) (a:A)
    : forall e:Trunc (n.+1) (T f), (fooo_Cover A B sepB f Omono_f a) e -> O nj (BTT ((tr o t) a = e)).
  Proof.
    refine (Trunc_ind _ _).
    refine (T_ind _ _ _ _).
    - intros e q. cbn in q.
      apply (Oap (mod:=mod_nj) (x:=a) (y:=e) (tr o (t:A -> T f)) q).
    - intros x y p.
      pose (i := (O_rec n nj (BTT (x=y)) (Build_subuniverse_Type n nj (BTT (f x = f y)) (separated_nj_paths B sepB (f x) (f y))) (ap f))).
      pose (i' := equiv_inv _ (IsEquiv := Omono_f x y)).
      path_via (transport
                  (λ w : T f,
                         fooo_Cover A B sepB f Omono_f a (tr w) → O nj (BTT (tr (t a) = tr w)))
                  (tp x y (i (i' p)))
                  ((λ (e : A) (q : fooo_Cover A B sepB f Omono_f a (tr (t e))),
                    Oap (tr o (t:A → T f)) q) x)).
      match goal with
      |[|- transport ?PP _ ?xx = _] =>
       apply (ap (λ U, transport PP (tp x y U) xx))
      end.
      symmetry; apply eisretr.
      apply path_forall; intro u; cbn in u.
      generalize (i' p).
      match goal with
      |[|- forall _, transport ?PP _ ?xx ?uu = ?yy] =>
       refine (O_rec_dep _ (λ q, Build_subuniverse_Type n nj (BTT (transport PP (tp x y (i q)) xx uu = yy)) _) _).1
      end.
      intro q; destruct q.
      Opaque fooo_Cover.
      cbn.
      unfold i.
      exact ((ap (λ U, transport (λ w : T f,
                                        fooo_Cover A B sepB f Omono_f a (tr w) → O nj (BTT (tr (t a) = tr w)))
                                 (tp x x U) (λ q : fooo_Cover A B sepB f Omono_f a (tr (t x)),
                                                   Oap (λ x0 : A, tr (t x0)) q) u)
                 (ap10 (O_rec_retr n nj (BTT (x=x))
                                   {| st := BTT (f x = f x);
                                      subu_struct := separated_nj_paths B sepB (f x) (f x) |}
                                   (ap f)) 1))
               @
               (ap10 (transport2 (λ w : T f,
                                        fooo_Cover A B sepB f Omono_f a (tr w) → O nj (BTT (tr (t a) = tr w)))
                                 (tp_1 x) (λ q : fooo_Cover A B sepB f Omono_f a (tr (t x)), Oap (λ x0 : A, tr (t x0)) q)) u)).
    -
      apply admitt.
      
      (* intro x; cbn. *)
      (* rewrite concat_p_pp. *)

      (* match goal with *)
      (* |[|- _ @ path_forall ?ff = _] => *)
      (*  assert (bar := ff) *)
      (* end. cbn in bar. *)

      (* match goal with *)
      (* |[ bar : ?XX |- _] => clear bar; transparent assert (bar : XX) *)
      (* end. *)
      (* { apply apD10. *)
      (*   etransitivity; [| exact (((transport2 (λ w : T f, *)
      (*                                                fooo_Cover A B sepB f Omono_f a (tr w) → O nj (BTT (tr (t a) = tr w))) *)
      (*                                         (tp_1 x) (λ q : fooo_Cover A B sepB f Omono_f a (tr (t x)), Oap (λ x0 : A, tr (t x0)) q))))]. *)
      (*   match goal with *)
      (*   |[|- transport ?PP (tp x x _) ?xx = _] => *)
      (*    apply (ap (λ U, transport PP (tp x x U) xx)) *)
      (*   end. *)
      (*   apply eisretr. } *)
      
      (* match goal with *)
      (* |[|- _ @ path_forall ?ff = _] => *)
      (*  (* pose proof ff *) *)
      (*  assert (r: bar = ff) *)
      (* end. *)
      (* {  *)
      (*   unfold bar; clear bar. *)
      (* match goal with *)
      (* |[|- ?ff = ?gg] => *)
      (*  apply path_forall; *)
      (*    refine (O_rec_dep _ (λ u, Build_subuniverse_Type n nj (BTT (ff u = gg u)) _) _).1 *)
      (* end. *)
      (* refine (subuniverse_paths _ _ (Build_subuniverse_Type n nj _ _) _ _). *)
      (* intro u; cbn. *)
      (* match goal with *)
      (* |[|- _ = pr1 _ ?xx] => transparent assert (r: (xx = °1)) *)
      (* end. *)
      (* {  *)
      (*   pose (s:=eissect _ (IsEquiv := Omono_f x x) °1). *)
      (*   pose (r:= ap (equiv_inv _ (IsEquiv := Omono_f x x)) (ap10 (O_rec_retr n nj (BTT (x = x)) *)
      (*                              {| st := BTT (f x = f x); *)
      (*                                 subu_struct := separated_nj_paths B sepB (f x) (f x) |} *)
      (*                              (ap f)) 1)). cbn in r. *)
      (*   exact (r^ @ s). *)
      (* } *)
      (* match goal with *)
      (* |[|- ?XX = pr1 ?YY ?xx] => *)
      (*  pose (p:= apD (λ U, pr1 YY U) r^) *)
      (* end. *)
      (* rewrite <- p; clear p. *)
      (* match goal with *)
      (* |[|- ?XX = transport _ _ (pr1 (O_rec_dep ?AA ?BB ?gg) ?xx)] => *)
      (*  pose ((O_rec_dep AA BB gg).2 1) *)
      (*  (* assert (p: (pr1 (O_rec_dep AA BB gg) xx) = gg 1) by apply *) *)
      (* end. *)
      (* rewrite p; clear p. *)
      (* cbn. rewrite transport_paths_Fl. *)
      (* rewrite apD10_pp. repeat rewrite concat_p_pp. *)
      (* apply whiskerR. *)
      (* match goal with |[|- _ = (ap ?ff ?rr)^ @ _] => rewrite <- (ap_V ff rr) end. *)
      (* match goal with *)
      (* |[|- _ = ap (λ x0:_, transport ?PP (tp x x (?gg x0)) ?ff ?oo) r^^ @ _] *)
      (*  => rewrite (ap_compose gg (λ U, transport PP (tp x x U) ff oo)); cbn *)
      (* end. *)
      (* match goal with *)
      (* |[|- _ = ap ?f1 ?r1 @ ap ?f2 ?r2 ] *)
      (*  => rewrite <- (ap_pp f1 r1 r2) *)
      (* end. *)
      (* match goal with *)
      (* |[|- apD10 (ap ?ff ?pp) _ = _] *)
      (*  => pose (p := ap_apply_Fl pp ff (O_unit _ (BTT (a = x)) u)); unfold ap10 in p; rewrite <- p; clear p *)
      (* end. *)
      (* apply ap. *)
      (* rewrite inv_V. *)
      (* unfold r; clear r. rewrite ap_pp. rewrite ap_V. *)
      (* rewrite <- ap_compose. *)
      (* rewrite <- eisadj. *)
      (* rewrite_moveL_Vp_p. *)

      (* pose (p := apD (λ U:f x = f x -> f x = f x, ap U (ap10 *)
      (*   (O_rec_retr n nj (BTT (x = x)) *)
      (*      {| *)
      (*      st := BTT (f x = f x); *)
      (*      subu_struct := separated_nj_paths B sepB (f x) (f x) |}  *)
      (*      (ap f)) 1)) (path_forall (λ u, (eisretr _ (IsEquiv := Omono_f x x) u)^))). *)
      (* cbn in p. *)
      (* rewrite <- p; clear p. *)
      (* rewrite ap_idmap. *)
      (* rewrite transport_paths_FlFr. cbn in *. *)
      (* pose (p := ap_ap_path_forall (λ u0 : f x = f x, *)
      (*       (eisretr (IsEquiv := Omono_f x x) *)
      (*         (O_rec n nj (BTT (x = x)) *)
      (*            {| *)
      (*            st := BTT (f x = f x); *)
      (*            subu_struct := separated_nj_paths B sepB (f x) (f x) |} *)
      (*            (ap f)) u0)^) (O_rec n nj (BTT (x = x)) *)
      (*         {| *)
      (*         st := BTT (f x = f x); *)
      (*         subu_struct := separated_nj_paths B sepB (f x) (f x) |}  *)
      (*         (ap f) (O_unit nj (BTT (x = x)) 1))). *)
      (* cbn in p. rewrite p; clear p. *)
      (* rewrite inv_V. *)
      (* repeat rewrite concat_pp_p. apply whiskerL. *)

      (* pose (p := ap_ap_path_forall (λ u0 : f x = f x, *)
      (*     (eisretr (IsEquiv := Omono_f x x) *)
      (*        (O_rec n nj (BTT (x = x)) *)
      (*           {| *)
      (*           st := BTT (f x = f x); *)
      (*           subu_struct := separated_nj_paths B sepB (f x) (f x) |} *)
      (*           (ap f)) u0)^) 1). *)
      (* cbn in p. rewrite p; clear p. *)
      (* rewrite concat_Vp. rewrite concat_p1. reflexivity. } *)
      (* destruct r. *)
      (* unfold bar. unfold path_forall; rewrite eissect. *)
      (* rewrite_moveR_Vp_p. rewrite concat_p1. *)
      (* rewrite ap_V. rewrite concat_Vp. rewrite concat_1p. *)
      (* reflexivity.       *)
  Defined.

  Lemma fooo_equiv (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B) (Omono_f : Omono_sep A B sepB f) (a:A)
    : (forall e, IsEquiv (fooo_encode A B sepB f Omono_f a e)).
  Proof.
    intro e.
    refine (isequiv_adjointify _ _ _).
    - exact (fooo_decode A B sepB f Omono_f a e).
    - revert e.
      refine (Trunc_ind _ _).
      refine (T_ind _ _ _ _).
      + intros e.
        unfold Sect.
        refine (O_rec_dep _ (λ x, Build_subuniverse_Type n nj (BTT (fooo_encode A B sepB f Omono_f a (tr (t e))
                                                                                (fooo_decode A B sepB f Omono_f a (tr (t e)) x) = x)) _) _).1.
        intro x; destruct x; cbn.
        match goal with
        |[|- fooo_encode _ _ _ _ _ _ _
                         (Oap ?ff _) =_] =>
         etransitivity; [exact (ap (fooo_encode A B sepB f Omono_f a (tr (t a))) (Oap_1 (mod := mod_nj) ff (x:=a))) |]
        end.
        apply Otransport_1.
      + intros x y p; cbn.
        pose (i := (O_rec n nj (BTT (x=y)) (Build_subuniverse_Type n nj (BTT (f x = f y)) (separated_nj_paths B sepB (f x) (f y))) (ap f))).
        pose (i' := equiv_inv _ (IsEquiv := Omono_f x y)).
        match goal with
        |[|- transport ?PP (?ff p) ?gg = _] =>
         path_via (transport PP (ff (i (i' p))) gg);
           [ refine (transport2 PP _ _); apply ap; symmetry; apply eisretr |]
        end.
        generalize (i' p).
        intro q.
        (* apply path_forall. intro u. *)
        match goal with
        |[|- transport ?PP (?ff (i q)) ?gg = ?hh] =>
         refine ((O_rec_dep _ (λ q, Build_subuniverse_Type n nj (BTT (transport PP (ff (i q)) gg = hh)) _) _).1 q)
        end.
        { abstract (refine istrunc_paths). }
        { abstract (
              match goal with
              |[|- IsSubu _ _ (BTT (?fooo = ?baar)) ] =>
               set (foo := fooo); set (bar := baar)
              end;
              match goal with
              |[ bar : ?XX |- _] =>
               assert (X: IsSubu n nj (BTT XX))
              end;
              [refine (subuniverse_forall n nj _ _ _) |
               pose (i0:= subuniverse_paths n nj (Build_subuniverse_Type n nj _ X) foo bar);
                 match goal with
                 |[i0 : IsSubu n nj ?XX |- IsSubu n nj ?YY]
                  => assert (r: XX = YY)
                 end;
                 [apply path_trunctype; apply equiv_idmap | ]; destruct r; exact i0] ).
        }

        rename q into old_q; intro q; cbn.
        destruct q. unfold i; cbn.

        assert (r: (tp x x
                       (O_rec n nj (BTT (x = x))
                              {|
                                st := BTT (f x = f x);
                                subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                              (ap f)
                              (O_unit
                                 (underlying_subu sheaf_def_and_thm.n sheaf_def_and_thm.mod_nj)
                                 (BTT (x = x)) 1))) = 1).
        { match goal with |[|- ?xx _ = 1] => path_via (xx 1) end.
          apply ap.
          refine (ap10 (O_rec_retr n nj (BTT (x=x)) {|st := BTT (f x = f x); subu_struct := separated_nj_paths B sepB (f x) (f x) |} (ap f)) 1).
          apply tp_1.
        }

        match goal with
        |[|- transport ?PP _ ?ff = _]
         => exact (transport2 PP r ff)
        end.
        
      + intro x.
        cbn.
        match goal with
        |[|- (transport2 ?PP _ ?xx)^ @ _ = _ ] =>
         set (P := PP) in *; set (foo := xx) in *
        end.
        rewrite <- (transport2_V P (tp_1 x) foo).
        rewrite concat_p_pp.
        rewrite <- (transport2_p2p P (tp_1 x)^
                    (ap (tp x x)
                        (eisretr (IsEquiv := Omono_f x x)
                                 (O_rec n nj (BTT (x = x))
                                        {|
                                          st := BTT (f x = f x);
                                          subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                        (ap f)) 1)^)
                      foo).

        apply moveR_Mp. rewrite concat_p1.
        rewrite <- (transport2_V P ((tp_1 x)^ @
                                                ap (tp x x)
                                                (eisretr (IsEquiv := Omono_f x x)
                                                         (O_rec n nj (BTT (x = x))
                                                                {|
                                                                  st := BTT (f x = f x);
                                                                  subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                                                (ap f)) 1)^)
                                 foo).
        rewrite ap_V.
        rewrite inv_VV.

        pose (r := (eissect _ (IsEquiv := Omono_f x x) °1)^
                   @(ap (equiv_inv _ (IsEquiv := Omono_f x x)) (ap10 (O_rec_retr n nj (BTT (x = x))
                                                                                 {| st := BTT (f x = f x);
                                                                                    subu_struct := separated_nj_paths B sepB (f x) (f x) |}
                                                                                 (ap f)) 1))).
        
        match goal with
        |[|- ?XX _ = _] =>
         pose (rr := apD XX r)
        end.
        rewrite <- rr. clear rr. cbn.
        match goal with
        |[|- transport ?PP r (pr1 ?XX °1) = _]
         => pose (ap (transport PP r) (pr2 XX 1))
        end.
        etransitivity; [exact p | clear p ]. 
        rewrite transport_paths_Fl.
        apply moveR_pM.
        pose (p:= transport2_V P (ap (tp x x)
                                     (ap10
                                        (O_rec_retr n nj (BTT (x = x))
                                                    {|
                                                      st := BTT (f x = f x);
                                                      subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                                    (ap f)) 1) @ tp_1 x) foo).
        rewrite <- p; clear p.

        pose (p:= transport2_p2p P (ap (tp x x)
                                       (eisretr (IsEquiv := Omono_f x x)
                                                (O_rec n nj (BTT (x = x))
                                                       {|
                                                         st := BTT (f x = f x);
                                                         subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                                       (ap f)) 1) @ tp_1 x)
                                 (ap (tp x x)
                                     (ap10
                                        (O_rec_retr n nj (BTT (x = x))
                                                    {|
                                                      st := BTT (f x = f x);
                                                      subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                                    (ap f)) 1) @ tp_1 x)^
                  foo).
        rewrite <- p; clear p.
        rewrite inv_pp.
        match goal with
        |[|- _ = transport2 _ ((ap ?ff ?X1 @ _) @ (_ @ (ap _ ?X2)^)) _]
         => path_via (transport2 P (ap ff (X1 @ X2^)) foo)
        end.
        Focus 2.
        refine (apD10 _ foo).
        apply (ap (x:= (ap (tp x x)
                           (eisretr (IsEquiv := Omono_f x x)
                                    (O_rec n nj (BTT (x = x))
                                           {|
                                             st := BTT (f x = f x);
                                             subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                           (ap f)) 1 @
                                    (ap10
                                       (O_rec_retr n nj (BTT (x = x))
                                                   {|
                                                     st := BTT (f x = f x);
                                                     subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                                   (ap f)) 1)^)))
                  (y:= ((ap (tp x x)
                            (eisretr (IsEquiv := Omono_f x x)
                                     (O_rec n nj (BTT (x = x))
                                            {|
                                              st := BTT (f x = f x);
                                              subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                            (ap f)) 1) @ tp_1 x) @
                                                                 ((tp_1 x)^ @
                                                                              (ap (tp x x)
                                                                                  (ap10
                                                                                     (O_rec_retr n nj (BTT (x = x))
                                                                                                 {|
                                                                                                   st := BTT (f x = f x);
                                                                                                   subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                                                                                 (ap f)) 1))^)))
                  
                  (λ U, transport2 P U)).

        rewrite ap_pp.
        repeat rewrite concat_pp_p.
        apply whiskerL.
        repeat rewrite concat_p_pp. rewrite ap_V.
        rewrite concat_pV. rewrite concat_1p. reflexivity.
        rewrite <- (ap_V (λ
                            x0 : O (underlying_subu sheaf_def_and_thm.n sheaf_def_and_thm.mod_nj)
                                   (BTT (x = x)),
                                 transport P
                                           (tp x x
                                               (O_rec n nj (BTT (x = x))
                                                      {|
                                                        st := BTT (f x = f x);
                                                        subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                                      (ap f) x0)) foo) r).
        rewrite (ap_compose (λ x0, (tp x x
                                       (O_rec n nj (BTT (x = x))
                                              {|
                                                st := BTT (f x = f x);
                                                subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                              (ap f) x0))) (λ U, transport P U foo)).
        match goal with
        |[|- ap (λ U:t x = t x, ?TT U ?fooo) ?rr = _]
         => rewrite (ap_compose TT (λ U, U fooo) rr)
        end.
        rewrite ap_apply_l.

        rewrite <- (@transport2_is_ap10 _ P).
        refine (apD10 _ foo).
        apply ap.
        unfold r; clear r.
        rewrite (ap_compose (O_rec n nj (BTT (x = x))
                                   {|
                                     st := BTT (f x = f x);
                                     subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                   (ap f)) (tp x x)).
        apply ap.
        rewrite inv_Vp.
        rewrite ap_pp.
        rewrite <- (eisadj _ (IsEquiv := Omono_f x x) °1).
        rewrite <- ap_V.
        rewrite <- ap_compose.
        match goal with
        |[|- ap ?ff _ @ _ = _] => transparent assert (r: (idmap = ff))
        end.
        { apply path_forall; intro y.
          symmetry.
          apply eisretr. }

        pose (p:= apD (λ U, ap U (ap10
                                    (O_rec_retr n nj (BTT (x = x))
                                                {|
                                                  st := BTT (f x = f x);
                                                  subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                                (ap f)) 1)^) r).
        rewrite <- p; clear p.
        rewrite ap_idmap. cbn.
        rewrite transport_paths_FlFr.
        unfold r; clear r.
        rewrite_moveR_Vp_p.
        rewrite (ap_ap_path_forall (λ
                                      y : {|
                                            st := BTT (f x = f x);
                                            subu_struct := separated_nj_paths B sepB (f x) (f x) |},
                                          (eisretr (IsEquiv := Omono_f x x)
                                                   (O_rec n nj (BTT (x = x))
                                                          {|
                                                            st := BTT (f x = f x);
                                                            subu_struct := separated_nj_paths B sepB (f x) (f x) |}
                                                          (ap f)) y)^) 1).
        rewrite concat_Vp. rewrite concat_1p.
        rewrite_moveR_Vp_p.
        rewrite concat_pV.
        rewrite (ap_ap_path_forall (λ
                                      y : {|
                                            st := BTT (f x = f x);
                                            subu_struct := separated_nj_paths B sepB (f x) (f x) |},
                                          (eisretr (IsEquiv := Omono_f x x)
                                                   (O_rec n nj (BTT (x = x))
                                                          {|
                                                            st := BTT (f x = f x);
                                                            subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                                          (ap f)) y)^)
                                   (O_rec n nj (BTT (x = x))
                                          {|
                                            st := BTT (f x = f x);
                                            subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                          (ap f) (O_unit nj (BTT (x = x)) 1))).
        rewrite concat_Vp. reflexivity.
    - unfold Sect.
      refine (O_rec_dep _ (λ x, Build_subuniverse_Type n nj (BTT (fooo_decode A B sepB f Omono_f a e (fooo_encode A B sepB f Omono_f a e x) =
                                                                  x
                                                            )) _) _).1.
      intro x; destruct x; cbn.
      unfold fooo_encode.
      pose (r:= @Otransport_1); unfold Oidpath in r; rewrite r; clear r.
      rewrite Oap_1.
      reflexivity.
  Defined.
  
  Lemma fooo (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B) (Omono_f : Omono_sep A B sepB f)
    : Omono _ _ (tr o t : A -> Trunc (n.+1) (T f)).
  Proof.
    intros a b.
    pose (e := fooo_encode A B sepB f Omono_f a (tr (t b))).
    pose (d := fooo_decode A B sepB f Omono_f a (tr (t b))).
    pose (eq := isequiv_inverse _ (feq := fooo_equiv A B sepB f Omono_f a (tr (t b)))).
    exact eq.
  Defined.
  
  


  
  Definition cT1 (E:TruncType (n.+1)) : TruncType (n.+1)
    := BuildTruncType _
                      (Trunc (n.+1)
                             (Coeq (λ x:{x:E/\E & O nj (BTT (fst x=snd x))}, fst x.1)
                                   (λ x:{x:E/\E & O nj (BTT (fst x=snd x))}, snd x.1))).

  Definition cT1f (E:TruncType (n.+1)) : E -> (cT1 E).
  Proof.
    intro e.
    apply tr. apply coeq. exact e.
  Defined.

  Definition cT2 (E:TruncType (n.+1)) : TruncType (n.+1)
    := BuildTruncType _
                      (Trunc (n.+1)
                             (Coeq (λ x:{x:E/\E & O nj (BTT (cT1f E (fst x) = cT1f E (snd x)))}, fst x.1)
                                   (λ x:{x:E/\E & O nj (BTT (cT1f E (fst x) = cT1f E (snd x)))}, snd x.1))).

  Definition cT2f (E:TruncType (n.+1)) : (cT1 E) -> (cT2 E).
  Proof.
    transparent assert (hh: ({x:E/\E & O nj (BTT (fst x=snd x))} -> {x:E/\E & O nj (BTT (cT1f E (fst x) = cT1f E (snd x)))})).
    { refine (functor_sigma idmap _).
      intros [a b]; cbn.
      apply O_rec. intro p. apply O_unit. apply ap. exact p. }
    
    refine (Trunc_rec _). refine (Coeq_rec _ _ _).
    intro e. apply tr. apply coeq. exact e.
    intros [[a b] p]. cbn in *.
    apply ap.
    exact (cp (f:=(λ x:{x:E/\E & O nj (BTT (cT1f E (fst x) = cT1f E (snd x)))}, fst x.1))
              (g:=(λ x:{x:E/\E & O nj (BTT (cT1f E (fst x) = cT1f E (snd x)))}, snd x.1))
              (hh ((a,b);p))
          ).
  Defined.

  Definition cT3 (E:TruncType (n.+1)) : TruncType (n.+1)
    := BuildTruncType _
                      (Trunc (n.+1)
                             (Coeq (λ x:{x:(cT1 E)/\(cT1 E) & O nj (BTT (cT2f E (fst x) = cT2f E (snd x)))}, fst x.1)
                                   (λ x:{x:(cT1 E)/\(cT1 E) & O nj (BTT (cT2f E (fst x) = cT2f E (snd x)))}, snd x.1))).

  Definition cT3f (E:TruncType (n.+1)) : (cT2 E) -> (cT3 E).
  Proof.
    
    transparent assert (hh: ({x:E/\E & O nj (BTT (cT1f E (fst x) = cT1f E (snd x)))} -> {x:(cT1 E)/\(cT1 E) & O nj (BTT (cT2f E (fst x) = cT2f E (snd x)))})).
    { intros [[a b] p].
      refine (exist _ _ _).
      split. exact (cT1f E a). exact (cT1f E b).
      revert p; apply O_rec; intro p.
      apply O_unit.
      Opaque cT2f. cbn. apply ap. exact p. }
    
    refine (Trunc_rec _).
    refine (Coeq_rec _ _ _).
    intro e. apply tr. apply coeq. apply cT1f. exact e.
    
    intros [[a b] p]. cbn.
    pose (cp (f := (λ x:{x:(cT1 E)/\(cT1 E) & O nj (BTT (cT2f E (fst x) = cT2f E (snd x)))}, fst x.1))
             (g := (λ x:{x:(cT1 E)/\(cT1 E) & O nj (BTT (cT2f E (fst x) = cT2f E (snd x)))}, snd x.1))).
    specialize (p0 (hh ((a,b);p))).
    cbn in p0. apply ap. simpl in *. exact p0.
  Defined.  

  Variable (E:TruncType (n.+1)).

  Definition Tθ1 := T (separated_unit E).
  Definition θ1 : Tθ1 -> (separated_Type E).
  Proof.
    refine (T_rec _ _ _ _).
    exact (separated_unit E).
    intros a b p; exact p.
    intro a. reflexivity.
  Defined.

  Definition Tθ2 := T θ1.
  Definition θ2 : Tθ2 -> (separated_Type E).
  Proof.
    refine (T_rec _ _ _ _).
    exact θ1.
    intros a b p; exact p.
    intro a; reflexivity.
  Defined.

  Instance IsTrunc_separated_Type : IsTrunc (n.+1) (separated_Type E).
  Admitted.

  Instance IsSubu_separated_unit_paths (x y:E)
    : IsSubu n nj (BTT (separated_unit E x = separated_unit E y)).
  pose (separated_nj_paths (BuildTruncType _ (separated_Type E)) (separated_Type_is_separated E) (separated_unit E x) (separated_unit E y)).
  unfold BTT. 
  match goal with
  |[i: IsSubu _ _ {| trunctype_type := _; istrunc_trunctype_type := ?XX|} |- IsSubu _ _ {| trunctype_type := _; istrunc_trunctype_type := ?YY|}]
   => assert (r:XX=YY) by apply path_ishprop
  end.
  destruct r.
  exact i.
  Qed.

  Instance IsSubu_θ1_path (x y:Trunc (n.+1) Tθ1) (H:= separated_Type_is_TruncType_Sn E)
    : IsSubu n nj (@BuildTruncType n (Trunc_rec θ1 x = Trunc_rec θ1 y) (istrunc_paths (n:=n) (H:=H) _ _)).
  Proof.
  Admitted.


  Definition ab_cacb (a b:E) (c := tr o t : E -> Trunc (n.+1) Tθ1)
    : O nj (BTT (a=b)) -> O nj (BTT (c a = c b)).
  Proof.
    refine (function_lift _ _ _ _ _).
    exact (ap c).
  Defined.

  Definition ab_cacb' (a b:E) (c := tr o t : E -> Trunc (n.+1) Tθ1)
    : O nj (BTT (a=b)) -> O nj (BTT (c a = c b)).
  Proof.
    intro p. pose (function_lift_modal n nj _ (Build_subuniverse_Type n nj (BTT (separated_unit E a = separated_unit E b)) _) (ap (x:=a) (y:=b) ((separated_unit E))) p).
    apply O_unit. apply (ap tr).
    apply tp. exact t0.
  Defined.

  Definition ab_cacb_' (a b:E) (c := tr o t : E -> Trunc (n.+1) Tθ1)
    : ab_cacb a b == ab_cacb' a b.
  Proof.
    unfold pointwise_paths.
    pose (shf := λ x: O nj (BTT (a=b)), Build_subuniverse_Type n nj (BuildTruncType _ (ab_cacb a b x = ab_cacb' a b x)) _).
    refine (O_rec_dep _ shf _).1.
    unfold shf; clear shf; intro p; cbn in *.
    unfold ab_cacb, ab_cacb'.
    unfold function_lift, function_lift_modal.
    pose (r := λ P Q f, ap10 (O_rec_retr n nj P Q f)); rewrite r; rewrite r; clear r.
    apply ap.
    destruct p; cbn.
    rewrite tp_1. reflexivity.
  Defined.

  Definition cacb_cacb (a b:E) (c := tr o t : E -> Trunc (n.+1) Tθ1)
    : O nj (BTT (c a= c b)) -> O nj (BTT (c a = c b)).
  Proof.
    refine (function_lift _ _ _ _ _).
    exact idmap.
    (* exact (ap c). *)
  Defined.

  Definition cacb_cacb' (a b:E) (c := tr o t : E -> Trunc (n.+1) Tθ1)
    : O nj (BTT (c a=c b)) -> O nj (BTT (c a = c b)).
  Proof.
    intro p. pose (function_lift_modal n nj _ (Build_subuniverse_Type n nj (BTT (separated_unit E a = separated_unit E b)) _) (ap (x:=c a) (y:=c b) (Trunc_rec θ1)) p).
    apply O_unit. apply (ap tr).
    apply tp. exact t0.
  Defined.

  Definition cacb_cacb_' (a b:E) (c := tr o t : E -> Trunc (n.+1) Tθ1)
    : cacb_cacb a b == cacb_cacb' a b.
  Proof.
    unfold pointwise_paths.
    pose (shf := λ x: O nj (BTT (c a=c b)), Build_subuniverse_Type n nj (BuildTruncType _ (cacb_cacb a b x = cacb_cacb' a b x)) _).
    refine (O_rec_dep _ shf _).1.
    unfold shf; clear shf; intro p; cbn in *.
    unfold cacb_cacb, cacb_cacb'.
    unfold function_lift, function_lift_modal.
    pose (r := λ P Q f, ap10 (O_rec_retr n nj P Q f)); rewrite r; rewrite r; clear r.
    apply ap.
    destruct p; cbn.
    rewrite tp_1. reflexivity.
  Defined.

  

  Definition equiv_path_T (a b:E) (t := t : E -> Tθ1) (θ := separated_unit E)
    : t a = t b <~> θ a = θ b.
  Proof.
    symmetry.
    transparent assert (Cover : (Tθ1 -> Type)).
    { refine (T_rec _ _ _ _).
      intro z.
      exact (θ a = θ z).
      intros x y p. cbn.
      apply path_universe_uncurried.
      refine (equiv_adjointify _ _ _ _).
      intro q.
      exact (q @ p).
      intro q. exact (q @ p^).
      intro q. apply moveR_pM. reflexivity.
      intro q. apply moveR_pV. reflexivity.

      intro x. cbn.
      unfold equiv_adjointify.
      apply (@equiv_inj _ _ _ (isequiv_equiv_path _ _)).
      
      rewrite equiv_path_path_universe_uncurried.
      apply path_equiv. cbn.
      apply path_forall; intro q. apply concat_p1.
    }

    transparent assert (encode : (forall e:Tθ1, forall p : t a = e, Cover e)).
    { intros e p.
      apply (transport Cover p).
      reflexivity. }

    transparent assert (decode : (forall e:Tθ1, forall p : Cover e, t a= e)).
    { refine (T_ind _ _ _ _).
      intro e. apply tp.
      intros x y p. cbn.
      apply path_forall; intro q.
      rewrite (transport_arrow).
      rewrite transport_paths_r.
      cbn. fold θ in p.

      assert ((transport Cover (tp x y p)^ q) = (q @ p^)).
      { admit. }
      rewrite X.

  Abort.


  
  Definition ab_cacb_e (a b:E) (c := tr o t : E -> Trunc (n.+1) Tθ1)
    : (forall x y:E, IsEquiv (function_lift_modal n nj _ (Build_subuniverse_Type n nj (BTT (separated_unit E x = separated_unit E y)) _) (ap (x:=x) (y:=y) ((separated_unit E))))) -> IsEquiv (ab_cacb' a b).
  Proof.
    intro H.
    
    refine (isequiv_adjointify _ _ _).
    - intro p.
      apply (equiv_inv _ (IsEquiv := H a b)).
      apply (function_lift_modal n nj _ (Build_subuniverse_Type n nj (BTT (Trunc_rec θ1 (tr (t a)) = Trunc_rec θ1 (tr (t b)))) _) (ap (x:=tr (t a)) (y:=tr (t b)) (Trunc_rec θ1)) p).
    - intro p.
      unfold ab_cacb'. cbn.
      rewrite eisretr.
      unfold function_lift_modal.
      
      revert p.
      match goal with
      |[|- forall p:?XX, ?ff p] =>
       pose (shf := λ p:XX, Build_subuniverse_Type n nj
                                                   (BuildTruncType _ (ff p)) _)
      end.
      refine (O_rec_dep _ shf _).1.
      unfold shf; clear shf; cbn.
      intro p. cbn. 
      (* rewrite eisretr.  *)
      (* unfold function_lift_modal. *)
      pose (r := λ P Q f, ap10 (O_rec_retr n nj P Q f)); rewrite r; clear r.
      (* unfold θ1. *)

      pose (@equiv_path_Tr ua n Tθ1 (t a) (t b)).
      
      path_via (O_unit nj _ (ap (tr (n:=n.+1))
                                (tp a b
                                    (ap
                                       (Trunc_rec
                                          θ1) (e (e^-1 p)))))).
      apply ap. apply ap.
      apply ap. apply ap. symmetry; apply eisretr.
      path_via (O_unit nj _ (e (e^-1 p))).
      2: apply ap; apply eisretr.
      generalize (e^-1 p). intro q. cbn in *.
      revert q. refine (Trunc_ind _ _).
      intro q.
      cbn.
      rewrite <- ap_compose. cbn. clear p. clear e.

      transparent assert (foo : (O nj (BTT {e:separated_unit E a = separated_unit E b & ap tr (tp a b e) = ap tr q}))).
      { pose (hfiber (λ e, ap (tr (n:=n.+1)) (tp a b e)) (ap tr q)).
        unfold hfiber in T0.
        pose (@islex_to_hfibers_preservation ua fs n0 mod_nj islex_mod_nj
                                             (BTT (separated_unit E a = separated_unit E b))
                                             (BTT (c a = c b))
                                             (λ e, ap (tr (n:=n.+1)) (tp a b e))
                                             (ap tr q)
             ). unfold hfiber in p. cbn in p.

        match goal with
        |[ p: ?XX = _ |- ?YY] => assert (XX = YY)
        end.
        admit.

        destruct X.
        apply (transport idmap p^).

        refine (exist _ _ _).
        apply O_unit.
        exact (function_lift_modal n nj (BTT (c a = c b)) {|
                                     st := BTT (separated_unit E a = separated_unit E b);
                                     subu_struct := IsSubu_separated_unit_paths a b |} (ap (Trunc_rec θ1))
                                   (O_unit nj _ (ap tr q))).

        cbn.
        unfold function_lift, function_lift_modal. cbn.
        pose (r := λ P Q f, ap10 (O_rec_retr n nj P Q f)); repeat rewrite r; clear r.
        
        assert {e: separated_unit E a = separated_unit E b & tp a b e = q}.
        admit.
        destruct X as [e p]; destruct p.
        unfold θ1.
        rewrite (T_rec_beta_tp (separated_Type E) (separated_unit E)
                               (λ (a0 b0 : E) (p : separated_unit E a0 = separated_unit E b0), p)
                               (λ a0 : E, 1)).
        

        
        admit.
        - unfold Sect.
          match goal with
          |[|- forall p:?XX, ?ff p] =>
           pose (shf := λ p:XX, Build_subuniverse_Type n nj
                                                       (BuildTruncType _ (ff p)) _)
          end.
          refine (O_rec_dep _ shf _).1.
          unfold shf; clear shf; cbn. intro p.
          unfold ab_cacb'.
          apply moveR_equiv_V.
          unfold function_lift_modal.
          pose (r := λ P Q f, ap10 (O_rec_retr n nj P Q f)); repeat rewrite r; clear r.
          destruct p. cbn.
          rewrite tp_1. reflexivity.
          
          
          


          
          Definition fooo :
            (forall x y:E, IsEquiv (function_lift_modal n nj _ (Build_subuniverse_Type n nj (BTT (separated_unit E x = separated_unit E y)) _) (ap (x:=x) (y:=y) ((separated_unit E)))))
            ->
            forall x y:Trunc (n.+1) Tθ1, IsEquiv (function_lift_modal n nj _ (Build_subuniverse_Type n nj (BTT (Trunc_rec θ1 x = Trunc_rec θ1 y)) _) (ap (x:=x) (y:=y) (Trunc_rec θ1))).
          Proof.
            intro H.
            refine (Trunc_ind _ _).
            intro aa; refine trunc_forall.
            intro a. apply (@trunc_leq -1 (n.+1) tt _ _).
            intro a.
            refine (Trunc_ind _ _).
            intro bb. apply (@trunc_leq -1 (n.+1) tt _ _).    
            intro b.

            revert a b.

            refine (T_ind _ _ _ _); try (intros; apply path_ishprop).
            intro a.
            refine (T_ind _ _ _ _); try (intros; apply path_ishprop).
            intro b.

            refine (isequiv_adjointify _ _ _).
            - intro p. apply O_unit. cbn. apply ap. cbn in *.
              apply tp. exact p.
            - intro p. cbn in *. unfold function_lift_modal.
              pose (r := λ P Q f, ap10 (O_rec_retr n nj P Q f)); rewrite r; clear r.
              cbn.
              rewrite <- ap_compose. cbn. unfold θ1. cbn.
              apply (T_rec_beta_tp (separated_Type E) (separated_unit E)
                                   (λ (a0 b0 : E) (p0 : separated_unit E a0 = separated_unit E b0), p0)
                                   (λ a0 : E, 1)).
            - unfold Sect.
              match goal with
              |[|- forall x:?XX, _] =>
               transparent assert (shf : (XX -> subuniverse_Type nj))
              end.
              { intro x.
                refine (Build_subuniverse_Type n nj
                                               (BuildTruncType _ (O_unit nj
                                                                         (default_TruncType n (tr (t a) = tr (t b))
                                                                                            (istrunc_paths (tr (t a)) (tr (t b))))
                                                                         (ap tr
                                                                             (tp a b
                                                                                 (function_lift_modal n nj
                                                                                                      (default_TruncType n (tr (t a) = tr (t b))
                                                                                                                         (istrunc_paths (tr (t a)) (tr (t b))))
                                                                                                      {|
                                                                                                        st := BTT (Trunc_rec θ1 (tr (t a)) = Trunc_rec θ1 (tr (t b)));
                                                                                                        subu_struct := IsSubu_θ1_path (tr (t a)) (tr (t b)) |}
                                                                                                      (ap (Trunc_rec θ1)) x))) = x)) _). }
              refine (O_rec_dep _ shf _).1.
              unfold shf; clear shf; cbn.
              intro p. apply ap.
              unfold function_lift_modal.
              pose (r := λ P Q f, ap10 (O_rec_retr n nj P Q f)); rewrite r; clear r.
              
              Definition Tθ1 := Coeq (λ x:{e:E /\ E & separated_unit E (fst e) = separated_unit E (snd e)}, fst x.1)
                                     (λ x:{e:E /\ E & separated_unit E (fst e) = separated_unit E (snd e)}, snd x.1).
              Definition θ1 : Tθ1 -> (separated_Type E).
              Proof.
                refine (Coeq_rec _ _ _).
                exact (separated_unit E).
                intros x; exact x.2.
              Defined.
              
              Instance IsTrunc_separated_Type : IsTrunc (n.+1) (separated_Type E).
          Admitted.

          Definition Tθ2 := Coeq (λ x:{e:Tθ1 /\ Tθ1 & θ1 (fst e) = θ1 (snd e)}, fst x.1)
                                 (λ x:{e:Tθ1 /\ Tθ1 & θ1 (fst e) = θ1 (snd e)}, fst x.1).

          Instance IsSubu_separated_unit_paths (x y:E)
            : IsSubu n nj (BTT (separated_unit E x = separated_unit E y)).
          pose (separated_nj_paths (BuildTruncType _ (separated_Type E)) (separated_Type_is_separated E) (separated_unit E x) (separated_unit E y)).
          unfold BTT. 
          match goal with
          |[i: IsSubu _ _ {| trunctype_type := _; istrunc_trunctype_type := ?XX|} |- IsSubu _ _ {| trunctype_type := _; istrunc_trunctype_type := ?YY|}]
           => assert (r:XX=YY) by apply path_ishprop
          end.
          destruct r.
          exact i.
  Qed.

  Definition bar : forall x y:E, IsEquiv (function_lift n nj _ _ (ap (x:=x) (y:=y) ((separated_unit E)))).
  Proof.
    intros x y.

    (* refine (isequiv_adjointify _ _ _). *)
    (* - apply O_rec. simpl. *)
    (*   intro p. *)
    (*   apply (equiv_path _ _ ((ap trunctype_type (ap (@st n nj) (ap10 (p..1) y))))^). *)
    (*   apply O_unit; reflexivity. *)
    (* - intro p. *)
    (*   cbn. *)
    (*   pose mu_modal_paths_aux. cbn in p0. *)
    

    pose (φ := separated_unit_paths_are_nj_paths_inv E x y).
    pose (η := O_unit nj (BTT (separated_unit E x = separated_unit E y))).
    assert ((η o φ) = (function_lift n nj _ _ (ap (x:=x) (y:=y) ((separated_unit E))))).
    { 
      apply path_forall; intro p.
      unfold function_lift, default_TruncType.
      unfold sheaf_induction.BTT, BTT in *.
      
      match goal with
      |[|- _ = O_rec _ _ ?XX (O nj ?YY) _ _] =>
       set (xy := XX) in *; set (sxsy := YY) in *
      end.
      assert (Subu_sxsy: IsSubu sheaf_def_and_thm.n nj sxsy).
      pose (separated_nj_paths (BuildTruncType _ (separated_Type E)) (separated_Type_is_separated E) (separated_unit E x) (separated_unit E y)).
      unfold BTT. unfold sxsy.
      match goal with
      |[i: IsSubu _ _ {| trunctype_type := _; istrunc_trunctype_type := ?XX|} |- IsSubu _ _ {| trunctype_type := _; istrunc_trunctype_type := ?YY|}]
       => assert (r:XX=YY) by apply path_ishprop
      end.
      destruct r.
      exact i.
      
      revert p.
      transparent assert (shf : (O nj xy -> subuniverse_Type nj)).
      { intro p.
        refine (Build_subuniverse_Type n nj
                                       (BuildTruncType _ (η (φ p) =
                                                          O_rec n nj xy (O nj sxsy)
                                                                (λ x0 : xy, O_unit nj sxsy (ap (separated_unit E) x0)) p))
                                       _). }
      refine (O_rec_dep _ shf _).1.
      unfold shf; clear shf; simpl.
      intro p.

      pose (p0 := O_rec_O_unit sheaf_def_and_thm.n nj (Build_subuniverse_Type sheaf_def_and_thm.n nj sxsy _) xy (ap (separated_unit E)) (O_unit (underlying_subu sheaf_def_and_thm.n sheaf_def_and_thm.mod_nj)
                                                                                                                                                xy p)).
      cbn in p0; rewrite <- p0; clear p0.
      apply ap.
      pose (r := λ P Q f, ap10 (O_rec_retr n nj P Q f)). rewrite r; clear r.
      destruct p; cbn.
      apply (@equiv_inj _ _ (equiv_inv _ (IsEquiv := isequiv_path_sigma_hprop)) _).
      rewrite eissect. simpl.
      apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
      unfold path_forall at 1. rewrite eisretr.
      apply path_forall; intro e. cbn.
      apply (@equiv_inj _ _ (equiv_inv _ (IsEquiv := isequiv_unique_subuniverse _ _ _ _)) _).
      rewrite eissect; cbn.
      rewrite concat_1p, concat_p1.
      match goal with
      |[|- ap _ ?uu = _] => assert (r: 1 = uu)
      end.
      2:destruct r; reflexivity.
      apply (@equiv_inj _ _ (equiv_inv _ (IsEquiv := isequiv_path_sigma_hprop)) _).
      simpl. unfold pr1_path.
      rewrite ap_pr1_path_sigma_hprop.
      apply (@equiv_inj _ _ _ (isequiv_equiv_path _ _)).
      rewrite equiv_path_path_universe_uncurried.
      unfold symmetric_equiv. cbn.
      unfold equiv_path.
      apply path_equiv.
      apply path_forall; intro p.
      cbn.
      unfold mu_modal_paths_func_univ_func; cbn.
      pose (r:= path_forall (λ u:x=e, ap10 (O_rec_retr n nj xy (O sheaf_induction.nj (sheaf_induction.BTT (x = e))) (λ v : x = x, O_unit sheaf_induction.nj (sheaf_induction.BTT (x = e)) (v^ @ u))) 1)).
      simpl in r. rewrite r; clear r. cbn.
      match goal with
      |[|- _ = O_rec _ _ _ _ ?ff _ ]
       => assert (rr: (λ u : x = e,
                             O_unit sheaf_induction.nj (sheaf_induction.BTT (x = e)) u) = ff)
      end.
      apply path_forall; intro u. apply ap. rewrite concat_1p; reflexivity.
      destruct rr.
      exact (ap10 (O_rec_sect n nj (BTT (x=e)) (O nj (BTT (x=e))) idmap) p)^. }
    
    rewrite <- X.
    refine isequiv_compose.
    refine (isequiv_adjointify _ _ _).
    exact (separated_unit_paths_are_nj_paths_fun E x y).
    exact (separated_unit_paths_are_nj_paths_sect E x y).
    exact (separated_unit_paths_are_nj_paths_retr E x y).
    assert (IsSubu n nj (BTT (separated_unit E x = separated_unit E y))).
    pose (separated_nj_paths (BuildTruncType _ (separated_Type E)) (separated_Type_is_separated E) (separated_unit E x) (separated_unit E y)).
    unfold BTT.
    match goal with
    |[i: IsSubu _ _ {| trunctype_type := _; istrunc_trunctype_type := ?XX|} |- IsSubu n nj {| trunctype_type := _; istrunc_trunctype_type := ?YY|}]
     => assert (r:XX=YY) by apply path_ishprop
    end.
    destruct r.
    exact i.

    refine (O_modal_equiv n nj (Build_subuniverse_Type n nj (BTT (separated_unit E x = separated_unit E y)) _)).
  Defined.
  
  Instance IsSubu_θ1_path (x y:Trunc (n.+1) Tθ1) (H:= separated_Type_is_TruncType_Sn E)
    : IsSubu n nj (@BuildTruncType n (Trunc_rec θ1 x = Trunc_rec θ1 y) (istrunc_paths (n:=n) (H:=H) _ _)).
  Proof.
  Admitted.
  
  Definition baar : (forall x y:E, IsEquiv (function_lift_modal n nj _ (Build_subuniverse_Type n nj (BTT (separated_unit E x = separated_unit E y)) _) (ap (x:=x) (y:=y) ((separated_unit E))))).
  Proof.
    intros x y.
    match goal with
    |[|- IsEquiv ?FF] => assert (r: separated_unit_paths_are_nj_paths_inv E x y = FF)
    end.
    { apply path_forall.
      transparent assert (shf: ( O nj (BTT (x=y)) -> subuniverse_Type nj)).
      { intro p.
        refine (Build_subuniverse_Type n nj
                                       (BuildTruncType _ (separated_unit_paths_are_nj_paths_inv E x y p =
                                                          function_lift_modal n nj (default_TruncType n (x = y) (istrunc_paths x y))
                                                                              {|
                                                                                st := BTT (separated_unit E x = separated_unit E y);
                                                                                subu_struct := IsSubu_separated_unit_paths x y |}
                                                                              (ap (separated_unit E)) p))
                                       _).
        exact ua. exact fs.
        apply istrunc_paths.
        pose (i:= subuniverse_paths n nj (Build_subuniverse_Type n nj (BTT (separated_unit E x = separated_unit E y)) _)
                                    (separated_unit_paths_are_nj_paths_inv E x y p)
                                    (function_lift_modal n nj
                                                         (default_TruncType n (x = y) (istrunc_paths x y))
                                                         {|
                                                           st := BTT (separated_unit E x = separated_unit E y);
                                                           subu_struct := IsSubu_separated_unit_paths x y |}
                                                         (ap (separated_unit E)) p)).
        match goal with
        |[i: IsSubu _ _ {| trunctype_type := _; istrunc_trunctype_type := ?XX|} |- IsSubu _ _ {| trunctype_type := _; istrunc_trunctype_type := ?YY|}]
         => assert (r:XX=YY) by apply path_ishprop
        end.
        destruct r.
        exact i.
      }

      refine (O_rec_dep _ shf _).1.
      unfold shf; clear shf; cbn.
      unfold function_lift_modal.
      cbn.
      intro p.
      pose (r := λ P Q f, ap10 (O_rec_retr n nj P Q f)). rewrite r; clear r.
      
      apply (@equiv_inj _ _ (equiv_inv _ (IsEquiv := isequiv_path_sigma_hprop)) _).
      rewrite eissect. simpl.
      apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
      unfold path_forall at 1. rewrite eisretr.
      apply path_forall; intro e. cbn.
      apply (@equiv_inj _ _ (equiv_inv _ (IsEquiv := isequiv_unique_subuniverse _ _ _ _)) _).
      rewrite eissect; cbn.
      rewrite concat_1p, concat_p1. cbn.
      destruct p; cbn.
      match goal with
      |[|- ap _ ?uu = _] =>
       (* pose uu *)
       assert (r: 1 = uu)
      end.
      2:destruct r; reflexivity.
      apply (@equiv_inj _ _ (equiv_inv _ (IsEquiv := isequiv_path_sigma_hprop)) _).
      simpl. unfold pr1_path.
      rewrite ap_pr1_path_sigma_hprop.
      apply (@equiv_inj _ _ _ (isequiv_equiv_path _ _)).
      rewrite equiv_path_path_universe_uncurried.
      unfold symmetric_equiv. cbn.
      unfold equiv_path.
      apply path_equiv.
      apply path_forall; intro p.
      cbn.
      unfold mu_modal_paths_func_univ_func; cbn.
      pose (r:= path_forall (λ u:x=e, ap10 (O_rec_retr n nj _ (O sheaf_induction.nj (sheaf_induction.BTT (x = e))) (λ v : x = x, O_unit sheaf_induction.nj (sheaf_induction.BTT (x = e)) (v^ @ u))) 1)).
      simpl in r. rewrite r; clear r. cbn.
      match goal with
      |[|- _ = O_rec _ _ _ _ ?ff _ ]
       => assert (rr: (λ u : x = e,
                             O_unit sheaf_induction.nj (sheaf_induction.BTT (x = e)) u) = ff)
      end.
      apply path_forall; intro u. apply ap. rewrite concat_1p; reflexivity.
      destruct rr.
      exact (ap10 (O_rec_sect n nj (BTT (x=e)) (O nj (BTT (x=e))) idmap) p)^. }
    destruct r.
    refine (isequiv_adjointify _ _ _).
    exact (separated_unit_paths_are_nj_paths_fun E x y).
    exact (separated_unit_paths_are_nj_paths_sect E x y).
    exact (separated_unit_paths_are_nj_paths_retr E x y).
  Defined.

  Definition Tid (A:Type)
    := Coeq (λ x:{a:A*A & fst a = snd a}, fst x.1)
            (λ x:{a:A*A & fst a = snd a}, snd x.1).

  Definition Im_coequalizes_kernel_pair A B (f : A -> B) : (toIm f) o (λ x:{a:A*A & f (fst a) = f (snd a)}, fst x.1) = (toIm f) o (λ x:{a:A*A & f (fst a) = f (snd a)}, snd x.1).
  Proof.
    apply path_forall; intros [[x y] p].
    cbn in *.
    unfold toIm.
    refine (path_sigma_hprop _ _ _). exact p.
  Defined.

  Definition is_coequalizer A B (f g : A -> B) X (coequalizer : {m : B -> X & m o f =  m o g}) :=
    forall Y:hProp, IsEquiv (fun x : X -> Y => 
                               existT (fun m => m o f =  m o g) (x o pr1 coequalizer) (ap (fun u => x o u) (pr2 coequalizer))).
  
  Lemma fooqefosuih (A B:Type) (f:A -> B) (Eqf: IsEquiv f)
    : is_coequalizer {a:A*A & f (fst a) = f (snd a)} A (λ x, fst x.1) (λ x, snd x.1) (Im f) (toIm f;(Im_coequalizes_kernel_pair _ _ f)).
  Proof.
    intro Z.
    refine (isequiv_adjointify _ _ _).
    - intros [α p].
      intros [b x].
      revert x. refine (Trunc_rec _).
      intros [a q].
      exact (α a).
    - intros [α p].
      refine (path_sigma' _ _ _).
      apply path_forall; intro a. reflexivity.
      apply path_ishprop.
    (* cbn. *)
    (* rewrite path_forall_1. cbn. *)
    (* apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)). *)
    (* apply path_forall; intro a. *)
    (* cbn. *)
    (* rewrite apD10_ap_postcompose. *)
    (* unfold path_forall; rewrite eisretr. *)
    (* cbn. *)
    (* destruct a as [[a b] q]; cbn in *. destruct q. cbn. *)
    (* admit. *)
    - intro a. apply path_forall; intros [x q].
      revert q.
      refine (Trunc_ind _ _). intros [b q]. cbn. apply ap.
      unfold toIm. cbn. refine (path_sigma' _ _ _).
      exact q.
      destruct q. cbn. reflexivity.
  Defined.
  
  reflexivity.
  

  Lemma sese (A:Type) : IsEquiv (coeq : A -> Tid A).
  Proof.
    refine (isequiv_adjointify _ _ _).
    - refine (Coeq_rec _ _ _).
      exact idmap.
      intros x. exact x.2.
    - refine (Coeq_ind _ _ _).
      intro a; cbn. reflexivity.
      intros [[a b] p]; cbn.
      rewrite transport_paths_FlFr. cbn.
      rewrite ap_compose.
      rewrite (Coeq_rec_beta_cp A idmap (λ x : ∃ a0 : A ∧ A, fst a0 = snd a0, pr2 x) ((a, b); p)).
      cbn. hott_simpl. cbn in *. 
      admit.
    - intro a.
      reflexivity.
      
      Definition fooo :
        (* (forall x y:E, IsEquiv (function_lift_modal n nj _ (Build_subuniverse_Type n nj (BTT (separated_unit E x = separated_unit E y)) _) (ap (x:=x) (y:=y) ((separated_unit E))))) *)
        (*   ->  *)
        forall x y:Trunc (n.+1) Tθ1, IsEquiv (function_lift_modal n nj _ (Build_subuniverse_Type n nj (BTT (Trunc_rec θ1 x = Trunc_rec θ1 y)) _) (ap (x:=x) (y:=y) (Trunc_rec θ1))).
      Proof.
        
        (* intro H. *)
        pose (H := baar).
        refine (Trunc_ind _ _).
        intro aa; refine trunc_forall.
        intro a. apply (@trunc_leq -1 (n.+1) tt _ _).
        intro a.
        refine (Trunc_ind _ _).
        intro bb. apply (@trunc_leq -1 (n.+1) tt _ _).    
        intro b.

        revert a b.

        refine (Coeq_ind2 _ _ _ _ _); try (intros; apply path_ishprop).
        intros a b. simpl.
        specialize (H a b).
        pose (inv := equiv_inv _ (IsEquiv := H)).
        (* destruct H as [inv retr sect _]. *)
        (* unfold Sect in sect. *)
        refine (isequiv_adjointify _ _ _).
        + intro x.
          generalize (inv x). apply function_lift. exact (ap (λ u, tr (coeq u))). 
        + intro p.
          unfold function_lift_modal at 1.
          unfold default_TruncType in *.

          match goal with
          |[|- (O_rec _ _ _ ?SUBU ?GG (function_lift _ _ ?XX ?YY ?FF _)) = _] =>
           pose (ap10 (reflect_factoriality_post n nj XX YY SUBU GG FF) (inv p))
          end.
          rewrite p0. clear p0.
          match goal with
          |[|- (O_rec _ _ _ _ (λ x, (ap ?GG (ap ?FF x))) _) = _] =>
           pose (path_forall (λ x, (ap_compose (x:=a) (y:=b) FF GG x)))
          end.
          rewrite <- p0; clear p0.
          cbn.
          pose (retr := eisretr _ (IsEquiv := H) p).
          cbn in retr. unfold function_lift_modal in retr.
          match goal with
          |[retr: O_rec _ _ _ ?XX _ _ = _ |- O_rec _ _ _ ?YY _ _ = _]
           => assert (r: YY = XX)
          end.
          apply unique_subuniverse. apply path_trunctype. apply equiv_idmap.
          cbn.
          admit (* FIX ME*).
        + intro p.
          unfold function_lift_modal, function_lift. cbn.
          match goal with
          |[|- O_rec n nj _ (O nj ?XX) _ _ = _] => pose (CaCb := XX)
          end.
          pose (r := ap10 (reflect_factoriality_pre n nj CaCb {|
                                                      st := BTT (separated_unit E a = separated_unit E b);
                                                      subu_struct := IsSubu_θ1_path (tr (coeq a)) (tr (coeq b)) |}
                                                    (O nj (default_TruncType n (a = b) (istrunc_paths a b)))
                                                    inv (ap (Trunc_rec θ1))) p).
          cbn in r; unfold CaCb in r; rewrite r; clear r.
          revert p.
          refine (O_rec_dep _ (λ p, (Build_subuniverse_Type n nj
                                                            (BuildTruncType _ (

                                                                              O_rec n nj (default_TruncType n (a = b) (istrunc_paths a b))
                                                                                    (O nj
                                                                                       CaCb)
                                                                                    (λ x : a = b,
                                                                                           O_unit nj
                                                                                                  CaCb
                                                                                                  (ap (λ u : E, tr (coeq u)) x))
                                                                                    (O_rec n nj
                                                                                           CaCb
                                                                                           (O nj (default_TruncType n (a = b) (istrunc_paths a b)))
                                                                                           (λ x : CaCb, inv (ap (Trunc_rec θ1) x)) p) = p)) _)) _).1.
          intro p; cbn.      
          pose (r := λ P Q f, ap10 (O_rec_retr n nj P Q f)). rewrite r; clear r.
          unfold CaCb in p.



          
          pose (O_equiv n nj (default_TruncType n (a = b) (istrunc_paths a b)) 
                        (O nj CaCb)). cbn in i.

          match goal with
          |[|- O_rec _ _ _ _ _ ?UU = _] =>
           assert ({x:  (BTT (a=b)) & UU =  (O_unit nj _ x)}) by admit
          end.
          destruct X as [xx q].
          rewrite q; clear q.
          pose (r := λ P Q f, ap10 (O_rec_retr n nj P Q f)). rewrite r; clear r.
          rewrite (sect (O_unit nj _ xx)).
          cbn.
          pose (r := λ P Q f, ap10 (O_rec_retr n nj P Q f)). rewrite r; clear r.
          apply ap.

          
          
          apply (transport (λ U, O_rec n nj (default_TruncType n (a = b) (istrunc_paths a b)) (O nj CaCb) (λ x : a = b, O_unit nj CaCb (ap (λ u : E, tr (coeq u)) x)) (inv U) = O_unit (underlying_subu sheaf_def_and_thm.n sheaf_def_and_thm.mod_nj) CaCb
                                                                                                                                                                                       p) q^).
          rewrite q.

          
          Definition foo :
            (forall x y:E, IsEquiv (function_lift n nj _ _ (ap (x:=x) (y:=y) ((separated_unit E)))))
            -> 
            forall x y:Trunc (n.+1) Tθ1, IsEquiv (function_lift n nj _ _ (ap (x:=x) (y:=y) (Trunc_rec θ1))).
          Proof.
            intro H.
            refine (Trunc_ind _ _).
            intro aa; refine trunc_forall.
            intro a. apply (@trunc_leq -1 (n.+1) tt _ _).
            intro a.
            refine (Trunc_ind _ _).
            intro bb. apply (@trunc_leq -1 (n.+1) tt _ _).    
            intro b.

            revert a b.

            refine (Coeq_ind2 _ _ _ _ _); try (intros; apply path_ishprop).
            intros a b. simpl.
            specialize (H a b).
            destruct H as [inv retr sect _].
            unfold Sect in sect.
            refine (isequiv_adjointify _ _ _).
            + intro x.
              generalize (inv x). apply function_lift. exact (ap (λ u, tr (coeq u))). 
            + assert (Subu_sxsy: IsSubu n nj (BTT (separated_unit E a = separated_unit E b))).
              admit.
              intro p.
              unfold function_lift at 1.
              unfold default_TruncType in *.

              match goal with
              |[|- (O_rec _ _ _ ?SUBU ?GG (function_lift _ _ ?XX ?YY ?FF _)) = _] =>
               pose (ap10 (reflect_factoriality_post n nj XX YY SUBU GG FF) (inv p))
              end.
              rewrite p0. clear p0.
              match goal with
              |[|- (O_rec _ _ _ _ (λ x, O_unit nj ?FOO (ap ?GG (ap ?FF x))) _) = _] =>
               pose (path_forall (λ x, ap (O_unit nj FOO) (ap_compose (x:=a) (y:=b) FF GG x)))
              end.
              rewrite <- p0; clear p0.
              cbn.
              specialize (retr p).
              unfold function_lift in retr.
              exact retr.
            +
              intro p.
              match goal with |[p: _ (_ (O nj ?XX)) |- _] => set (CaCb := XX) in * end.
              revert p.
              transparent assert (shf: (O nj CaCb -> subuniverse_Type nj)).
              { intro p.
                refine (Build_subuniverse_Type n nj
                                               (BuildTruncType _
                                                               (function_lift n nj (default_TruncType n (a = b) (istrunc_paths a b))
                                                                              (default_TruncType n (tr (coeq a) = tr (coeq b))
                                                                                                 (istrunc_paths (tr (coeq a)) (tr (coeq b))))
                                                                              (λ p0 : default_TruncType n (a = b) (istrunc_paths a b),
                                                                                      ap (λ u : E, tr (coeq u)) p0)
                                                                              (inv
                                                                                 (function_lift n nj
                                                                                                (default_TruncType n (tr (coeq a) = tr (coeq b))
                                                                                                                   (istrunc_paths (tr (coeq a)) (tr (coeq b))))
                                                                                                (default_TruncType n (separated_unit E a = separated_unit E b)
                                                                                                                   (istrunc_paths (separated_unit E a) (separated_unit E b)))
                                                                                                (ap
                                                                                                   (Trunc_rec
                                                                                                      (Coeq_rec (separated_Type E) (separated_unit E)
                                                                                                                (λ
                                                                                                                   x : ∃ e : E ∧ E,
                                                                                                                    separated_unit E (fst e) = separated_unit E (snd e),
                                                                                                                   pr2 x)))) p)) = p)) _). }
              refine (O_rec_dep _ shf _).1.
              unfold shf; clear shf; cbn.
              intro p.
              assert (Subu_sxsy: IsSubu n nj (BTT (separated_unit E a = separated_unit E b))).
              admit.
              unfold Sect in *.
              unfold function_lift.
              pose (O_rec_O_unit n nj (Build_subuniverse_Type n nj (BTT (separated_unit E a = separated_unit E b)) _) CaCb (λ x, (ap
                                                                                                                                    (Trunc_rec
                                                                                                                                       (Coeq_rec (separated_Type E) (separated_unit E)
                                                                                                                                                 (λ
                                                                                                                                                    x0 : ∃ e : E ∧ E,
                                                                                                                                                     separated_unit E (fst e) =
                                                                                                                                                     separated_unit E (snd e), 
                                                                                                                                                    pr2 x0))) x))). simpl in p0.
              rewrite <- p0; clear p0.
              pose (r := λ P Q f, ap10 (O_rec_retr n nj P Q f)). rewrite r; clear r.

              pose (ap
                      (Trunc_rec
                         (Coeq_rec (separated_Type E) (separated_unit E)
                                   (λ
                                      x0 : ∃ e : E ∧ E,
                                       separated_unit E (fst e) = separated_unit E (snd e),
                                      pr2 x0))) p). cbn in p0.

              Set Printing Implicit.
              assert (p = ap tr (cp (a,b))).
              
              pose (r := λ P Q f, ap10 (O_rec_sect n nj P Q f)).
              unfold O_rec. cbn in r.
              assert (fooo : forall (m:trunc_index) (A:Type) (x y:A) (p:tr x = tr y :> Trunc m A),
                         ap Trunc_rec p = ap Trunc_rec p).

              
              match goal with
              |[|- function_lift _ _ _ _ _ (inv (function_lift _ _ _ _ ?FF _)) = _] =>
               pose (foo := (separated_unit_paths_are_nj_paths_fun E a b) (FF p))
              end.
              unfold separated_unit_paths_are_nj_paths_fun in foo; cbn in foo.
              specialize (sect foo).
              
              rewrite ap_compose.
              specialize (sect  (inv (function_lift n nj
                                                    (default_TruncType n (tr (coeq a) = tr (coeq b))
                                                                       (istrunc_paths (tr (coeq a)) (tr (coeq b))))
                                                    (default_TruncType n (separated_unit E a = separated_unit E b)
                                                                       (istrunc_paths (separated_unit E a) (separated_unit E b)))
                                                    (ap
                                                       (Trunc_rec
                                                          (Coeq_rec (separated_Type E) (separated_unit E)
                                                                    (λ
                                                                       x : ∃ e : E ∧ E,
                                                                        separated_unit E (fst e) = separated_unit E (snd e),
                                                                       pr2 x)))) p))).
              
              
          Admitted.


          
          Lemma foo : cT1 E <~> Trunc (n.+1) Tθ1.
          Proof.
            unfold cT1. simpl.
            match goal with
            |[|- Trunc _ ?XX <~> Trunc _ ?YY] => assert (XX <~> YY)
            end.

            refine (equiv_functor_coeq' _ _ _ _).
            - refine (equiv_functor_sigma_id _).
              intros a.
              exact (separated_unit_paths_are_nj_paths E (fst a) (snd a))^-1.
            - apply equiv_idmap.
            - intros [[a b] p]. reflexivity.
            - intros [[a b] p]. reflexivity.
            - refine (equiv_adjointify _ _ _ _).
              apply Trunc_rec.
              intro x; apply tr; revert x.
              apply X.

              apply Trunc_rec.
              intro x; apply tr; revert x.
              apply X^-1.

              refine (Trunc_ind _ _). intro x; cbn.
              apply ap.
              apply eisretr.

              refine (Trunc_ind _ _). intro x; cbn.
              apply ap.
              apply eissect.
          Defined.

          Lemma foo2 : cT2 E <~> Trunc (n.+1) Tθ2.
          Proof.
            unfold cT3. simpl.
            match goal with
            |[|- Trunc _ ?XX <~> Trunc _ ?YY] => assert (XX <~> YY)
            end.
            { refine (equiv_functor_coeq' _ _ _ _).
              refine (equiv_functor_sigma' _ _).
              refine (equiv_functor_prod' _ _).
              apply foo.
              
              Instance IsTrunc_separated_Type : IsTrunc (n.+1) (separated_Type E).
          Admitted.
          
          Lemma cT1_Tf : cT1 E <~> Trunc (n.+1) (Tf (separated_unit E) 1%nat).
          Proof.
            unfold cT1. unfold Tf. simpl.
            unfold KP.
            refine (equiv_adjointify _ _ _ _).
            - refine (Trunc_rec _). intro x; apply tr; revert x.
              refine (Coeq_rec _ _ _).
              intro e. refine (colim _ _). simpl. exact False. exact e.
              intros [[a b] p]. cbn in *.
              pose (separated_unit_paths_are_nj_paths E a b)^-1.
              pose (@pp coequalizer_graph (KP_diag (separated_unit E)) True False False (a;(b;p0 p))). simpl in p1.
              pose (@pp coequalizer_graph (KP_diag (separated_unit E)) True False False (b;(a;(p0 p)^))). simpl in p2.
              
              
              Definition foo_aux (T1 T2:TruncType (n.+1)) (φ:T1 -> T2)
                         (T3 := Trunc (n.+1) (Coeq (λ x:{e:T1*T1 & O nj (BTT (φ (fst e) = φ (snd e)))}, fst x.1) (λ x, snd x.1)))
                         (ψ :T2 -> T3)
                : {T4: TruncType (n.+1) & T3 -> T4}.
              Proof.
                pose (PB := {e:T2*T2 & O nj (BTT (ψ (fst e) = ψ (snd e)))}).
                exists (BuildTruncType _ (Trunc (n.+1) (Coeq (λ x:PB, fst x.1) (λ x:PB, snd x.1)))).

                transparent assert (hh : ({x:T1/\T1 & O nj (BTT (φ (fst x) = φ (snd x)))} -> {x:T2/\T2 & O nj (BTT (ψ (fst x) = ψ (snd x)))})).
                { intros [[a b] p].
                  exists (φ a, φ b).
                  revert p; apply O_rec; intro p; apply O_unit.
                  exact (ap _ p). }

                refine (Trunc_rec _). refine (Coeq_rec _ _ _).
                intro e. apply tr. apply coeq. apply φ. exact e.

                intros x. cbn.
                pose (cp (f := (λ x:PB, fst x.1))
                         (g := (λ x:PB, snd x.1))
                         (hh x)).
                apply ap. exact p.
              Defined.

              Definition bar_aux (E:TruncType (n.+1))
                : forall m:nat, {T1:TruncType (n.+1) &
                                    {T2:TruncType (n.+1) &
                                        {φ:T1 -> T2 &
                                                 T2 -> Trunc (n.+1) (Coeq (λ x:{e:T1*T1 & O nj (BTT (φ (fst e) = φ (snd e)))}, fst x.1) (λ x, snd x.1))}}}.
              Proof.
                intro m. induction m as [| m [T1 [T2 [φ ψ]]]].
                exists E. exists E.
                simpl.
                exists idmap.
                intro e. apply tr. apply coeq. exact e.
                exists T2.
                pose (foo_aux T1 T2 φ ψ).
                exists s.1.
                
                exists (BuildTruncType _ (Trunc (n.+1) (Coeq (λ x:{e:T1*T1 & O nj (BTT (φ (fst e) = φ (snd e)))}, fst x.1) (λ x, snd x.1)))).
                cbn.
                exists ψ.
                exact (foo_aux T1 T2 T3 φ

                               Definition foo (E:TruncType (n.+1)) : diagram mappingtelescope_graph.
                       Proof.
                         refine (Build_diagram _ _ _).
                         - apply nat_ind3.
                           exact E. exact E. exact (Trunc (n.+1)
                                                          (Coeq (λ x:{x:E/\E & O nj (BTT (fst x=snd x))}, fst x.1)
                                                                (λ x:{x:E/\E & O nj (BTT (fst x=snd x))}, snd x.1))).
                           intros m T1 T2 T3.
                           (* End Foo. *)