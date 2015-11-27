(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import Limit.
Require Import T T_telescope.
Require Import Forall_ Equivalences_ epi_mono reflective_subuniverse modalities OPaths.
Require Import sheaf_base_case.
Require Import sheaf_def_and_thm.


Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
Local Open Scope type_scope.

  
Section Tf_Omono_sep.

  
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

  Definition Omono_sep (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B)
    : Type.
  Proof.
    pose (separated_nj_paths B sepB).
    exact (forall x y:A, IsEquiv (O_rec n nj (BuildTruncType _ (x=y)) (Build_subuniverse_Type n nj (BuildTruncType _ (f x = f y)) (i (f x) (f y))) (ap f))).
  Defined.

  Lemma OT_Cover (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B) (Omono_f : Omono_sep A B sepB f) (a:A)
    : Trunc (n.+1) (T f) -> subuniverse_Type nj.
  Proof.
    refine (Trunc_rec _).
    apply subuniverse_Type_is_TruncTypeSn. exact ua. 
    refine (T_rec _ _ _ _).
    intro e; exact (O nj (BuildTruncType _ (a=e))).
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

  Lemma OT_encode (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B) (Omono_f : Omono_sep A B sepB f) (a:A)
    : forall e:Trunc (n.+1) (T f), O nj (BuildTruncType _ ((tr o t) a = e)) -> OT_Cover A B sepB f Omono_f a e.
  Proof.
    intros e q. exact (Otransport (OT_Cover A B sepB f Omono_f a) q °1).
  Defined.

  Opaque O_rec_dep.

   Lemma OT_decode_fun (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B) (Omono_f : Omono_sep A B sepB f) (a:A) 
     : ∀ a0 : A,
      OT_Cover A B sepB f Omono_f a (tr (t a0))
      → O nj (BuildTruncType _ ((tr o (t (f:=f)) ) a = (tr o t) a0)) .
   Proof.
     intros e q. cbn in q.
     apply (Oap (mod:=mod_nj) (x:=a) (y:=e) (tr o (t:A -> T f)) q).
   Defined.

   Lemma OT_decode_coh1 (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B) (Omono_f : Omono_sep A B sepB f) (a:A)
     : ∀ (x y : A) (p : f x = f y),
       transport (λ w, OT_Cover A B sepB f Omono_f a (tr w) → O nj (BuildTruncType _ ((tr o (t (f:=f)) ) a = tr w)))
                 (tp x y p)
                 (OT_decode_fun A B sepB f Omono_f a x) = OT_decode_fun A B sepB f Omono_f a y.
   Proof.
     intros x y p.
     pose (i := (O_rec n nj (BuildTruncType _ (x=y)) (Build_subuniverse_Type n nj (BuildTruncType _ (f x = f y)) (separated_nj_paths B sepB (f x) (f y))) (ap f))).
     pose (i' := equiv_inv _ (IsEquiv := Omono_f x y)).
     path_via (transport
                 (λ w : T f,
                        OT_Cover A B sepB f Omono_f a (tr w) → O nj (BuildTruncType _ (tr (t a) = tr w)))
                 (tp x y (i (i' p)))
                 ((λ (e : A) (q : OT_Cover A B sepB f Omono_f a (tr (t e))),
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
      refine (O_rec_dep _ (λ q, Build_subuniverse_Type n nj (BuildTruncType _ (transport PP (tp x y (i q)) xx uu = yy)) _) _).1
     end.
     intro q; destruct q.
     Opaque OT_Cover.
     cbn.
     unfold i.
     exact ((ap (λ U, transport (λ w : T f,
                                       OT_Cover A B sepB f Omono_f a (tr w) → O nj (BuildTruncType _ (tr (t a) = tr w)))
                                (tp x x U) (λ q : OT_Cover A B sepB f Omono_f a (tr (t x)),
                                                  Oap (λ x0 : A, tr (t x0)) q) u)
                (ap10 (O_rec_retr n nj (BuildTruncType _ (x=x))
                                  {| st := BuildTruncType _ (f x = f x);
                                     subu_struct := separated_nj_paths B sepB (f x) (f x) |}
                                  (ap f)) 1))
              @
              (ap10 (transport2 (λ w : T f,
                                       OT_Cover A B sepB f Omono_f a (tr w) → O nj (BuildTruncType _ (tr (t a) = tr w)))
                                (tp_1 x) (λ q : OT_Cover A B sepB f Omono_f a (tr (t x)), Oap (λ x0 : A, tr (t x0)) q)) u)).
   Defined.

   Lemma OT_decode_coh2 (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B) (Omono_f : Omono_sep A B sepB f) (a:A)
     : ∀ a0 : A,
   transport2
     (λ w : T f,
      OT_Cover A B sepB f Omono_f a (tr w)
      → O nj
          {|
          trunctype_type := tr (t a) = tr w;
          istrunc_trunctype_type := istrunc_paths
                                      (istrunc_truncation n.+1 (T f))
                                      (tr (t a)) (tr w) |}) 
     (tp_1 a0) (OT_decode_fun A B sepB f Omono_f a a0) =
   OT_decode_coh1 A B sepB f Omono_f a a0 a0 1.
   Proof.
     intro x; cbn.
     match goal with |[|- ?XX = _ ] => path_via (XX @ 1); apply moveR_Mp; symmetry end.
     unfold OT_decode_fun, OT_decode_coh1.
     rewrite concat_p_pp.

     match goal with
     |[|- _ @ path_forall ?ff = _] =>
      assert (bar := ff)
     end. cbn in bar.
     
     match goal with
     |[ bar : ?XX |- _] => clear bar; transparent assert (bar : XX)
     end.
     { apply apD10.
       etransitivity; [| exact (((transport2 (λ w : T f,
                                                    OT_Cover A B sepB f Omono_f a (tr w) → O nj (BuildTruncType _ (tr (t a) = tr w)))
                                             (tp_1 x) (λ q : OT_Cover A B sepB f Omono_f a (tr (t x)), Oap (λ x0 : A, tr (t x0)) q))))].
       match goal with
       |[|- transport ?PP (tp x x _) ?xx = _] =>
        apply (ap (λ U, transport PP (tp x x U) xx))
       end.
       apply eisretr. }
     
     match goal with
     |[|- _ @ path_forall ?ff = _] =>
      assert (r: bar = ff)
     end.
     {
       unfold bar; clear bar.
       match goal with
       |[|- ?ff = ?gg] =>
        apply path_forall;
          refine (O_rec_dep _ (λ u, Build_subuniverse_Type n nj (BuildTruncType _ (ff u = gg u)) _) _).1
       end.
       refine (subuniverse_paths _ _ (Build_subuniverse_Type n nj _ _) _ _).
       intro u; cbn.
       match goal with
       |[|- _ = pr1 _ ?xx] => transparent assert (r: (xx = °1))
       end.
       {
         pose (s:=eissect _ (IsEquiv := Omono_f x x) °1).
         pose (r:= ap (equiv_inv _ (IsEquiv := Omono_f x x)) (ap10 (O_rec_retr n nj (BuildTruncType _ (x = x))
                                                                               {| st := BuildTruncType _ (f x = f x);
                                                                                  subu_struct := separated_nj_paths B sepB (f x) (f x) |}
                                                                               (ap f)) 1)). cbn in r.
         exact (r^ @ s).
       }
       match goal with
       |[|- ?XX = pr1 ?YY ?xx] =>
        pose (p:= apD (λ U, pr1 YY U) r^)
       end.
       rewrite <- p; clear p.
       match goal with
       |[|- ?XX = transport _ _ (pr1 (O_rec_dep ?AA ?BB ?gg) ?xx)] =>
        pose ((O_rec_dep AA BB gg).2 1)
       end.
       rewrite p; clear p.
       cbn. rewrite transport_paths_Fl.
       rewrite apD10_pp. repeat rewrite concat_p_pp.
       apply whiskerR.
       match goal with |[|- _ = (ap ?ff ?rr)^ @ _] => rewrite <- (ap_V ff rr) end.
       match goal with
       |[|- _ = ap (λ x0:_, transport ?PP (tp x x (?gg x0)) ?ff ?oo) r^^ @ _]
        => rewrite (ap_compose gg (λ U, transport PP (tp x x U) ff oo)); cbn
       end.
       match goal with
       |[|- _ = ap ?f1 ?r1 @ ap ?f2 ?r2 ]
        => rewrite <- (ap_pp f1 r1 r2)
       end.
       match goal with
       |[|- apD10 (ap ?ff ?pp) _ = _]
        => pose (p := ap_apply_Fl pp ff (O_unit _ (BuildTruncType _ (a = x)) u)); unfold ap10 in p; rewrite <- p; clear p
       end.
       apply ap.
       rewrite inv_V.
       unfold r; clear r. rewrite ap_pp. rewrite ap_V.
       rewrite <- ap_compose.
       rewrite <- eisadj.
       rewrite_moveL_Vp_p.

       pose (p := apD (λ U:f x = f x -> f x = f x, ap U (ap10
                                                           (O_rec_retr n nj (BuildTruncType _ (x = x))
                                                                       {|
                                                                         st := BuildTruncType _ (f x = f x);
                                                                         subu_struct := separated_nj_paths B sepB (f x) (f x) |}
                                                                       (ap f)) 1)) (path_forall (λ u, (eisretr _ (IsEquiv := Omono_f x x) u)^))).
       cbn in p.
       rewrite <- p; clear p.
       rewrite ap_idmap.
       rewrite transport_paths_FlFr. cbn in *.
       pose (p := ap_ap_path_forall (λ u0 : f x = f x,
                                            (eisretr (IsEquiv := Omono_f x x)
                                                     (O_rec n nj (BuildTruncType _ (x = x))
                                                            {|
                                                              st := BuildTruncType _ (f x = f x);
                                                              subu_struct := separated_nj_paths B sepB (f x) (f x) |}
                                                            (ap f)) u0)^) (O_rec n nj (BuildTruncType _ (x = x))
                                                                                 {|
                                                                                   st := BuildTruncType _ (f x = f x);
                                                                                   subu_struct := separated_nj_paths B sepB (f x) (f x) |}
                                                                                 (ap f) (O_unit nj (BuildTruncType _ (x = x)) 1))).
       cbn in p. rewrite p; clear p.
       rewrite inv_V.
       repeat rewrite concat_pp_p. apply whiskerL.

       pose (p := ap_ap_path_forall (λ u0 : f x = f x,
                                            (eisretr (IsEquiv := Omono_f x x)
                                                     (O_rec n nj (BuildTruncType _ (x = x))
                                                            {|
                                                              st := BuildTruncType _ (f x = f x);
                                                              subu_struct := separated_nj_paths B sepB (f x) (f x) |}
                                                            (ap f)) u0)^) 1).
       cbn in p. rewrite p; clear p.
       rewrite concat_Vp. rewrite concat_p1. reflexivity. }
     destruct r.
     unfold bar. unfold path_forall; rewrite eissect.
     rewrite_moveR_Vp_p. rewrite concat_p1.
     rewrite ap_V. rewrite concat_Vp. rewrite concat_1p.
     reflexivity.
   Qed.
                                                                                                                
     Lemma OT_decode (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B) (Omono_f : Omono_sep A B sepB f) (a:A)
    : forall e:Trunc (n.+1) (T f), (OT_Cover A B sepB f Omono_f a) e -> O nj (BuildTruncType _ ((tr o t) a = e)).
  Proof.
    refine (Trunc_ind _ _).
    refine (T_ind _ _ _ _).
    - apply OT_decode_fun. 
    - apply OT_decode_coh1.      
    - apply OT_decode_coh2.
  Defined.
  
  Lemma OT_equiv (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B) (Omono_f : Omono_sep A B sepB f) (a:A)
    : (forall e, IsEquiv (OT_encode A B sepB f Omono_f a e)).
  Proof.
    intro e.
    refine (isequiv_adjointify _ _ _).
    - exact (OT_decode A B sepB f Omono_f a e).
    - revert e.
      refine (Trunc_ind _ _).
      refine (T_ind _ _ _ _).
      + intros e.
        unfold Sect.
        refine (O_rec_dep _ (λ x, Build_subuniverse_Type n nj (BuildTruncType _ (OT_encode A B sepB f Omono_f a (tr (t e))
                                                                                (OT_decode A B sepB f Omono_f a (tr (t e)) x) = x)) _) _).1.
        intro x; destruct x; cbn.
        unfold OT_decode_fun.
        match goal with
        |[|- OT_encode _ _ _ _ _ _ _
                         (Oap ?ff _) =_] =>
         etransitivity; [exact (ap (OT_encode A B sepB f Omono_f a (tr (t a))) (Oap_1 (mod := mod_nj) ff (x:=a))) |]
        end.
        apply Otransport_1.
      + intros x y p; cbn.
        pose (i := (O_rec n nj (BuildTruncType _ (x=y)) (Build_subuniverse_Type n nj (BuildTruncType _ (f x = f y)) (separated_nj_paths B sepB (f x) (f y))) (ap f))).
        pose (i' := equiv_inv _ (IsEquiv := Omono_f x y)).
        match goal with
        |[|- transport ?PP (?ff p) ?gg = _] =>
         path_via (transport PP (ff (i (i' p))) gg);
           [ refine (transport2 PP _ _); apply ap; symmetry; apply eisretr |]
        end.
        generalize (i' p).
        intro q.
        unfold OT_decode_fun, OT_decode_coh1.
        match goal with
        |[|- transport ?PP (?ff (i q)) ?gg = ?hh] =>
         refine ((O_rec_dep _ (λ q, Build_subuniverse_Type n nj (BuildTruncType _ (transport PP (ff (i q)) gg = hh)) _) _).1 q)
        end.
        { abstract (refine (istrunc_paths _ _ _)). }
        { abstract (
              match goal with
              |[|- IsSubu _ _ (BuildTruncType _ (?fooo = ?baar)) ] =>
               set (foo := fooo); set (bar := baar)
              end;
              match goal with
              |[ bar : ?XX |- _] =>
               assert (X: IsSubu n nj (BuildTruncType _ XX))
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
                       (O_rec n nj (BuildTruncType _ (x = x))
                              {|
                                st := BuildTruncType _ (f x = f x);
                                subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                              (ap f)
                              (O_unit
                                 (underlying_subu sheaf_def_and_thm.n sheaf_def_and_thm.mod_nj)
                                 (BuildTruncType _ (x = x)) 1))) = 1).
        { match goal with |[|- ?xx _ = 1] => path_via (xx 1) end.
          apply ap.
          refine (ap10 (O_rec_retr n nj (BuildTruncType _ (x=x)) {|st := BuildTruncType _ (f x = f x); subu_struct := separated_nj_paths B sepB (f x) (f x) |} (ap f)) 1).
          apply tp_1.
        }

        match goal with
        |[|- transport ?PP _ ?ff = _]
         => exact (transport2 PP r ff)
        end.
        
      + intro x.
        cbn.
        match goal with |[|- ?XX = _ ] => path_via (XX @ 1); apply moveR_Mp; symmetry end.
        match goal with
        |[|- (transport2 ?PP _ ?xx)^ @ _ = _ ] =>
         set (P := PP) in *; set (foo := xx) in *
        end.
        rewrite <- (transport2_V P (tp_1 x) foo).
        rewrite concat_p_pp.
        rewrite <- (transport2_p2p P (tp_1 x)^
                    (ap (tp x x)
                        (eisretr (IsEquiv := Omono_f x x)
                                 (O_rec n nj (BuildTruncType _ (x = x))
                                        {|
                                          st := BuildTruncType _ (f x = f x);
                                          subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                        (ap f)) 1)^)
                      foo).

        apply moveR_Mp. rewrite concat_p1.
        rewrite <- (transport2_V P ((tp_1 x)^ @
                                                ap (tp x x)
                                                (eisretr (IsEquiv := Omono_f x x)
                                                         (O_rec n nj (BuildTruncType _ (x = x))
                                                                {|
                                                                  st := BuildTruncType _ (f x = f x);
                                                                  subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                                                (ap f)) 1)^)
                                 foo).
        rewrite ap_V.
        rewrite inv_VV.

        pose (r := (eissect _ (IsEquiv := Omono_f x x) °1)^
                   @(ap (equiv_inv _ (IsEquiv := Omono_f x x)) (ap10 (O_rec_retr n nj (BuildTruncType _ (x = x))
                                                                                 {| st := BuildTruncType _ (f x = f x);
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
                                        (O_rec_retr n nj (BuildTruncType _ (x = x))
                                                    {|
                                                      st := BuildTruncType _ (f x = f x);
                                                      subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                                    (ap f)) 1) @ tp_1 x) foo).
        rewrite <- p; clear p.

        pose (p:= transport2_p2p P (ap (tp x x)
                                       (eisretr (IsEquiv := Omono_f x x)
                                                (O_rec n nj (BuildTruncType _ (x = x))
                                                       {|
                                                         st := BuildTruncType _ (f x = f x);
                                                         subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                                       (ap f)) 1) @ tp_1 x)
                                 (ap (tp x x)
                                     (ap10
                                        (O_rec_retr n nj (BuildTruncType _ (x = x))
                                                    {|
                                                      st := BuildTruncType _ (f x = f x);
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
                                    (O_rec n nj (BuildTruncType _ (x = x))
                                           {|
                                             st := BuildTruncType _ (f x = f x);
                                             subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                           (ap f)) 1 @
                                    (ap10
                                       (O_rec_retr n nj (BuildTruncType _ (x = x))
                                                   {|
                                                     st := BuildTruncType _ (f x = f x);
                                                     subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                                   (ap f)) 1)^)))
                  (y:= ((ap (tp x x)
                            (eisretr (IsEquiv := Omono_f x x)
                                     (O_rec n nj (BuildTruncType _ (x = x))
                                            {|
                                              st := BuildTruncType _ (f x = f x);
                                              subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                            (ap f)) 1) @ tp_1 x) @
                                                                 ((tp_1 x)^ @
                                                                              (ap (tp x x)
                                                                                  (ap10
                                                                                     (O_rec_retr n nj (BuildTruncType _ (x = x))
                                                                                                 {|
                                                                                                   st := BuildTruncType _ (f x = f x);
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
                                   (BuildTruncType _ (x = x)),
                                 transport P
                                           (tp x x
                                               (O_rec n nj (BuildTruncType _ (x = x))
                                                      {|
                                                        st := BuildTruncType _ (f x = f x);
                                                        subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                                      (ap f) x0)) foo) r).
        rewrite (ap_compose (λ x0, (tp x x
                                       (O_rec n nj (BuildTruncType _ (x = x))
                                              {|
                                                st := BuildTruncType _ (f x = f x);
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
        rewrite (ap_compose (O_rec n nj (BuildTruncType _ (x = x))
                                   {|
                                     st := BuildTruncType _ (f x = f x);
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
                                    (O_rec_retr n nj (BuildTruncType _ (x = x))
                                                {|
                                                  st := BuildTruncType _ (f x = f x);
                                                  subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                                (ap f)) 1)^) r).
        rewrite <- p; clear p.
        rewrite ap_idmap. cbn.
        rewrite transport_paths_FlFr.
        unfold r; clear r.
        rewrite_moveR_Vp_p.
        rewrite (ap_ap_path_forall (λ
                                      y : {|
                                            st := BuildTruncType _ (f x = f x);
                                            subu_struct := separated_nj_paths B sepB (f x) (f x) |},
                                          (eisretr (IsEquiv := Omono_f x x)
                                                   (O_rec n nj (BuildTruncType _ (x = x))
                                                          {|
                                                            st := BuildTruncType _ (f x = f x);
                                                            subu_struct := separated_nj_paths B sepB (f x) (f x) |}
                                                          (ap f)) y)^) 1).
        rewrite concat_Vp. rewrite concat_1p.
        rewrite_moveR_Vp_p.
        rewrite concat_pV.
        rewrite (ap_ap_path_forall (λ
                                      y : {|
                                            st := BuildTruncType _ (f x = f x);
                                            subu_struct := separated_nj_paths B sepB (f x) (f x) |},
                                          (eisretr (IsEquiv := Omono_f x x)
                                                   (O_rec n nj (BuildTruncType _ (x = x))
                                                          {|
                                                            st := BuildTruncType _ (f x = f x);
                                                            subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                                          (ap f)) y)^)
                                   (O_rec n nj (BuildTruncType _ (x = x))
                                          {|
                                            st := BuildTruncType _ (f x = f x);
                                            subu_struct := separated_nj_paths B sepB (f x) (f x) |} 
                                          (ap f) (O_unit nj (BuildTruncType _ (x = x)) 1))).
        rewrite concat_Vp. reflexivity.
    - unfold Sect.
      refine (O_rec_dep _ (λ x, Build_subuniverse_Type n nj (BuildTruncType _ (OT_decode A B sepB f Omono_f a e (OT_encode A B sepB f Omono_f a e x) =
                                                                  x
                                                            )) _) _).1.
      intro x; destruct x; cbn.
      unfold OT_encode.
      pose (r:= @Otransport_1); unfold Oidpath in r; rewrite r; clear r.
      unfold OT_decode_fun.
      rewrite Oap_1.
      reflexivity.
  Defined.
  
  Lemma OT (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B) (Omono_f : Omono_sep A B sepB f)
    : Omono _ _ (tr o t : A -> Trunc (n.+1) (T f)).
  Proof.
    intros a b.
    exact (isequiv_inverse _ (feq := OT_equiv A B sepB f Omono_f a (tr (t b)))).
  Defined.

  Lemma OT_Omono_sep (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B) (Omono_f : Omono_sep A B sepB f)
    : Omono_sep (BuildTruncType _ (Trunc (n.+1) (T f))) B sepB (Trunc_rec (T_rec B f (λ a b, idmap) (λ a, 1))).
  Proof.
    refine (Trunc_ind _ _).
    intro aa; refine trunc_forall.
    intro a. apply (@trunc_leq -1 (n.+1) tt _ _).
    intro a.
    refine (Trunc_ind _ _).
    intro bb. apply (@trunc_leq -1 (n.+1) tt _ _).    
    intro b.
    
    revert a b.
    
    refine (T_ind _ _ _ _).
    2: intros; apply path_ishprop.
    2: intro a; cbn. 
    
    intro a.
    refine (T_ind _ _ _ _).
    2: intros; apply path_ishprop.
    2: intro b; cbn.
    intro b.
    cbn.

    pose (Sh:= {|
        st := {|
              trunctype_type := f a = f b;
              istrunc_trunctype_type := istrunc_paths
                                          (istrunc_trunctype_type B) 
                                          (f a) (f b) |};
        subu_struct := separated_nj_paths B sepB (f a) (f b) |}).

    match goal with
    |[|- IsEquiv ?ff]
     => assert (X: (O_rec n nj (BuildTruncType _ (a = b)) Sh (ap f)) o (equiv_inv _ (IsEquiv := OT A B sepB f Omono_f a b)) = ff)
    end.
    { apply moveL_equiv_pM.
      match goal with
      |[|- ?FF = ?GG ] =>
       apply path_forall;
         refine (O_rec_dep _ (λ u, Build_subuniverse_Type n nj (BuildTruncType _ (FF u = GG u)) _) _).1
      end.
      intro u; cbn in *; destruct u; cbn.
      unfold function_lift.
      repeat rewrite (λ P Q f, ap10 (O_rec_retr n nj P Q f)).
      reflexivity. }
          
    destruct X.
    refine isequiv_compose.
    exact (Omono_f a b).

    apply path_ishprop. apply path_ishprop.
  Defined.

  Lemma Omono_sep_compose_equiv (A B C:TruncType (n.+1)) (sepB : separated B) (f: A -> B) (φ: C -> A) (Eφ: IsEquiv φ)
    : Omono_sep A B sepB f -> Omono_sep C B sepB (f o φ).
  Proof.
    intro H.
    intros x y.
    rewrite (path_forall (ap_compose φ f)).
    pose (function_lift_compose).
    (* unfold function_lift in p. *)
    rewrite <- (reflect_factoriality_post n nj {|
        trunctype_type := x = y;
        istrunc_trunctype_type := istrunc_paths (istrunc_trunctype_type C) x
                                    y |} _ {|
        st := {|
              trunctype_type := f (φ x) = f (φ y);
              istrunc_trunctype_type := istrunc_paths
                                          (istrunc_trunctype_type B)
                                          (f (φ x)) 
                                          (f (φ y)) |};
        subu_struct := separated_nj_paths B sepB (f (φ x)) (f (φ y)) |} (ap f) (ap φ)).
    refine (isequiv_compose).
    refine (function_lift_equiv _ _ _ _ _ _).
    exact (H (φ x) (φ y)).
  Qed.
  
  Definition TrTtelescope {X Y:TruncType (n.+1)} (f: X -> Y): diagram mappingtelescope_graph
    := tr_diagram _ (Ttelescope f) (n.+1).

  Definition TrTtelescope_to_Y {X Y:TruncType (n.+1)} (f: X -> Y)
    : forall i, TrTtelescope f i -> Y.
  Proof.
    intro i.
    refine (Trunc_rec _).
    exact (Ttelescope_aux f i).2.
  Defined.

  Definition T_trunc_T_coh_fun1 (X:Type) (Y:TruncType (n.+1)) (sepY: separated Y)
             (f:X -> Y)
    : Trunc (n.+1) (T (Trunc_rec (n:=n.+1) f)) -> Y.
  Proof.
    refine (Trunc_rec _). refine (T_rec _ _ _ _).
    refine (Trunc_rec _). exact f.
    intros a b. exact idmap.
    intro a; reflexivity.
  Defined.

  Require Import PathGroupoid_.

  Definition T_trunc_T_coh (X:Type) (Y:TruncType (n.+1)) (sepY: separated Y)
             (f:X -> Y)
    : (Trunc_rec (T_rec Y f (λ a b, idmap) (λ a, 1)) : Trunc (n.+1) (T f) -> Y)
      =
      (T_trunc_T_coh_fun1 X Y sepY f) o (T_trunc (n.+1) _ _ f).
  Proof.
    unfold T_trunc_T_coh_fun1, T_trunc, T_trunc_fun. cbn.
    apply path_forall; refine (Trunc_ind _ _). 
    refine (path_T _ _ _ _ _ _).
    - intro x; reflexivity.
    - intros a b p; cbn.
      refine (concat_1p _ @ _ @ (concat_p1 _)^).
      match goal with
      |[|- ap (λ x, ?G (?F x)) ?P = _] =>
       refine (ap_compose F G P @ _); cbn;
         refine (ap02 G (T_rec_beta_tp (Trunc n.+1 (T (Trunc_rec f))) (tr o t o tr) _ _ a b p) @ _)
      end.
      refine (_ @ (T_rec_beta_tp Y f (λ (a0 b0 : X) (x0 : f a0 = f b0), x0) (λ a0 : X, 1) _ _ _)^).
      refine ((ap_compose tr _ _)^ @ _); cbn.
      refine (T_rec_beta_tp _ _ _ _ _ _ _).
    - intro a; cbn. rewrite transport_paths_FlFr.
      rewrite concat_ap_Fpq, concat_ap_pFq.
      apply moveR_pV. rewrite !concat_pp_p.
      match goal with
      |[|- _ = _ @ (_ @ (whiskerR ?hh 1 @ _))] =>
       pose (rew:= whiskerR_p1 hh);
         rewrite concat_pp_p in rew;
         apply moveL_Vp in rew;
         rewrite rew; clear rew
      end.
      apply moveL_Vp. rewrite !concat_p_pp.
      match goal with
      |[|- (((((whiskerL 1 ?hh @ _)@_)@_)@_)@_)@_ = _]
       => pose (rew:= whiskerL_1p hh);
         rewrite concat_pp_p in rew;
         apply moveL_Vp in rew;
         rewrite rew; clear rew
      end. cbn.
      rewrite !ap_V. rewrite !concat_1p.
      rewrite <- (ap02_is_ap _ _(λ x : T f,
                                       T_rec Y f (λ (a0 b : X) (x0 : f a0 = f b), x0) (λ a0 : X, 1) x)).
      rewrite (T_rec_beta_tp_1 _ _ _ _ _).
      rewrite inv_pp. apply whiskerR.
      match goal with
      |[|- (((( ap (ap ?ff) ?pp)^@_)@_)@_)@_ = _]
       => rewrite <- (ap02_is_ap _ _ ff);
         rewrite ap02_compose; cbn
      end.
      rewrite (T_rec_beta_tp_1 _ _ _ _ _).
      rewrite inv_pp. rewrite concat_p1. rewrite !concat_pp_p.
      apply moveR_Vp.
      rewrite concat_V_pp. rewrite !concat_p1.
      rewrite ap02_pp. apply whiskerL.
      rewrite <- ap02_is_ap.
      apply moveR_Vp.
      match goal with
      |[|- _ = _ @ ap02 ?gg (ap02 ?ff ?pp)]
       => pose (rew := ap02_compose _ _ _ ff gg _ _ _ _ pp);
         rewrite concat_p_pp in rew;
         apply moveR_pM in rew         
      end.
      rewrite <- rew; clear rew; cbn.
      rewrite concat_p1. symmetry. rewrite (T_rec_beta_tp_1 Y (Trunc_rec f)
        (λ (a0 b : Trunc n.+1 X) (x0 : Trunc_rec f a0 = Trunc_rec f b), x0)
        (λ a0 : Trunc n.+1 X, 1)).
      apply concat_p1.
  Defined.
  
  Lemma Ttelescope_Omono_sep (A B:TruncType (n.+1)) (sepB : separated B) (f:A -> B) (Omono_f : Omono_sep A B sepB f)
    : forall i, Omono_sep _ _ sepB (TrTtelescope_to_Y f i).
  Proof.
    intro i; induction i.
    - unfold TrTtelescope_to_Y. cbn.
      pose (isequiv_tr (n.+1) A).
      assert (Trunc_rec (n:=n.+1) f = f o tr^-1).
      { apply path_forall; refine (Trunc_ind _ _).
        intro a. auto. }
      rewrite X.
      exact (Omono_sep_compose_equiv A B (BuildTruncType _ (Trunc (n.+1) A)) sepB f (tr^-1) _ Omono_f).
    - pose (e:= OT_Omono_sep _ _ sepB _ IHi).
      pose (H := T_trunc_T_coh _ _ sepB (pr2 (Ttelescope_aux f i))).
      unfold TrTtelescope_to_Y. simpl.
      rewrite H.
      vm_cast_no_check (Omono_sep_compose_equiv _ B _ sepB (T_trunc_T_coh_fun1 (pr1 (Ttelescope_aux f i)) B sepB
        (pr2 (Ttelescope_aux f i))) (T_trunc n.+1 (pr1 (Ttelescope_aux f i)) B (pr2 (Ttelescope_aux f i))) _ e).
  Defined.

End Tf_Omono_sep.