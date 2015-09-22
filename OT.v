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

  
Section OT.

  
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
       (transport2
          (λ w : T f,
                 OT_Cover A B sepB f Omono_f a (tr w)
                 → O nj
                     {|
                       trunctype_type := tr (t a) = tr w;
                       istrunc_trunctype_type := istrunc_paths
                                                   (istrunc_truncation n.+1 (T f))
                                                   (tr (t a)) (tr w) |}) 
          (tp_1 a0) (OT_decode_fun A B sepB f Omono_f a a0))^ @
                                                                OT_decode_coh1 A B sepB f Omono_f a a0 a0 1 = 1.
   Proof.
     intro x; cbn.
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
    2: intro a; cbn; apply path_ishprop.
    
    intro a.
    refine (T_ind _ _ _ _).
    2: intros; apply path_ishprop.
    2: intro b; cbn; apply path_ishprop.
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
  Defined.    
    
End OT.

Module Export OTid.

  Private Inductive OTid (A:TruncType (n.+1)) : Type :=
    | Ot : A -> (OTid A).

  Arguments Ot {A} a.

  Axiom Otp : forall {A:TruncType (n.+1)} (a b:A), O nj (BuildTruncType _ (a = b)) -> Ot a = Ot b.

  Axiom Otp_1 : forall {A:TruncType (n.+1)} (a:A), Otp a a °1 = 1.

  Definition OTid_ind (A:TruncType (n.+1)) (P : OTid A -> Type)
             (Ot' : forall a, P (Ot a))
             (Otp' : forall a b p, transport P (Otp a b p) (Ot' a) = Ot' b)
             (Otp_1' : forall a, (transport2 P (Otp_1 a) (Ot' a))^ @ Otp' a a °1 = 1)
    : forall w, P w
    := fun w => match w with
                |Ot a => fun _ => Ot' a
                end Otp_1'.

  Axiom OTid_ind_beta_Otp : forall (A:TruncType (n.+1)) (P : OTid A -> Type)
             (Ot' : forall a, P (Ot a))
             (Otp' : forall a b p, transport P (Otp a b p) (Ot' a) = Ot' b)
             (Otp_1' : forall a, (transport2 P (Otp_1 a) (Ot' a))^ @ Otp' a a °1 = 1)
             a b p,
     apD (OTid_ind A P Ot' Otp' Otp_1') (Otp a b p) = Otp' a b p.
        
End OTid.

Definition OTid_rec (A:TruncType (n.+1)) (P:Type)
           (Ot': A -> P)
           (Otp' : forall (a b:A) (p:O nj (BuildTruncType _ (a=b))), Ot' a = Ot' b)
           (Otp_1' : forall a, Otp' a a °1 = 1)
  : OTid A -> P.
Proof.
  refine (OTid_ind _ _ Ot' (fun a b p => transport_const _ _ @ Otp' a b p)  _).
  intro a.
  exact ((@concat_p_pp _ _ _ _ _ ((transport2 (λ _ : OTid A, P) (Otp_1 a) (Ot' a))^)  (transport_const (Otp a a °1) (Ot' a)) (Otp' a a °1))                                                                                                 @ whiskerR (moveR_Vp _ _ _ (transport2_const (A:=OTid A) (B:= P) (Otp_1 a) (Ot' a))) (Otp' a a °1)                                                                                                         @ concat_1p _                                                                                     @ (Otp_1' a)).
Defined.

Definition OT_rec_beta_Otp (A:TruncType (n.+1)) (P:Type)
           (Ot': A -> P)
           (Otp' : forall (a b:A) (p:O nj (BuildTruncType _ (a=b))), Ot' a = Ot' b)
           (Otp_1' : forall a, Otp' a a °1 = 1)
           a b p
  : ap (OTid_rec A P Ot' Otp' Otp_1') (Otp a b p) = Otp' a b p.
Proof.
Admitted.

Section OT_telescope.
  
  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  (* Local Definition n0 := sheaf_def_and_thm.n0. *)
  (* Local Definition n := sheaf_def_and_thm.n. *)
  (* Local Definition mod_nj := sheaf_def_and_thm.mod_nj. *)
  (* Local Definition nj := sheaf_def_and_thm.nj. *)
  (* Local Definition j_is_nj := sheaf_def_and_thm.j_is_nj. *)
  (* Local Definition j_is_nj_unit := sheaf_def_and_thm.j_is_nj_unit. *)
  (* Local Definition islex_mod_nj := sheaf_def_and_thm.islex_mod_nj. *)
  (* Local Definition islex_nj := sheaf_def_and_thm.islex_nj. *)
  (* Local Definition lex_compat := sheaf_def_and_thm.lex_compat. *)

    
  Definition OTtelescope_aux (X:TruncType (n.+1)) (m: nat)
  : TruncType (n.+1).
    induction m as [|m U].
    - exact X. 
    - exact (BuildTruncType _ (Trunc (n.+1) (OTid U))).
  Defined.

  Definition OTtelescope (X:TruncType (n.+1)) 
  : diagram mappingtelescope_graph.
    refine (Build_diagram _ _ _).
    - intros m. exact (OTtelescope_aux X m).
    - intros n m q; destruct q; simpl.
      intro x. apply tr. apply Ot. exact x.
  Defined.

  Lemma fooo (A B:TruncType (n.+1)) (f:A -> B) (H: forall x y:A, O nj (BuildTruncType _ (x=y)) <~> (f x = f y))
        (H1: forall x:A, H x x °1 = 1) (H1': forall x:A, (H x x)^-1 1 = °1)
    : OTid A <~>  (T f).
  Proof.
    refine (equiv_adjointify _ _ _ _).
    - refine (OTid_rec _ _ _ _ _); cbn.
      + intro x. apply (@t A B f x). 
      + intros a b p. cbn.
        exact (tp a b (H a b p)).
      + intro a. cbn.
        pose (Hretr1 := eisretr (H a a) 1).
        match goal with |[|- ?XX _ = _] => path_via (XX 1) end.
        apply ap; apply H1.
        apply tp_1.
    - refine (T_rec _ _ _ _); cbn.
      apply Ot.
      intros a b p.
      apply (Otp a b ((H a b)^-1 p)).
      intro a; cbn.
      match goal with |[|- ?XX _ = _] => path_via (XX °1) end.
      apply ap; apply H1'.
      apply Otp_1.
    - unfold Sect.
      refine (T_ind _ _ _ _).
      intro a; reflexivity.
      intros a b p; cbn.
      rewrite transport_paths_FlFr.
      rewrite ap_idmap. cbn.
      rewrite_moveR_Vp_p.
      rewrite concat_p1, concat_1p.
      
      admit.
      admit.
    - unfold Sect.
      refine (OTid_ind _ _ _ _ _); cbn.
      intro a; reflexivity.
      intros a b p; cbn.
      rewrite transport_paths_FlFr.
      rewrite ap_idmap. cbn.
      
                 
      

      
End OT_telescope.