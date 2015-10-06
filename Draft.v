(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Import Limit.
Require Import T T_telescope OT OT_Tf.
Require Import PathGroupoid_ Forall_ Equivalences_ epi_mono reflective_subuniverse modalities OPaths.
Require Import sheaf_base_case.
Require Import sheaf_def_and_thm.
Require Import sheaf_induction.



Set Universe Polymorphism.
Global Set Primitive Projections. 

Local Open Scope path_scope.
Local Open Scope type_scope.

Section Foo.

  Lemma foo (E S:TruncType (n.+1)) (sepS: separated S) (f:E -> S)
        (oT := Trunc (n.+1) (OTid E)) 
  : oT -> S.
  Proof.
    refine (Trunc_rec _).
    refine (OTid_rec _ _ _ _ _).
    exact f.
    intros a b. refine (O_rec n nj _ (Build_subuniverse_Type n nj _ (separated_nj_paths S sepS (f a) (f b))) _).
    exact (ap f).
    intro a; cbn.
    exact (ap10 (O_rec_retr n nj
                            {|
                              trunctype_type := a = a;
                              istrunc_trunctype_type := istrunc_paths a a |}
                            {|
                              st := {|
                                     trunctype_type := f a = f a;
                                     istrunc_trunctype_type := istrunc_paths (f a) (f a) |};
                              subu_struct := separated_nj_paths S sepS (f a) (f a) |} 
                            (ap f)) 1).
  Defined.

  Lemma bar (E S:TruncType (n.+1)) (sepS: separated S) (f g:E -> S)
        (oT := Trunc (n.+1) (OTid E)) (g1: oT -> S)
        (c: g1 o (tr o (@Ot E)) = g)
        (f1 := foo E S sepS f)
        (eq: f = g)
    : f1 = g1.
  Proof.
    unfold f1, foo. clear f1.
    apply path_forall.
    refine (Trunc_ind _ _); cbn.
    refine (path_OT _ _ _ _ _ _ _); cbn.
    intro x.
    path_via (g x). exact (ap10 eq x).
    exact (ap10 c^ x).
    intros a b; cbn.
    match  goal with
    |[|- forall p:?XX, ?P1 @ ap ?f1 (?P2 p) = ap ?f2 (?P3 p) @ ?P4] => 
     pose (shf:= λ p:XX, Build_subuniverse_Type n nj _ (subuniverse_paths n nj
                                                                    (Build_subuniverse_Type n nj _ (separated_nj_paths S sepS (f a) (g1 (tr (Ot b)))))
                                                                    (P1 @ ap f1 (P2 p)) (ap f2 (P3 p) @ P4)))
    end.

    refine (O_rec_dep _ shf _).1.
    unfold shf; clear shf; cbn.
    intro p. destruct p.
    refine (_ @ ((OT_rec_beta_Otp E S f _ _ a a °1)^ @@ 1)).

    match goal with
    |[|- _ = O_rec n nj ?PP ?QQ ?ff _ @ _] =>
     refine (_ @ ((ap10 (O_rec_retr n nj PP QQ ff) 1)^ @@ 1))
    end.
    cbn.
    match goal with |[|- _ = 1 @ ?xx] => path_via (xx @ 1) end.
    apply whiskerL.
    
    match goal with |[|- ap ?ff _ = _] => path_via (ap (x:= Ot a) ff 1) end.
    apply ap.
    apply Otp_1.

    refine (concat_p1 _ @ _). symmetry; apply concat_1p.
    
    Opaque O_rec_dep.
    intro a; cbn.
    match goal with |[|- (pr1 ?ff) °1 = _ ]
                     => pose (pp := pr2 ff 1)
    end.
    cbn in pp. rewrite pp; clear pp.
    rewrite transport_paths_FlFr. cbn.
    rewrite (concat_p1 (ap (ap (λ x : OTid E, g1 (tr x))) (Otp_1 a))).
    rewrite ap_V. rewrite inv_V.
    rewrite concat_ap_pFq.
    match goal with
    |[|- (?P1 @ ?P2) @ ?P3 = ?P4 @ _ ] 
     => rewrite (concat_pp_p (p:=P1))
    end.
    apply whiskerL. rewrite concat_concat2.
    cbn.
    rewrite concat_ap_Fpq. unfold whiskerR.
    rewrite ap_V.

    match goal with
    |[|- ?P1 @@ 1 = ?P2 @@ 1] => assert (rr: P1 = P2)
    end.
    2: destruct rr; reflexivity.
    rewrite <- inv_pp.
    apply ap.
    match goal with
    |[|- _ = ap (ap ?ff) ?rr] => 
     rewrite <- (ap02_is_ap _ _ ff _ _ _ _ rr)
    end.
    rewrite OT_rec_beta_Otp_1.
    reflexivity.
  Defined.

  Lemma foobar (E S:TruncType (n.+1)) (sepS: separated S) (f g:E -> S)
        (oT := Trunc (n.+1) (OTid E)) (g1: oT -> S)
        (c: g1 o (tr o (@Ot E)) = g)
        (f1 := foo E S sepS f)
        (eq: f = g)
    : ap (λ u, u o (tr o (@Ot E))) (bar E S sepS f g g1 c eq) @ c @ eq^ = 1.
  Proof.
    apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
    apply path_forall; intro x. simpl.
    pose (p:=@ap10_ap_precompose). unfold ap10 in p.
    cbn in p.
    do 2 rewrite apD10_pp.
    rewrite (p _ _ _ (λ x0, (tr (Ot x0))) _ _ (bar E S sepS f g g1 c eq) x).
    unfold bar. unfold path_forall; rewrite eisretr.
    simpl. rewrite path_OT_compute.
    unfold ap10.
    do 2 rewrite apD10_V.
    apply moveR_pV.
    rewrite concat_pV_p.
    rewrite concat_1p. reflexivity.
  Defined.
    


    
End Foo.