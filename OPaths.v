(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Export MyTacs.
Require Import HoTT.
Require Export Utf8_core.
Require Import Forall_.
Require Import reflective_subuniverse modalities.

Set Universe Polymorphism.
Global Set Primitive Projections.

Delimit Scope Opath_scope with Opath.
Open Scope Opath_scope.

Section OPath.
Local Open Scope path_scope.

Context `{ua: Univalence}.
Context `{fs: Funext}.
Context `{n:trunc_index}.
Context `{mod : Modality n}.
Let subU := underlying_subu n mod.

Let BTT (A:Type) {TrA : IsTrunc n A} := @BuildTruncType n A TrA.

Definition Oidpath (A:TruncType (n.+1)) (x:A)
  : O subU (BTT (x=x))
  := O_unit subU _ 1.

Global Arguments Oidpath {A x}, [A] x.
Notation "°1" := Oidpath : Opath_scope.

Definition Oconcat (A:TruncType (n.+1)) (x y z:A) 
  : O subU (BTT (x = y)) -> O subU (BTT (y = z)) -> O subU (BTT (x = z)).
Proof.
  intros p q.
  revert q; apply O_rec; intro q.
  revert p; apply O_rec; intro p.
  exact (O_unit subU _ (p @ q)).
Defined.

Global Arguments Oconcat {A x y z} p q.
Notation "p °@ q" := (Oconcat p q) (at level 20) : Opath_scope.

Definition Oinverse (A: TruncType (n.+1)) (x y:A)
  : O subU (BTT (x=y)) -> O subU (BTT (y = x))
  := function_lift _ _ _ _ inverse.
Global Arguments Oinverse {A x y} p.
Notation "p '°^'" := (Oinverse p) (at level 3, format "p '°^'") : Opath_scope.

Local Open Scope Opath_scope.

Definition Oconcat_p1 {A:TruncType (n.+1)} {x y:A} (p: O subU (BTT (x=y))) 
  : p °@ °1 = p.
Proof.
  revert p.
  simple refine (O_rec_dep _ (λ p, Build_subuniverse_Type n subU (BTT (p °@ °1 = p)) _) _).1.
  simple refine (subuniverse_paths _ _ _ _ _).
  intro p.
  unfold Oconcat, Oidpath.
  repeat rewrite (λ P Q f, ap10 (O_rec_retr n subU P Q f)).
  cbn. apply ap. apply concat_p1.
Defined.

Definition Oconcat_1p {A:TruncType (n.+1)} {x y:A} (p: O subU (BTT (x=y))) 
  : °1 °@ p = p.
Proof.
  revert p.
  simple refine (O_rec_dep _ (λ p, Build_subuniverse_Type n subU (BTT (°1 °@ p = p)) _) _).1.
  simple refine (subuniverse_paths _ _ _ _ _).
  intro p.
  unfold Oconcat, Oidpath.
  repeat rewrite (λ P Q f, ap10 (O_rec_retr n subU P Q f)).
  cbn. apply ap. apply concat_1p.
Defined.

Definition Oconcat_p_pp {A:TruncType (n.+1)} {x y z t:A} (p: O subU (BTT (x=y))) (q: O subU (BTT (y=z))) (r: O subU (BTT (z=t)))
  : p °@ (q °@ r) = (p °@ q) °@ r.
Proof.
  revert p.
  simple refine (O_rec_dep _ (λ p, Build_subuniverse_Type n subU (BTT (p °@ _ = (p °@ _) °@ _)) _) _).1.
  simple refine (subuniverse_paths _ _ _ _ _). intro p.
  revert q.
  simple refine (O_rec_dep _ (λ q, Build_subuniverse_Type n subU (BTT (_ °@ (q °@ _) = (_ °@ q) °@ _)) _) _).1.
  intro q.
  revert r.
  simple refine (O_rec_dep _ (λ r, Build_subuniverse_Type n subU (BTT (_ °@ (_ °@ r) = (_ °@ _) °@ r)) _) _).1.
  intro r. cbn.
  unfold Oconcat, Oidpath, Oinverse, function_lift.
  cbn.
  repeat rewrite (λ P Q f, ap10 (O_rec_retr n subU P Q f)).
  apply ap. apply concat_p_pp.
Defined.

Definition Oconcat_pp_p {A:TruncType (n.+1)} {x y z t:A} (p: O subU (BTT (x=y))) (q: O subU (BTT (y=z))) (r: O subU (BTT (z=t)))
  : (p °@ q) °@ r = p °@ (q °@ r).
Proof.
  revert p.
  simple refine (O_rec_dep _ (λ p, Build_subuniverse_Type n subU (BTT ((p °@ _) °@ _ = p °@ (_ °@ _))) _) _).1.
  simple refine (subuniverse_paths _ _ _ _ _). intro p.
  revert q.
  simple refine (O_rec_dep _ (λ q, Build_subuniverse_Type n subU (BTT ((_ °@ q) °@ _ = _ °@ (q °@ _))) _) _).1.
  intro q.
  revert r.
  simple refine (O_rec_dep _ (λ r, Build_subuniverse_Type n subU (BTT ((_ °@ _) °@ r = _ °@ (_ °@ r))) _) _).1.
  intro r. cbn.
  unfold Oconcat, Oidpath, Oinverse, function_lift.
  cbn.
  repeat rewrite (λ P Q f, ap10 (O_rec_retr n subU P Q f)).
  apply ap. apply concat_pp_p.
Defined.

Definition Oconcat_pV {A:TruncType (n.+1)} {x y:A} (p: O subU (BTT (x=y)))
  : p °@ p °^ = °1.
Proof.
  revert p.
  simple refine (O_rec_dep _ (λ p, Build_subuniverse_Type n subU (BTT (p °@ p °^ = °1)) _) _).1.
  simple refine (subuniverse_paths _ _ _ _ _).
  intro p.
  unfold Oconcat, Oidpath, Oinverse, function_lift.
  cbn.
  repeat rewrite (λ P Q f, ap10 (O_rec_retr n subU P Q f)).
  apply ap. apply concat_pV.
Defined.

Definition Oconcat_Vp {A:TruncType (n.+1)} {x y:A} (p: O subU (BTT (x=y)))
  : p°^ °@ p = °1.
Proof.
  revert p.
  simple refine (O_rec_dep _ (λ p, Build_subuniverse_Type n subU (BTT (p °^ °@ p = °1)) _) _).1.
  simple refine (subuniverse_paths _ _ _ _ _).
  intro p.
  unfold Oconcat, Oidpath, Oinverse, function_lift.
  cbn.
  repeat rewrite (λ P Q f, ap10 (O_rec_retr n subU P Q f)).
  apply ap. apply concat_Vp.
Defined.

Definition Oinv_pp {A:TruncType (n.+1)} {x y z:A} (p: O subU (BTT (x=y))) (q: O subU (BTT (y=z)))
  : (p °@ q)°^ = q°^ °@ p°^.
Proof.
  revert p.
  simple refine (O_rec_dep _ (λ p, Build_subuniverse_Type n subU (BTT ((p °@ q)°^ = q°^ °@ p°^)) _) _).1.
  simple refine (subuniverse_paths _ _ _ _ _).
  intro p. cbn.
  revert q.
  simple refine (O_rec_dep _ (λ q, Build_subuniverse_Type n subU (BTT ((_ °@ q)°^ = q°^ °@ _)) _) _).1.
  simple refine (subuniverse_paths _ _ _ _ _).
  intro q.
  cbn.
  unfold Oconcat, Oidpath, Oinverse, function_lift.
  cbn.
  repeat rewrite (λ P Q f, ap10 (O_rec_retr n subU P Q f)).
  apply ap. apply inv_pp.
Defined.

Definition Oinv_V {A:TruncType (n.+1)} {x y:A} (p: O subU (BTT (x=y)))
  : p°^°^ = p.
Proof.
  revert p.
  simple refine (O_rec_dep _ (λ p, Build_subuniverse_Type n subU (BTT ((p°^)°^ = p)) _) _).1.
  simple refine (subuniverse_paths _ _ _ _ _).
  intro p.
  cbn.
  unfold Oconcat, Oidpath, Oinverse, function_lift.
  cbn.
  repeat rewrite (λ P Q f, ap10 (O_rec_retr n subU P Q f)).
  apply ap. apply inv_V.
Defined.

Definition Oap {A B:TruncType (n.+1)} (f: A -> B) {x y:A} (p: O subU (BTT (x=y)))
  : O subU (BTT (f x = f y))
  := function_lift n subU (BTT (x=y)) (BTT (f x = f y)) (ap f) p.

Definition Oap_1 {A B:TruncType (n.+1)} (f: A -> B) {x:A}
  : Oap (x:=x) (y:=x) f °1 = °1.
Proof.
  unfold Oap, Oidpath, function_lift. cbn.
  apply (λ P Q f, ap10 (O_rec_retr n subU P Q f)). 
Defined.

Definition Oap_pp {A B:TruncType (n.+1)} (f: A -> B) {x y z:A} (p: O subU (BTT (x=y))) (q: O subU (BTT (y=z)))
  : Oap f (p °@ q) = (Oap f p) °@ (Oap f q).
Proof.
  revert p.
  simple refine (O_rec_dep _ (λ p, Build_subuniverse_Type n subU (BTT (Oap f (p °@ q) = Oap f p °@ Oap f q)) _) _).1.
  simple refine (subuniverse_paths _ _ _ _ _).
  intro p. cbn.
  revert q.
  simple refine (O_rec_dep _ (λ q, Build_subuniverse_Type n subU (BTT (Oap f (_ °@ q) = _ °@  Oap f q)) _) _).1.
  simple refine (subuniverse_paths _ _ _ _ _).
  intro q.
  cbn.
  unfold Oconcat, Oidpath, Oinverse, Oap, function_lift.
  repeat rewrite (λ P Q f, ap10 (O_rec_retr n subU P Q f)).
  apply ap. apply ap_pp.
Defined.

Definition Oap_V {A B:TruncType (n.+1)} (f: A -> B) {x y:A} (p: O subU (BTT (x=y)))
  : Oap f (p°^) = (Oap f p)°^.
Proof.
  revert p.
  simple refine (O_rec_dep _ (λ p, Build_subuniverse_Type n subU (BTT (Oap f p°^ = (Oap f p)°^)) _) _).1.
  simple refine (subuniverse_paths _ _ _ _ _).
  intro p. cbn.
  unfold Oconcat, Oidpath, Oinverse, Oap, function_lift.
  cbn.
  repeat rewrite (λ P Q f, ap10 (O_rec_retr n subU P Q f)).
  apply ap. apply ap_V.
Defined.

Definition Oap_idmap {A:TruncType (n.+1)} {x y:A} (p: O subU (BTT (x=y)))
  : Oap idmap p = p.
Proof.
  unfold Oap.
  path_via (function_lift n subU (BTT (x = y)) (BTT (x = y)) idmap p).
  apply (ap (λ U, function_lift n subU (BTT (x = y)) (BTT (x = y)) U p)).
  apply (path_forall _ _ (ap_idmap)).
  apply (ap10 (function_lift_idmap _ _ _)).
Defined.

Lemma Oap_idmap_Oap_1 {A:TruncType (n.+1)} (x:A) 
  : Oap_idmap (A:=A) (x:=x) °1 = Oap_1 idmap.
Proof.
  unfold Oap_idmap, Oap_1.
  unfold function_lift_idmap.
  rewrite <- (apD (λ U, ap10
     (O_rec_retr n subU
        (default_TruncType n (x = x)
           (istrunc_paths (istrunc_trunctype_type A) x x))
        (O subU (BTT (x = x)))
        (λ x0 : x = x, O_unit subU (BTT (x = x)) (U x0))) 1) (path_forall (ap idmap) idmap ap_idmap)^).
  
  rewrite transport_paths_FlFr. cbn. rewrite ap_V. rewrite inv_V.
  rewrite !concat_pp_p. apply whiskerL.
  unfold Oidpath. simple refine ((ap10_O_retr_sect n subU (BTT (x = x)) (O subU (BTT (x = x))) idmap 1) @ _).
  simple refine ((concat_p1 _)^ @ _). apply whiskerL.
  rewrite (ap_compose (λ x0, x0 1) (λ x0, (O_unit subU (BTT (x = x))) x0)).
  rewrite ap_apply_l. rewrite ap10_V.
  rewrite ap10_path_forall. reflexivity.
Qed.

Definition Oap_compose {A B C:TruncType (n.+1)} (f: A -> B) (g: B -> C) {x y:A} (p: O subU (BTT (x=y)))
  : Oap (g o f) p = Oap g (Oap f p).
Proof.
  revert p.
  simple refine (O_rec_dep _ (λ p, Build_subuniverse_Type n subU (BTT (Oap (g o f) p = Oap g (Oap f p))) _) _).1.
  simple refine (subuniverse_paths _ _ _ _ _).
  intro p. cbn.
  unfold Oconcat, Oidpath, Oinverse, Oap, function_lift.
  cbn.
  repeat rewrite (λ P Q f, ap10 (O_rec_retr n subU P Q f)).
  apply ap. apply ap_compose.
Defined.

Definition Otransport {A:TruncType (n.+1)} (P:A -> subuniverse_Type subU) {x y:A}
  : O subU (BTT (x=y)) -> P x -> P y.
Proof.
  intros p q. revert p. apply O_rec.
  exact (λ p, transport P p q).
Defined.

Definition Otransport_1 {A:TruncType (n.+1)} (P:A -> subuniverse_Type subU) {x:A} (q:P x)
  : Otransport P °1 q = q.
Proof.
  apply (λ P Q f, ap10 (O_rec_retr _ subU P Q f)).
Defined.

Definition Otransport2 {A:TruncType (n.+1)} (P:A -> subuniverse_Type subU) {x y:A} (p q:O subU (BTT (x=y)))
           (r:O subU (BTT (p=q)))
  : forall z:P x, Otransport P p z = Otransport P q z.
Proof.
  intro z.
  simple refine (O_rec _ subU (BTT (p=q))
                (Build_subuniverse_Type n subU (BTT (Otransport P p z = Otransport P q z)) _) _ r).
  simple refine (subuniverse_paths _ _ _ _ _).
  intro r'; destruct r'; reflexivity.
Defined.
  
End OPath.

Notation "°1" := Oidpath : Opath_scope.
Notation "p °@ q" := (Oconcat p q) (at level 20) : Opath_scope.
Notation "p '°^'" := (Oinverse p) (at level 3, format "p '°^'") : Opath_scope.
