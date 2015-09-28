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

Lemma path_OT (A:(n.+1)-Type) (B:Type)
      (α β :OTid A -> B)
      (eq1: α o Ot == β o Ot)
      (eq2: forall a b p, eq1 a @ ap β (Otp a b p) = ap α (Otp a b p) @ eq1 b)
      (eq3: forall a,  (eq2 a a °1)
                      = transport (λ U, eq1 a @ ap β U = ap α U @ eq1 a) (Otp_1 a)^ (concat_p1 (eq1 a) @ (concat_1p (eq1 a))^))
  : α == β.
Proof.
  (* We refer to the general case in R.v *)
Admitted.
  

Section OT_telescope.
  
  Context `{ua: Univalence}.
  Context `{fs: Funext}.

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

    
End OT_telescope.

