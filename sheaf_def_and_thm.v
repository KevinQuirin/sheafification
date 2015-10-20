(* -*- coq-prog-args: ("-emacs" "-indices-matter" "-type-in-type") -*- *)

Require Import HoTT HoTT.hit.Truncations Connectedness.
Require Export Utf8_core.
Require Import Forall_.
Require Import epi_mono reflective_subuniverse modalities.
Require Import sheaf_base_case.

Set Universe Polymorphism.
Global Set Primitive Projections.

Local Open Scope path_scope.
(* Local Open Scope equiv_scope. *)
Local Open Scope type_scope.

(* Readability *)
Arguments trunc_arrow {H} {A} {B} {n} H0: simpl never.
Arguments trunc_sigma {A} {P} {n} H H0: simpl never.
Arguments istrunc_paths {A} {n} H x y: simpl never.

Section Definitions.


  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  Parameter n0 : trunc_index.

  Definition n := trunc_S n0.

  Parameter mod_nj : Modality n.

  Definition nj := underlying_subu n mod_nj.

  (* The following two parameters are the hypothesis 26 *)
  Parameter j_is_nj : forall P, trunctype_type (j P) = trunctype_type (@st _ _ (O nj (@BuildTruncType _ P (@trunc_leq -1 n tt _ _)))).

  Parameter j_is_nj_unit : forall P x ,
                          transport idmap (j_is_nj P) (Oj_unit P x) = O_unit nj (@BuildTruncType _ P (@trunc_leq -1 n tt _ _)) x.
  
  Parameter islex_mod_nj : IsLex mod_nj.

  Definition islex_nj := islex_to_hfibers_preservation mod_nj islex_mod_nj.
  Definition lex_compat := islex_to_hfibers_preservation_compat mod_nj islex_mod_nj.

  Definition J :=
    (* pr1 (nchar_to_sub (pr1 o Oj)). *)
  {P : hProp & j P}.

  Definition Oj_J_Contr (χ:J) : Contr (j χ.1).
    apply BuildContr with (center := χ.2).
    intro. apply path_ishprop.
  Defined.
  
  Definition nJ := {T : TruncType n & (O nj T)}.

  (* Definition 18, for subobjects seen as a characteristic function [χ : E -> TruncType n], or as n-fibered functions *)
  Definition closed {E} (χ : E -> TruncType n) := forall e, IsEquiv (nj.(O_unit) (χ e)).
  
  (* Definition closed' E A (m : {f : A -> E & forall b:E, IsTrunc n (hfiber f b)}) := closed (nsub_to_char n (A;m)). *)

  Definition cloture {E} (χ : E -> TruncType n) : E -> TruncType n := nj.(O) o χ.
  
  (* Definition cloture' E A (m : {f : A -> E & forall b:E, IsTrunc n (hfiber f b)}) := *)
    (* nchar_to_sub (cloture (nsub_to_char n (A;m))). *)

  (* Proofs that the the closure of a subobject is closed *)
  Definition cloture_is_closed {E :Type} (χ : E -> TruncType n) : closed (cloture χ).
    intro. apply O_modal_equiv. exact fs.
  Defined.

  (* Lemma cloture_is_closed' (A:Type) (E:Type) (m : {f : A -> E & forall e:E, IsTrunc n (hfiber f e)}) : closed' (pr2 (cloture' m)). *)
  (*   unfold closed', cloture'.  *)
  (*   rewrite (eta_sigma (nchar_to_sub (cloture (nsub_to_char n (A; m))))). *)
  (*   pose (f := cloture_is_closed (nsub_to_char n (A; m))).  *)
  (*   rewrite <- (@nsub_eq_char_retr ua fs n _ (cloture (nsub_to_char n (A; m)))) in f. *)
  (*   exact f. *)
  (* Defined. *)

  Definition incl_Aeq_Eeq {E:Type} (χ:E -> TruncType n) (x:{e:E & χ e})
  : {e':{e:E & χ e} & x.1 = e'.1} -> {e':E & x.1 = e'}
    := λ X, (X.1.1;X.2).

  Definition eq_dense_1 {E:Type} (χ:E -> TruncType n) (x:{e:E & χ e})
  : {e':{e:E & χ e} & x.1 = e'.1} <~> (χ x.1).
    exists (λ X:(∃ e' : ∃ e : E, χ e, x.1 = e'.1), (transport (λ u, χ u) (X.2)^ X.1.2)).
    apply isequiv_adjointify with (g := (λ X, ((x.1;X);1)) : ((χ x.1) -> {e':{e:E & χ e} & x.1 = e'.1})).
    - intro u. reflexivity.
    - intro u. destruct u as [[e' e] p]. simpl in *. destruct p. simpl. reflexivity.
  Defined.

  Definition is_dense_eq {E:Type} (char : E -> TruncType n) := forall e:E, ({e':E & e=e'}) = O nj (char e).

  Definition is_dense_diag {E:Type} (char : E -> TruncType n) (dense_eq : is_dense_eq char)
    := forall x:{e:E & char e}, forall u:{e':{e:E & char e} & x.1 = e'.1}, (equiv_path _ _ (dense_eq x.1)) o (incl_Aeq_Eeq char x) = (O_unit nj _) o ((eq_dense_1 char x)).

(* For A a subobject of E, and x:A, this diagram commute : *)
(*                                                         *)   
(*   {e':A & x.1 = e'.1} === (χ x.1).1                     *)
(*          |                    |                         *)
(*        ι |                    | η                       *)
(*          |                    |                         *)
(*          v                    v                         *)
(*    {e':E & x.1 = e'}  === (O nj (χ x.1)).1.1            *)                                      
    
  (* Definition 19 *)
  Record EnJ (E:Type) :=
    {
      char :> E -> TruncType n ;
      dense_eq : forall e:E, ({e':E & e=e'}) = (O nj (char e))                              
    }.

  Arguments char {E} χ e: rename.
  Arguments dense_eq {E} χ e: rename.
  
  Definition dense_diag {E:Type} (char : EnJ E)
  : forall x:{e:E & char e}, forall u:{e':{e:E & char e} & x.1 = e'.1}, (equiv_path _ _ (dense_eq char x.1)) o (incl_Aeq_Eeq char x) = (O_unit nj _) o ((eq_dense_1 char x)).
    intros x u.
    apply path_forall; intro z.
    assert (Contr (O nj (char x.1))).
    { rewrite <- dense_eq. exists (x.1;1). intros [y q]. destruct q. reflexivity. }
    apply (path_contr).
  Qed.

  Definition witness_is_eta {E:Type} (χ:EnJ E) (x:{e:E & χ e})
  : transport idmap (dense_eq χ x .1) (x .1; 1) = O_unit nj (χ x .1) x.2
    := ap10 (dense_diag χ x (x;1)) (x;1).

  Definition EnJ_is_nJ {E:Type} (χ : EnJ E)
  : forall e:E, (O nj (χ e))
    := λ e, transport (λ T, T) (dense_eq χ e) (e;idpath).

  Definition dense_eta_equal {E:Type} (χ : EnJ E) (x:E) : forall (v w:χ x), O_unit nj (χ x) v = O_unit nj (χ x) w.
    intros v w.
    assert (forall (a b:(∃ e' : E, x = e')), a=b).
    intros a b.
    destruct a as [a p], b as [b q]. simpl.
    apply @path_sigma' with (p := p^@q).
    destruct p. destruct q. simpl. reflexivity.
    rewrite (dense_eq χ) in X; apply X.
  Defined.

  (* Definition 20, for (-1)-subobjects *)
  Definition E_to_χmono_map (T:TruncType (trunc_S n)) {E} (χ : E -> J) (f : E -> T) : 
    {x:E & (χ x).1} -> T := f o pr1.

  Arguments E_to_χmono_map T {E} χ f _.
  
  (* Definition 20, for n-subobjects *)
  Definition E_to_χ_map (T:TruncType (trunc_S n)) {E} (χ : EnJ E) (f : E -> T) : 
    {x:E & χ x} -> T := f o pr1.

  (* Definition 21 *)
  Definition separated T :=  ∀ E (χ : EnJ E), IsMono (E_to_χ_map T (E:=E) χ).

  (* Definition 22 *)
  Definition Snsheaf_struct T := (separated T) /\ (∀ E (χ : E -> J), IsEquiv (E_to_χmono_map T (E:=E) (χ))). 

  Definition SnType_j_Type := {T : TruncType (trunc_S n) & Snsheaf_struct T}.

  Definition separated_is_HProp T : IsHProp (separated T).
    repeat (apply trunc_forall).
  Defined.

  Definition Snsheaf_struct_is_HProp T : IsHProp (Snsheaf_struct T).
    apply trunc_prod.
  Defined.



  (* If T is a n-Type, then if T is a n-sheaf, then T is also a (S n)-sheaf *)

  Lemma nsheaf_to_Snsheaf (T:TruncType (trunc_S n)) (Trn : IsTrunc n T) (nsheaf : IsSubu _ nj (@BuildTruncType n T Trn))
  : Snsheaf_struct T.
    split.
    { intros E χ u v.
      refine (isequiv_adjointify _ _ _ _).
      - unfold E_to_χ_map; simpl; intro p.
        apply path_forall; intro x.
        destruct χ as [χ χeq χdiag]. simpl in *.
        pose proof (transport idmap (χeq x) (x;1)). simpl in X.
        revert X.
        transparent assert (modal_family : (subuniverse_Type nj)).
        { refine (Build_subuniverse_Type _ nj (BuildTruncType _ (u x = v x)) _).
          apply istrunc_paths. apply trunc_succ. exact Trn.
          exact (subuniverse_paths _ nj (Build_subuniverse_Type _ nj (@BuildTruncType _ T Trn) nsheaf) (u x) (v x)). }
        apply (O_rec _ nj (χ x) modal_family); unfold modal_family; clear modal_family.
        intro xx; simpl.
        exact (ap10 p (x;xx)).
      - intro p. simpl. unfold E_to_χ_map in *; simpl in *.
        apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
        apply path_forall; intro x.
        pose (rew := @ap10_ap_precompose); unfold ap10 in rew; rewrite rew; clear rew.
        unfold ap10 at 1, path_forall at 1; rewrite eisretr. simpl.
        assert (χdiag := dense_diag χ).
        destruct χ as [χ χeq]. simpl in *.
        specialize (χdiag x (x;1)).
        unfold incl_Aeq_Eeq in χdiag.
        apply ap10 in χdiag.
        specialize (χdiag (x;1)). simpl in χdiag.
        rewrite χdiag.
        match goal with
          |[|- O_rec _ _ _ ?X _ _ = _] => set (sheaf := X) end.
        exact (ap10 (O_rec_retr _ _ (χ x.1) sheaf (λ xx : (χ x.1), ap10 p (x.1; xx))) x.2). 
      - intro p. destruct p. simpl.
        match goal with
          |[|- path_forall u u ?X = _] => assert (X=(λ _, 1)) end.
        { apply path_forall; intro x. rewrite O_rec_const. reflexivity. }
        rewrite X. apply path_forall_1. }
    { intros E χ.
      refine (isequiv_adjointify _ _ _ _).
      - intros f x.
        unfold J in χ; simpl in *.
        assert (p := transport idmap (j_is_nj (χ x).1) (χ x).2).
        revert p. simpl. apply (O_rec _ nj _ (Build_subuniverse_Type _ nj (@BuildTruncType _ T Trn) nsheaf)).
        intros xx. simpl in *.
        exact (f (x;xx)).
      - intro f. apply path_forall; intro x; simpl in *.
        unfold E_to_χmono_map; simpl.
        assert ((χ x.1).2 = (Oj_unit (χ x.1).1 x.2)) by apply path_ishprop.
        rewrite X.
        transparent assert (TrH: (IsTrunc n ((λ x : E, (χ x).1) x.1))).
        intros x0 y. apply (@trunc_leq -1 n). exact tt. exact (istrunc_trunctype_type _).
        path_via (O_rec n nj
                        {|
                          trunctype_type := (χ x.1).1;
                          istrunc_trunctype_type := _ |}
                        {|
                          st := {| trunctype_type := T; istrunc_trunctype_type := Trn |};
                          subu_struct := nsheaf |}
                        (λ xx : (χ x.1).1, f (x.1;xx))
                        (O_unit nj {|
                          trunctype_type := (χ x.1).1;
                          istrunc_trunctype_type := _ |}
                                x.2)).
        
        apply ap. exact (j_is_nj_unit (χ x.1).1 x.2).
        exact (ap10 (O_rec_retr _ _ {| trunctype_type := (χ x.1).1; istrunc_trunctype_type := TrH |}
                                {|
     st := {| trunctype_type := T; istrunc_trunctype_type := Trn |};
     subu_struct := nsheaf |}
                                (λ xx : ((χ x.1).1), f (x.1; xx)))
                    x.2).
      - intro f.
        apply path_forall; intro x.
        assert (p := transport idmap (j_is_nj (χ x).1) (χ x).2).
        revert p. simpl.
        transparent assert (sheaf : (subuniverse_Type nj)).
        { refine (Build_subuniverse_Type n nj
           (BuildTruncType _ (O_rec n nj
       {|
       trunctype_type := (χ x).1;
       istrunc_trunctype_type := _ |}
       {|
       st := {| trunctype_type := T; istrunc_trunctype_type := Trn |};
       subu_struct := nsheaf |}
       (λ xx : (χ x).1, E_to_χmono_map T χ f (x; xx))
       (transport (λ x0 : Type, x0) (j_is_nj (χ x).1) (χ x).2) = 
     f x)) _). }          
        apply (O_rec _ _ _ sheaf).
        unfold sheaf; clear sheaf. simpl. intro xx.
        pose (j_is_nj_unit (χ x).1 xx).
        assert ((χ x).2 = (Oj_unit (χ x).1 xx)) by apply path_ishprop.
        rewrite X.
        transparent assert (TrH: (IsTrunc n ((λ x : E, (χ x).1) x))).
        intros x0 y. apply (@trunc_leq -1 n). exact tt. exact (istrunc_trunctype_type _).
        path_via (O_rec n nj
                        {|
                          trunctype_type := (χ x).1;
                          istrunc_trunctype_type := _|}
                        {|
                          st := {| trunctype_type := T; istrunc_trunctype_type := Trn |};
                          subu_struct := nsheaf |}
                        (λ xx0 : (χ x).1, E_to_χmono_map T χ f (x; xx0))
                        (O_unit nj
                                {|
                          trunctype_type := (χ x).1;
                          istrunc_trunctype_type := _|} xx)).
        apply ap; exact p.
        exact (ap10 (O_rec_retr _ nj {| trunctype_type := (χ x).1; istrunc_trunctype_type := TrH |} {|
     st := {| trunctype_type := T; istrunc_trunctype_type := Trn |};
     subu_struct := nsheaf |} (λ xx0 : (χ x).1, E_to_χmono_map T χ f (x; xx0))) xx). }
  Defined.                                         

  Definition nj_inter_f (A : TruncType n) (φ : A -> TruncType n) : 
    (O nj (BuildTruncType _ {a:A & φ a})) ->
    (O nj (BuildTruncType _ {a:A & (O nj (φ a))}))
    := function_lift _
         nj
         (BuildTruncType _ {a:A & φ a})
         (BuildTruncType _ {a:A & (O nj (φ a))})
         (λ X, (X.1;nj.(O_unit) _ X.2)).

  Definition nj_inter_g (A : TruncType n) (φ : A -> TruncType n) : 
    (O nj (BuildTruncType _ {a:A & (O nj (φ a))})) ->
    (O nj (BuildTruncType _ {a:A & φ a})).
  Proof.
    apply O_rec. intro X.
    generalize X.2. apply O_rec; intro φa.
    apply nj.(O_unit). exact (X.1;φa).
  Defined.

  Instance nj_inter_equiv (A : TruncType n) (φ : A -> TruncType n) : IsEquiv (nj_inter_f A φ).
  apply (isequiv_adjointify _ (nj_inter_g A φ)).
  - intro x. unfold nj_inter_f, nj_inter_g. simpl in *.
    transitivity (function_lift n nj
                      (BuildTruncType _ {a:A & φ a})
                      (BuildTruncType _ {a:A & (O nj (φ a))})
                      (λ X : ∃ a : A, φ a,
                         (X.1;
                          O_unit nj
                                 (default_TruncType n (φ X.1) (istrunc_trunctype_type (φ X.1))) X.2))
                      (O_rec n nj 
                         (BuildTruncType _ {a:A & (O nj (φ a))})
                         (O nj
                            (BuildTruncType _ {a:A & φ a}))
                         (λ X : (BuildTruncType _ {a:A & (O nj (φ a))}),
                            (function_lift n nj (φ X.1) (BuildTruncType _ {a:A & φ a}) (λ b, (X.1;b)))
                              X .2) x)
      ); auto with path_hints.

    pose (foo := ap10 (reflect_factoriality_pre n nj
                         (BuildTruncType _ {a:A & (O nj (φ a))})
                         (((O nj
                              (BuildTruncType _ {a:A & φ a}))))
                         (((O nj
                              (BuildTruncType _ {a:A & (O nj (φ a))}))))
                         (function_lift n nj
                                        (BuildTruncType _ {a:A & φ a})
                                        (BuildTruncType _ {a:A & (O nj (φ a))})
                                        (λ X : (BuildTruncType _ {a:A & φ a}), (X .1; O_unit nj (φ X .1) X .2)))
                         ((λ X : (BuildTruncType _ {a:A & (O nj (φ a))}),
                             function_lift n nj (φ X .1)
                                           (BuildTruncType _ {a:A & φ a}) (λ b : φ X.1, (X.1; b)) 
                                           X .2))) x
         ). 
    etransitivity; try exact foo. clear foo.

    transitivity (
        O_rec n nj
          (BuildTruncType _ {a:A & (O nj (φ a))})
          (O nj
             (BuildTruncType _ {a:A & (O nj (φ a))}))
          (λ x0 :(BuildTruncType _ {a:A & (O nj (φ a))}),
             function_lift n nj (φ x0 .1)
                           (BuildTruncType _ {a:A & (O nj (φ a))})
                           (λ x : (φ x0 .1), (x0 .1; O_unit nj (φ x0 .1) x)) 
                           x0 .2) x
      ).
    apply (ap (λ u, O_rec n nj
                      (BuildTruncType _ {a:A & (O nj (φ a))})
                      (O nj
                         (BuildTruncType _ {a:A & (O nj (φ a))})) u x)).
    apply path_forall; intro x0.
    exact (ap10 (reflect_functoriality
                   n nj
                   (φ x0 .1)
                   (BuildTruncType _ {a:A & (φ a)})
                   (BuildTruncType _ {a:A & (O nj (φ a))})
                   (λ X, (X .1; O_unit nj (φ X .1) X .2))
                   (λ b : (φ x0 .1), (x0 .1; b))) x0.2
          ).
    exact (ap10 (O_rec_O_rec_dep_sect n nj
                                      (BuildTruncType _ {a:A & (O nj (φ a))})
                                      (λ a, (φ a.1))
                                      (λ u, λ v, (u.1;v))
                                      (λ u, u.2)
                                      (λ a, eta_sigma a)) x); simpl in foo.   
  - intro x. unfold nj_inter_f, nj_inter_g. simpl.
    pose (foo := ap10 (reflect_factoriality_post n nj
                         (BuildTruncType _ {a:A & (φ a)})
                         (BuildTruncType _ {a:A & (O nj (φ a))})
                         (O nj
                            (BuildTruncType _ {a:A & (φ a)}))
                         (λ X : (BuildTruncType _ {a:A & (O nj (φ a))}),
                                O_rec n nj (φ X .1)
                                      (O nj
                                         (BuildTruncType _ {a:A & (φ a)}))
                                      (λ φa : (φ X .1),
                                              O_unit nj
                                                     (BuildTruncType _ {a:A & (φ a)})
                                                     (X .1; φa)) X .2)
                         (λ X,
                                (X .1; O_unit nj (φ X .1) X .2)))
                      x
         ).

    etransitivity; try exact foo. clear foo.
    apply (ap10 (O_rec_O_rec_dep_retr n nj
                                      (BuildTruncType _ {a:A & (φ a)})
                                      (λ a, (φ a .1))
                                      (λ a b, (a.1;b))
                                      (λ a, a.2)
                                      (λ a, eta_sigma a))
                x).
  Defined.

  Definition nj_inter (A : TruncType n) (φ : A -> TruncType n) : 
    O nj (BuildTruncType n {a:A & (φ a)}) =
    O nj (BuildTruncType n {a:A & (O nj (φ a))}).
  Proof.
    apply unique_subuniverse.
    apply path_trunctype.
    exact (BuildEquiv _ _ _ (nj_inter_equiv _ _)).
  Defined.

  (** Put that elsewhere *)

  Lemma istruncmap_compose n {A B C:Type} (f:A -> B) (g: B -> C)
    : IsTruncMap n f -> IsTruncMap n g -> IsTruncMap n (g o f).
  Proof.
    intros Hf Hg.
    intro x.
    refine (trunc_equiv' _ (hfiber_compose f g x)^-1).
  Defined.

  Instance istruncmap_charn n {B:Type} (P: B -> TruncType n)
    : IsTruncMap n (pr1: sig P -> B).
  Proof.
    intro b. unfold hfiber.
    refine (@trunc_equiv (P b) _ (λ x:P b, ((b;x);1)) _ _ _).
    refine (isequiv_adjointify _ _ _ _).
    exact (fun X => transport (λ b, P b) (X.2) (X.1.2)).
    intros [[b' P'] eqb']; cbn in *. destruct eqb'.
    reflexivity.
    intro x; reflexivity.
  Defined.

  Lemma hfiber_compose_mono {A B C:Type} (f : A -> B) (g : B -> C) (Mg: IsMono g) b
    : hfiber f b <~> hfiber (g o f) (g b).
  Proof.
    refine (equiv_adjointify _ _ _ _).
    - intros [x p]. exact (x; ap g p).
    - intros [x p]. exact (x; (equiv_inv (IsEquiv := Mg (f x) b)) p).
    - intros [x p]. refine (path_sigma' _ 1 _); cbn.
      apply eisretr.
    - intros [x p]. refine (path_sigma' _ 1 _); simpl.
      apply eissect.
  Defined.
      


      
  (*********)

  (* Lemma 24 *)
  
  Definition nj_fibers_compose A B C (f : A -> B) (g : B -> C) (c : C)
             (HB : IsTruncMap n f) (HC : IsTruncMap n g)
  :
    O nj (@BuildTruncType _ (hfiber (g o f) c) (istruncmap_compose n f g HB HC c)) =
    O nj (BuildTruncType _ { w : hfiber g c & O nj (BuildTruncType _ (hfiber f w.1))}).
  Proof.
    etransitivity; [exact (ap (O nj) (@path_trunctype ua n (@BuildTruncType _ (hfiber (λ x : A, g (f x)) c) (istruncmap_compose n f g HB HC c)) _ (hfiber_compose f g c)))| cbn].
    apply unique_subuniverse. unfold default_TruncType.
    exact (ap (@st n nj) (nj_inter (@BuildTruncType _ (hfiber g c) (HC c)) (fun w => (@BuildTruncType _ (hfiber f w .1) (HB w.1))))). 
  Defined.
  
  Definition type_j_f {E} (χ: E -> J) 
  : (E -> subuniverse_Type nj) -> {e:E & (χ e).1}  -> subuniverse_Type nj
    := λ α e, α (pr1 e).

  Definition type_j_inv {E} (χ: E -> J) : ({e:E & (χ e).1} -> subuniverse_Type nj) -> E -> subuniverse_Type nj.
  Proof.
    intros α e.
    apply (O nj).
    pose (m := pr1 : {e:E & (χ e).1} -> E).
    pose (f := pr1 : {e: (∃ e : E, (χ e).1) & (α e)} -> (∃ e : E, (χ e).1)).
    assert (IsTruncMap n (m o f)).
    apply istruncmap_compose. apply istruncmap_charn.
    intro x. exact (@trunc_leq -1 n tt _ (istruncmap_charn -1 (pr1 o χ) x)).
    exact (BuildTruncType _ (hfiber (λ x : ∃ e : ∃ e : E, (χ e).1, α e, m (f x)) e)).
  Defined.

  Definition inter_symm E (χ φ : E -> Type) x :
  hfiber (λ t : {b : {b : E & χ b} & φ (pr1 b)}, pr1 (pr1 t)) x <~>
  hfiber (λ t : {b : {b : E & φ b} & χ (pr1 b)}, pr1 (pr1 t)) x.
    unfold hfiber. cbn.
    refine (equiv_functor_sigma' _ _).
    refine (equiv_adjointify _ _ _ _).
    - intros [[a b] c]. exact ((a;c);b).
    - intros [[a b] c]. exact ((a;c);b).
    - intros a. reflexivity.
    - intros a. reflexivity.
    - intros [[a b] c]; apply equiv_idmap.
  Defined.
  
  (* Proposition 23, sheaf part *)
  Instance nTjTiSnTjT_eq E (χ : E -> J) : IsEquiv (λ (f : E -> subuniverse_Type nj) (t : {b : E & pr1 ((χ b))}), f (pr1 t)). 
  apply (isequiv_adjointify _ (type_j_inv (E:=E) χ)).
  - intro φ.
    unfold type_j_inv. simpl. 
    apply path_forall; intro x.
    rewrite (O_modal n nj (φ x)).
    repeat apply ap.
    apply path_trunctype.
    pose (hfiber_fibration x (trunctype_type o (@st n nj) o φ)).
    cbn in e.
    etransitivity; try exact (hfiber_fibration x (trunctype_type o (@st n nj) o φ))^-1.
    symmetry. apply (hfiber_compose_mono pr1 pr1).
    intros X Y.
    apply isequiv_pr1_path_hprop.
  - intro φ.
    unfold type_j_inv. simpl.
    apply path_forall; intro x.
    rewrite (O_modal n nj (φ x)).
    assert (Tr1: IsTruncMap n (λ x0 : ∃ e : ∃ e : E, φ e, (χ e.1).1, (x0.1).1)).
    refine (istruncmap_compose n pr1 pr1 _ _). 
    intro e; exact (@trunc_leq -1 n tt _ (istruncmap_charn -1 (λ t, (χ t.1).1) e)).

    match goal with
    |[|- O nj ?XX = _] =>
     path_via (O nj (@BuildTruncType _ (hfiber (λ x0 : ∃ e : ∃ e : E, (φ e), (χ e.1).1, x0.1.1) x) (istruncmap_fiber x)))
    end.
    apply ap.
    apply path_trunctype. cbn.
    exact (inter_symm _ (fun b => (χ b).1) (fun b => φ b) x).
    pose (X := nj_fibers_compose (∃ e : ∃ e : E, φ e, (χ e.1).1) {e:E & φ e} E pr1 pr1 x).
    assert (HB : IsTruncMap n (λ s : ∃ e : ∃ e : E, φ e, (χ e.1).1, s.1)).
    intro e. refine (@trunc_leq -1 n tt _ _).
    assert (HC : IsTruncMap n
                            (λ s : ∃ e : E, φ e, let (proj1_sig, _) := s in proj1_sig)).
    intro e. refine (istruncmap_charn _ _ _).
    cbn in *.
    specialize (X HB HC).
    match goal with
    |[|- O nj (@BuildTruncType _ _ ?foo) = _] => assert (rTr: istruncmap_compose n pr1 pr1 HB HC x = foo) by apply path_ishprop
    end.
    destruct rTr.
    etransitivity; [exact X| clear X; cbn].

    apply ap. apply path_trunctype. cbn.
    eapply transitive_equiv.
    apply equiv_sigma_contr.
    intro a.
    match goal with
    |[|- Contr (trunctype_type (@st n nj (O nj (BuildTruncType _ ?foo))))]
     => pose (f:= j_is_nj (BuildTruncType -1 foo))
    end.
    match goal with
    |[ f : _ = trunctype_type (@st n nj (O nj (@BuildTruncType _ _ ?foo))) |- Contr (trunctype_type (@st n nj (O nj (@BuildTruncType _ _ ?bar)))) ]
     => assert (foo = bar) by apply path_ishprop
    end.
    destruct X.
    apply (transport (fun X => Contr X) f); cbn.
    apply (transport (fun X => Contr (not (not X))) (path_universe_uncurried (hfiber_fibration a.1 (λ x, (χ x.1).1)))).
    apply Oj_J_Contr.
    apply equiv_path.
    exact (path_universe_uncurried (hfiber_fibration x φ))^.
  Defined.

  Definition nTjTiseparated_eq_fun_univ {E:Type} {χ:EnJ E} {φ1 φ2}
             (p: E_to_χ_map (@BuildTruncType _ (subuniverse_Type nj) (subuniverse_Type_is_TruncTypeSn n nj)) χ φ1 =
                 E_to_χ_map (@BuildTruncType _ (subuniverse_Type nj) _) χ φ2)
             (x:E)
  :  (φ1 x) -> (φ2 x).
    unfold E_to_χ_map in p.
    generalize dependent (EnJ_is_nJ χ x).
    refine (O_rec n nj (χ x) (Build_subuniverse_Type n nj (BuildTruncType _ (φ1 x -> φ2 x)) _) _).
    intro v.
    exact (transport (λ U, U) (ap (trunctype_type) (ap (@st n nj) (ap10 p (x;v))))).
  Defined.
  
  Lemma nTjTiseparated_eq_fun_univ_invol {E:Type} {χ:EnJ E} {φ1 φ2}
        (p: E_to_χ_map (@BuildTruncType _ (subuniverse_Type nj) (subuniverse_Type_is_TruncTypeSn n nj)) χ φ1 =
            E_to_χ_map (@BuildTruncType _ (subuniverse_Type nj) _) χ φ2)
        (x:E)
  : forall (y:φ2 x), nTjTiseparated_eq_fun_univ p x (nTjTiseparated_eq_fun_univ p^ x y) = y.
  Proof.
    intro y. unfold nTjTiseparated_eq_fun_univ; simpl.
    unfold E_to_χ_map in p; simpl in *.
    pose (foo := ap10 (ap10 (reflect_factoriality_arrow_space n nj
                               (χ x)
                               (φ1 x)
                               (φ2 x)
                               (λ v : (χ x),
                                      transport idmap
                                                (ap (trunctype_type) (ap (@st n nj) (ap10 p (x;v)))))
                               (λ v : (χ x),
                                      transport idmap
                                                
                                                (ap (trunctype_type) (ap (@st n nj) (ap10 p^ (x;v))))))
                            (EnJ_is_nJ χ x)) y
         ). 
    apply (transport (λ u, u = y) foo^). clear foo.

    transitivity (O_rec n nj (χ x)
                    {|
                      st := {|
                             trunctype_type := φ2 x → φ2 x;
                             istrunc_trunctype_type := trunc_arrow
                                                         (istrunc_trunctype_type (φ2 x)) |};
                      subu_struct := subuniverse_arrow n nj (φ2 x) (φ2 x) |}
                    (λ (v : χ x) (x0 : φ2 x),
      transport (λ x1 : Type, x1)
        (ap trunctype_type (ap (@st n nj) (ap10 p (x; v))))
        (transport (λ x1 : Type, x1)
           (ap trunctype_type (ap (@st n nj) (ap10 p (x; v))))^ x0)) (EnJ_is_nJ χ x) y); auto with path_hints.
    apply (ap (λ u, O_rec n nj (χ x)
                          {|
                            st := {|
                                   trunctype_type := φ2 x → φ2 x;
                                   istrunc_trunctype_type := trunc_arrow
                                                               (istrunc_trunctype_type (φ2 x)) |};
                            subu_struct := subuniverse_arrow n nj (φ2 x) (φ2 x) |}
                          u (EnJ_is_nJ χ x) y)).
    funext v x0.
    apply ap. apply (ap (λ U, transport idmap U x0)).
    repeat rewrite <- ap_V. rewrite ap10_V. reflexivity.

    pose (fooo := @transport_arrow_space_dep_path n nj fs (φ1 x) (φ2 x) (χ x) (λ v, (ap (trunctype_type) (ap (@st n nj) (ap10 p (x;v)))))).
    simpl in fooo.
    
    apply (transport (λ U, O_rec n nj (χ x)
                                 {|
                                   st := {|
                                          trunctype_type := φ2 x → φ2 x;
                                          istrunc_trunctype_type := trunc_arrow
                                                                      (istrunc_trunctype_type (φ2 x)) |};
                                   subu_struct := subuniverse_arrow n nj (φ2 x) (φ2 x) |}
                                 U
                                 (EnJ_is_nJ χ x) y = y) fooo^).
    clear fooo; simpl.
    rewrite O_rec_const; reflexivity.
  Defined.

  Definition nTjTiseparated_eq_inv (E:Type) (χ:EnJ E) φ1 φ2 :
    (E_to_χ_map (@BuildTruncType _ (subuniverse_Type nj) (subuniverse_Type_is_TruncTypeSn n nj)) χ φ1 =
            E_to_χ_map (@BuildTruncType _ (subuniverse_Type nj) _) χ φ2)
    -> φ1 = φ2.
    intro p.
    simpl in *.
    unfold E_to_χ_map in p; simpl in p.
    apply path_forall; intro x.
    apply unique_subuniverse; apply path_trunctype.
    exists (nTjTiseparated_eq_fun_univ p x).
    apply isequiv_adjointify with (g := nTjTiseparated_eq_fun_univ (inverse p) x).
    - exact (nTjTiseparated_eq_fun_univ_invol p x).
    - exact (transport (λ u, ∀ y : φ1 x, nTjTiseparated_eq_fun_univ (inverse p) x (nTjTiseparated_eq_fun_univ u x y) = y) (inv_V p) (nTjTiseparated_eq_fun_univ_invol (inverse p) x)).
  Defined.

  (* Proposition 23, separation part *)
  Lemma nTjTiseparated_eq : separated (@BuildTruncType _ (subuniverse_Type nj) (@subuniverse_Type_is_TruncTypeSn _ nj ua)).
    intros E χ φ1 φ2.
    apply isequiv_adjointify with (g := @nTjTiseparated_eq_inv E χ φ1 φ2).
    - intro p. 
      unfold E_to_χ_map in *; simpl in *.
      apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ (φ1 o (@pr1 _ (fun e => (χ e)))) (φ2 o pr1))).
      apply path_forall; intro x.
      unfold nTjTiseparated_eq_inv.
      pose (r:= @ap10_ap_precompose); unfold ap10 in r; rewrite r; clear r.
      unfold path_forall; rewrite eisretr.

      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_unique_subuniverse _ _ _ _))). apply isequiv_inverse.
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_path_trunctype))). apply isequiv_inverse.
      repeat rewrite eissect.
      apply path_equiv; cbn.
      unfold nTjTiseparated_eq_fun_univ, EnJ_is_nJ. 
      apply (transport (λ U, O_rec n nj _ {|
     st := {|
           trunctype_type := φ1 (let (proj1_sig, _) := x in proj1_sig)
                             → φ2 (let (proj1_sig, _) := x in proj1_sig);
           istrunc_trunctype_type := trunc_arrow
                                       (istrunc_trunctype_type
                                          (φ2
                                             (let
                                              (proj1_sig, _) := x in
                                              proj1_sig))) |};
     subu_struct := subuniverse_arrow n nj
                      (φ1 (let (proj1_sig, _) := x in proj1_sig))
                      (φ2 (let (proj1_sig, _) := x in proj1_sig)) |} _ U = _) ((witness_is_eta χ x)^)).
      etransitivity;
        [ exact (ap10 (O_rec_retr n nj (χ x.1) {|
     st := {|
           trunctype_type := φ1 (let (proj1_sig, _) := x in proj1_sig)
                             → φ2 (let (proj1_sig, _) := x in proj1_sig);
           istrunc_trunctype_type := trunc_arrow
                                       (istrunc_trunctype_type
                                          (φ2
                                             (let
                                              (proj1_sig, _) := x in
                                              proj1_sig))) |};
     subu_struct := subuniverse_arrow n nj
                      (φ1 (let (proj1_sig, _) := x in proj1_sig))
                      (φ2 (let (proj1_sig, _) := x in proj1_sig)) |}
                                    (λ v : χ (let (proj1_sig, _) := x in proj1_sig),
      transport (λ U : Type, U)
        (ap trunctype_type
           (ap (@st n nj) (ap10 p (let (proj1_sig, _) := x in proj1_sig; v)))))) x.2) |].
      repeat apply ap. destruct x as [x1 x2]. reflexivity.
      
    - intro p; destruct p.
      unfold E_to_χ_map, nTjTiseparated_eq_inv in *; simpl in *.
      eapply concat; [idtac | apply (path_forall_1 φ1)]; apply ap.
      apply path_forall; intro x; simpl.
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_unique_subuniverse _ _ _ _))). apply isequiv_inverse.
      apply (@equiv_inj _ _ (equiv_inv (IsEquiv := isequiv_path_trunctype))). apply isequiv_inverse.
      repeat rewrite eissect.
      apply path_equiv; cbn.
      unfold transport, nTjTiseparated_eq_fun_univ; simpl.
      exact (ap10 (O_rec_const n nj (χ x) {|
     st := {|
           trunctype_type := φ1 x → φ1 x;
           istrunc_trunctype_type := trunc_arrow
                                       (istrunc_trunctype_type (φ1 x)) |};
     subu_struct := subuniverse_arrow n nj (φ1 x) (φ1 x) |} idmap) (EnJ_is_nJ χ x)). 
  Defined.

  (* Proposition 23 *)
  Lemma nType_j_Type_is_SnType_j_Type : Snsheaf_struct (@BuildTruncType _ (subuniverse_Type nj) (@subuniverse_Type_is_TruncTypeSn _ nj ua)).
  Proof.
    split.
    apply nTjTiseparated_eq.
    intros E χ. unfold E_to_χ_map; simpl.
    exact (nTjTiSnTjT_eq _ _).
  Defined.

  Definition nType_j_Type_sheaf : SnType_j_Type :=
    ((@BuildTruncType _ (subuniverse_Type nj) (@subuniverse_Type_is_TruncTypeSn _ nj ua));nType_j_Type_is_SnType_j_Type).

  (* Proposition 25, sheaf part *)
  Instance dep_prod_SnType_j_Type_eq
           (A : Type)
           (B : A -> SnType_j_Type)
  : forall (E:Type) (χ : E -> J) (H := λ a, (snd (pr2 (B a))) E χ),
      IsEquiv (λ (f : E -> ∀ a : A, (B a).1) (t : {b : E & (χ b).1}), f (pr1 t)).
  intros E χ H.   
  apply (isequiv_adjointify _ (λ g e a, (@equiv_inv _ _ _ (H a) (λ x, g x a) e))).
  - intro φ.
    apply path_forall; intro x.
    apply path_forall; intro a.
    destruct (H a) as [inv retr sect adj]; simpl in *.
    clear adj; clear sect.
    unfold Sect, E_to_χmono_map in retr.
    specialize (retr (λ x, φ x a)).
    exact (ap10 retr x).
  - intro φ.
    funext x a.
    destruct (H a) as [inv retr sect adj]; simpl in *.
    clear adj; clear retr.
    unfold Sect, E_to_χ_map in sect.
    specialize (sect (λ x, φ x a)).
    exact (ap10 sect x).
  Defined.

  Definition dep_prod_SnType_j_Type_sep_inv
             (A : Type)
             (B : A -> SnType_j_Type)
             (E : Type)
             (χ : EnJ E)
             (x y : E -> ∀ a : A, (B a).1)
  : (λ (f : E -> ∀ a : A, (B a).1) (t : {b : E & (χ b)}),
     f t .1) x =
    (λ (f : E -> ∀ a : A, (B a).1) (t : {b : E & (χ b)}),
     f t .1) y
    -> x = y.
  Proof.
    intro H; simpl in H.
    funext u a .
    refine (@ap10 _ _ (λ u, x u a) (λ u, y u a) _ u).
    pose ((fst (B a).2) E χ (λ v, x v a) (λ v, y v a)).
    exact (equiv_inv (IsEquiv := i) (path_forall _ _ (λ t, apD10 ((apD10 H) t) a))).
  Defined.

  (* Proposition 25, separated part *)
  Lemma dep_prod_SnType_j_Type_sep
        (A : Type)
        (B : A -> SnType_j_Type)
  : forall (E:Type) (χ : EnJ E), IsMono
                                   (λ (f : E -> ∀ a : A, (B a).1) (t : {b : E & χ b}), f (t.1)).
    intros E χ.
    unfold IsMono.
    intros f g.
    apply @isequiv_adjointify with (g := @dep_prod_SnType_j_Type_sep_inv A B E χ f g).
    - unfold Sect.
      intro p.
      unfold dep_prod_SnType_j_Type_sep_inv. 
      unfold E_to_χ_map. simpl.
      unfold equiv_inv.
      pose (foo := path_forall_precompose (∃ b : E, χ b)
                                   E
                                   (∀ a : A, (B a).1)
                                   pr1
                                   f
                                   g
                                   (λ u : E,
                                          path_forall (f u) (g u)
                                                      (λ a : A,
                                                             ap10
                                                               ((let (equiv_inv, eisretr, eissect, _) :=
                                                                     fst (B a) .2 E χ (λ v : E, f v a) (λ v : E, g v a) in
                                                                 equiv_inv)
                                                                  (path_forall (λ t : ∃ b : E, (χ b), f t .1 a)
                                                                               (λ t : ∃ b : E, (χ b), g t .1 a)
                                                                               (λ t : ∃ b : E, (χ b), apD10 (apD10 p t) a))) u))).
      apply (transport (λ U, U=p) foo^); clear foo.
      apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
      unfold ap10 at 1, path_forall at 1; rewrite eisretr.
      apply path_forall; intro x.
      apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)); unfold path_forall at 1; rewrite eisretr.
      apply path_forall; intro a.

      pose (r := @ap10_ap_precompose (∃ b : E, χ b)
                             E
                             ((B a).1)
                             pr1
                             (λ v, f v a)
                             (λ v, g v a)
                             ((let (equiv_inv, eisretr, eissect, _) :=
                                   fst (B a) .2 E χ (λ v : E, f v a) (λ v : E, g v a) in
                               equiv_inv)
                                (path_forall (λ t : ∃ b : E, (χ b), f t .1 a)
                                             (λ t : ∃ b : E, (χ b), g t .1 a)
                                             (λ t : ∃ b : E, (χ b), apD10 (apD10 p t) a)))
                             x);
        unfold ap10 in r; rewrite <- r; clear r.
      rewrite (@eisretr _ _ _ (fst (B a) .2 E χ (λ v : E, f v a) (λ v : E, g v a))).

      unfold path_forall; rewrite eisretr.
      reflexivity.
    - intro v. unfold dep_prod_SnType_j_Type_sep_inv. 
      unfold E_to_χ_map. simpl.
      destruct v. simpl.
      etransitivity; [idtac | apply path_forall_1]; apply ap; apply path_forall; intro x.
      etransitivity; [idtac | apply path_forall_1]; apply ap; apply path_forall; intro y.
      assert ((apD10
                 ((let (equiv_inv, eisretr, eissect, _) :=
                       fst (B y) .2 E χ (λ v : E, f v y) (λ v : E, f v y) in
                   equiv_inv)
                    (path_forall (λ t : ∃ b : E, χ b, f t .1 y)
                                 (λ t : ∃ b : E, χ b, f t .1 y) (λ t : ∃ b : E, χ b, 1)))) = λ _, 1).
      apply (@equiv_inj _ _ _ (isequiv_path_forall _ _)).
      unfold path_forall. rewrite eissect. 
      apply (@equiv_inj _ _ _ (fst (B y) .2 E χ (λ v : E, f v y) (λ v : E, f v y))).
      pose (foo := @eisretr _ _ _ (fst (B y) .2 E χ (λ v : E, f v y) (λ v : E, f v y))).
      unfold Sect, equiv_inv in foo; simpl in foo.
      rewrite foo.
      unfold E_to_χ_map. simpl.
      apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
      rewrite eisretr.
      apply path_forall; intro t.
      match goal with
        |[|- _ = apD10 (ap _ ?X) _] => pose (ap10_ap_precompose (pr1 : ({e:E & χ e} -> E)) X) end. unfold ap10 in p; rewrite p.
      unfold ap10; rewrite eisretr. reflexivity.
      exact (apD10 X x).
  Defined.

  (* Proposition 25 *)
  Definition dep_prod_SnType_j_Type
    : forall A (B : A -> SnType_j_Type),
      Snsheaf_struct (BuildTruncType _ (forall a, pr1 (B a))).
  Proof.
    intros. split.
    exact (dep_prod_SnType_j_Type_sep _ _).
    exact (dep_prod_SnType_j_Type_eq _ _).
  Defined.

  (* Definition of diagonals *)
  Definition δ (T:TruncType (trunc_S n)) : T * T-> TruncType n.
    intros x. exists (fst x = snd x). refine (istrunc_paths _ _ _).
  Defined.

  Definition Δ (T:TruncType (trunc_S n)) := {x:T*T & δ T x}.
  
  Definition clδ (T:TruncType (trunc_S n)) := nj.(O) o (δ T).

  Definition clΔ (T:TruncType (trunc_S n)) := {x:T*T & clδ T x}.

  Lemma equal_hfibers (A B:Type) (r:A=B) (f g:A -> B) e (p : f = equiv_path _ _ r) (q : g = equiv_path _ _ r)
  : {a:A & a = e} <~> {a:A & f a = g e}.

    exists (λ x:(∃ a : A, a = e), (x.1 ; (ap f x.2) @ (ap10 (p@q^) e))).
    destruct r.
    assert (f=idmap).
    apply path_forall; intro x. exact (ap10 p x).
    destruct p. destruct q.
    rewrite X. simpl.
    apply @isequiv_adjointify with  (g:= ( λ x, (x.1; x.2))).
    - intro x. simpl. hott_simpl.
    - intro x. simpl. hott_simpl. 
  Defined.
        
  Lemma dicde_l {E:Type} (φ:E -> TruncType n) (A:={e:E & φ e}) (clA := {e:E & (O nj (φ e))}) (e:clA)
  : (∃ rx : (O nj (φ e .1)),
       rx =
      e.2) =(∃ rx : (O nj (φ e .1)),
       O_rec n nj (φ e .1) (O nj (O nj (φ e .1)))
             (λ x : (φ e .1),
                    O_unit nj (O nj (φ e .1)) (O_unit nj (φ e .1) x)) rx =
       O_unit nj (O nj (φ e .1)) e .2).
  Proof.
    apply path_universe_uncurried.
    apply (@equal_hfibers
                   ((O nj (φ e .1)))
                   ((O nj (O nj (φ e .1))))
                   (ap (trunctype_type) (ap (@st n nj) ((O_invol_ n nj (φ e .1)))))
                   (O_rec n nj (φ e .1) (O nj (O nj (φ e .1)))
                          (λ x : (φ e .1), O_unit nj (O nj (φ e .1)) (O_unit nj (φ e .1) x)))
                   (O_unit nj (O nj (φ e .1)))
                   e.2). 
    - cbn.
      etransitivity; [exact (O_rec_sect n nj (φ e .1) (O nj (O nj (φ e .1))) (O_unit nj _)) | apply OO_unit_idmap].
    - apply OO_unit_idmap.
  Defined.
    
  Lemma dicde_ll
        (E : Type)
        (φ : E → TruncType n)
        (A := ∃ e : E, (φ e) : Type)
        (clA := ∃ e : E, O nj (φ e) : Type)
        (a : ∃ e : E, O nj (φ e))
        (x : ∃ π : (φ a .1), O_unit nj (φ a .1) π = a .2)
        (π : ∃ π : (φ a .1), O_unit nj (φ a .1) π = a .2)
        (π' : ∃ π : (φ a .1), O_unit nj (φ a .1) π = a .2)
  : equiv_path _ _ (dicde_l φ a) (a .2; 1) =
    (O_unit nj (φ a .1) π' .1;
     islex_compat_func mod_nj (φ a .1) (O nj (φ a .1)) (O_unit nj (φ a .1)) _ π').
    unfold dicde_l.   
    unfold path_universe_uncurried.
    rewrite eisretr. simpl. hott_simpl.
    apply @path_sigma' with (p := π'.2^). simpl. destruct π' as [b p]. simpl. destruct p. simpl.
    unfold islex_compat_func. simpl.
    apply ap10_O_retr_sect.
  Defined.

  Lemma dense_into_cloture_dense_eq {E:Type} (φ:E -> TruncType n) (A:={e:E & φ e}) (clA := {e:E & O nj (φ e)})
  : is_dense_eq (λ e:clA, (BuildTruncType _ {π : φ e.1 & O_unit nj _ π = e.2})).
    intro e.
    assert (rew := ((islex_nj (φ e .1) (O nj (φ e .1)) (O_unit nj _) e.2) @ (dicde_l φ e)^)).
    apply path_universe_uncurried.
    apply (transport (λ U, (∃ e' : clA, e = e') <~> U) (islex_nj (φ e .1) (O nj (φ e .1)) (O_unit nj _) e.2)^).
    apply (transport (λ U, (∃ e' : clA, e = e') <~> U) (dicde_l φ e)).
    
    exists ((λ x:(∃ e' : clA, e = e'), existT (λ u, u = e.2) e.2 1)).
    apply @isequiv_adjointify with (g:= (λ x:(∃ rx : ((O nj (φ e .1))), rx = e .2), ((e.1;x.1); path_sigma _ e (e.1;x.1) 1 x.2^))).

    - intros [x p]. destruct p. reflexivity.
    - intros [x p]. destruct p. simpl.
      apply @path_sigma' with (p := eta_sigma _).
      reflexivity.
  Defined.

  (** Put that elswhere *)
  Lemma transport_equiv (A: Type) (f g:A -> Type) (x y: A) (p: x=y) (q: f x <~> g x)
  : transport (λ a:A, f a <~> g a) p q
    = (equiv_compose' (equiv_path _ _ (ap g p)) (equiv_compose' q (equiv_inverse (equiv_path _ _ (ap f p))))).
    path_induction.
    destruct q. apply path_equiv. reflexivity.
  Defined.

  (*****)

  Lemma dense_into_cloture_dense_diag (E:Type) (φ:E -> TruncType n) (A:={e:E & φ e}) (clA := {e:E & (O nj (φ e))})
  : is_dense_diag _ (dense_into_cloture_dense_eq φ).
    intros x p.
    unfold dense_into_cloture_dense_eq.
    apply path_forall; intro y.
    unfold path_universe_uncurried. rewrite eisretr.
    simpl.
    destruct x as [a x]. simpl in x. simpl in p. destruct p as [a' q]. destruct a' as [a' π]. simpl in q.
    destruct q. simpl.
    destruct y as [[a' π'] q]. simpl in *. destruct q. simpl in *.
    unfold incl_Aeq_Eeq. simpl.
    rewrite <- transport_pp.
    rewrite transport_equiv. simpl.
    simpl.
    rewrite ap_idmap.
    rewrite transport_pp.

    pose (foo := lex_compat (φ a .1) (O nj (φ a .1)) (O_unit nj (φ a .1))). unfold equiv_path in foo; simpl in foo.
    specialize (foo a.2 π'). simpl in foo.
    unfold hfiber in foo. simpl in foo.

    apply (moveR_transport_V idmap (islex_nj (φ a .1) (O nj (φ a .1)) (O_unit nj (φ a .1)) a .2) (transport idmap (dicde_l φ a)  (a .2; 1))).

    apply (transport (λ U, transport idmap (dicde_l φ a) (a .2; 1) = U) foo^).
    clear foo.
    apply dicde_ll. exact π. exact π'.
  Qed.

  (* Any object seen as a subobject of its closure is closed *)
  Definition dense_into_cloture (E:Type) (φ:E -> TruncType n) (A:={e:E & φ e}) (clA := {e:E & (O nj (φ e))})
  : EnJ clA.
    refine (Build_EnJ _ _ (dense_into_cloture_dense_eq φ)).
  Defined.

  (*** CHECK IF THAT IS NEEDED *)

  (* Definition transport_density (E:Type) (φ:E -> TruncType n) (A:={e:E & (φ e).1}) (clA := {e:E & (O nj (φ e)).1.1}) *)
  (* : forall X, clA = X -> EnJ X. *)
  (*   pose (e := dense_into_cloture φ); simpl in e. *)
  (*   assert (χdiag := dense_diag e). *)
  (*   destruct e as [χ χeq]. *)
  (*   intros X p. *)
  (*   refine (Build_EnJ _ _). *)
  (*   - intro x. apply χ. *)
  (*     apply (equiv_path _ _ p). *)
  (*     exact x. *)
  (*   - destruct p. intro x. simpl. *)
  (*     apply χeq. *)
  (*   (* - destruct p. intros x e'. simpl. *) *)
  (*     (* apply χdiag. exact e'. *) *)
  (* Defined. *)

  (* Definition path_sigma_transport (E:Type) (φ χ : E -> Type) (eq : χ = φ) (x y : {e:E & φ e}) *)
  (* : (x = y) <~> ((x.1 ; transport idmap (ap10 eq x.1)^ x.2) = (y.1 ; transport idmap (ap10 eq y.1)^ y.2)). *)
  (*   destruct eq. simpl. *)
  (*   apply equiv_idmap. *)
  (* Defined. *)

  (* Definition path_sigma_transport_transport (E:Type) (φ χ : E -> Type) (α : {e:E & (χ e)} -> Type) (eq : χ = φ) (x y : {e:E & φ e}) (xy : x = y)  *)
  (* : transport (λ u:{e:E & (χ e)}, α u) ((path_sigma_transport eq x y) xy)^ *)
  (*   = *)
  (*   transport (λ u:{e:E & (φ e)}, α (u.1 ; transport idmap (ap10 eq u.1)^ u.2)) *)
  (*             xy^. *)
  (* destruct eq; simpl. reflexivity. *)
  (* Defined. *)
            
  (* Definition path_sigma_transport' (E:Type) (φ χ : E -> Type) (eq : χ == φ) (x y : {e:E & φ e}) *)
  (* : (x = y) <~> ((x.1 ; transport idmap (eq x.1)^ x.2) = (y.1 ; transport idmap (eq y.1)^ y.2)). *)
  (*   transitivity ((x.1; transport idmap (ap10 (path_forall _ _ eq) x.1)^ x.2) = (y.1; transport idmap (ap10 (path_forall _ _ eq) y.1)^ y.2)). *)
  (*   refine (path_sigma_transport _ _ _). *)
  (*   unfold ap10, path_forall. rewrite eisretr.  *)
  (*   apply equiv_idmap. *)
  (* Defined. *)

  (* Definition path_sigma_transport'_transport (E:Type) (φ χ : E -> Type) (α : {e:E & (χ e)} -> Type) (eq : χ == φ) (x y : {e:E & φ e}) (xy : x = y) *)
  (* : transport (λ u:{e:E & (χ e)}, α u) ((path_sigma_transport' eq x y) xy)^ *)
  (*   = *)
  (*   transport (λ u:{e:E & (φ e)}, α (u.1 ; transport idmap (eq u.1)^ u.2)) *)
  (*             xy^. *)
  (* simpl. *)
  (* destruct (eisretr apD10 eq). simpl.  simpl. *)
  (* exact (@path_sigma_transport_transport E φ χ α (path_forall χ φ eq) x y xy). *)
  (* Defined. *)
  (* Opaque path_sigma_transport'. *)

  (* Definition transport_density_sigma (E:Type) (φ:E -> TruncType n) (A:={e:E & (φ e).1}) (clA := {e:E & (O nj (φ e)).1.1}) *)
  (* : forall α:E -> TruncType n, (pr1 o pr1 o (O nj) o φ == pr1 o α) -> EnJ {e:E & (α e).1}. *)
  (*   intros α p. *)
  (*   transparent assert (X : (clA = (∃ e : E, (α e).1))). *)
  (*   { apply path_universe_uncurried. *)
  (*     apply (equiv_functor_sigma_id). *)
  (*     intro a. apply equiv_path. apply p. *)
  (*   } *)
  (*   pose (e := dense_into_cloture φ); simpl in e. *)
  (*   assert (χdiag := dense_diag e). *)
  (*   destruct e as [χ χeq]. *)
  (*   refine (Build_EnJ _ _). *)
  (*   - intro x. apply χ. *)
  (*     exists x.1. *)
  (*     apply (equiv_path _ _ (p x.1)). *)
  (*     exact x.2. *)
  (*   - intro e. simpl in *. *)

  (*     pose (eq := χeq (e.1; transport idmap (p e.1)^ e.2)). *)
  (*     etransitivity; try exact eq. clear eq. *)
  (*     apply path_universe_uncurried. *)
  (*     refine (equiv_functor_sigma' _ _). *)
  (*     apply (equiv_functor_sigma_id). *)
  (*     intro a. *)
  (*     apply equiv_path. exact (p a)^. *)
  (*     intro a. simpl. unfold functor_sigma. *)
  (*     apply path_sigma_transport'. *)
  (* Defined. *)

    (** We note that a type is separated if, and only if all its path spaces are n-sheaves *)
  Definition separated_nj_paths (T:TruncType (n.+1))
    : separated T -> forall x y:T, IsSubu n nj (BuildTruncType _ (x=y)).
  Proof.
    intros sepT x y.
    rewrite <- (subuniverse_iff_O n nj _).
    refine (O_unit_retract_equiv n nj _ _ _).
    intro p.
    specialize (sepT _ (dense_into_cloture (T*T) (λ x, BuildTruncType _ (fst x = snd x))) (fst o pr1) (snd o pr1)).
    apply (λ C, ap10 (equiv_inv (IsEquiv := sepT) C) ((x,y);p)).
    unfold E_to_χ_map. apply path_forall; intros q. exact q.2.1.
    intro p. destruct p.
    transparent assert (xx: (∃
                 (x : ∃ e : T ∧ T,
                      O nj (BuildTruncType _ (fst e = snd e)))
                 (π : fst (pr1 x) = snd (pr1 x)),
                 O_unit nj
                   (BuildTruncType _ (fst (pr1 x) = snd (pr1 x))) π = 
                 pr2 x)).
    { refine (exist _  _ _).
      exists (x,x).
      apply O_unit. reflexivity.
      simpl. exists 1. reflexivity. }
    match goal with
    |[|- ap10 ?gg _ = _] => path_via (ap10 gg (pr1 xx))
    end.
    rewrite <- ap10_ap_precompose.
    unfold equiv_inv. simpl.
    destruct (sepT (∃ e : T ∧ T, O nj (BuildTruncType _ (fst e = snd e)))
            (dense_into_cloture (T ∧ T) (λ x0 : T ∧ T, BuildTruncType _ (fst x0 = snd x0)))
            (λ
             x0 : ∃ e : T ∧ T, O nj (BuildTruncType _ (fst e = snd e)),
             let (fst, _) := let (proj1_sig, _) := x0 in proj1_sig in fst)
            (λ
             x0 : ∃ e : T ∧ T, O nj (BuildTruncType _ (fst e = snd e)),
               let (_, snd) := let (proj1_sig, _) := x0 in proj1_sig in snd)) as [inv retr sect _].
    cbn in *.
    unfold Sect, E_to_χ_map in *; cbn in *.
    specialize (retr (path_forall _ _
              (λ
               q : ∃
                   (x0 : ∃ e : T ∧ T,
                         O nj (BuildTruncType _ (fst e = snd e)))
                   (π : fst (pr1 x0) = snd (pr1 x0)),
                   O_unit nj
                     (BuildTruncType _ (fst (pr1 x0) = snd (pr1 x0))) π = 
                   pr2 x0, pr1 (pr2 q)))). clear sect.
    rewrite retr.
    unfold ap10, path_forall; rewrite eisretr. reflexivity.
  Defined.

  Definition nj_paths_separated (T:TruncType (n.+1))
    : (forall x y:T, IsSubu n nj (BuildTruncType _ (x=y))) -> separated T.
  Proof.
    intros H F χ f g.
    refine (isequiv_adjointify _ _ _ _).
    - intro p. apply path_forall; intro x.
      specialize (H (f x) (g x)).
      unfold E_to_χ_map in *.
      generalize (equiv_path _ _ (dense_eq χ x) (x;1)).
      apply (O_rec n nj (χ x) (Build_subuniverse_Type n nj (BuildTruncType _ (f x=g x)) _)).
      intro w.
      exact (ap10 p (x;w)).
    - intro p. unfold E_to_χ_map in *; cbn in *.
      rewrite (path_forall_precompose (∃ x : F, χ x) F T pr1 _ _ (λ x : F,
         O_rec n nj (χ x)
           {| st := BuildTruncType _ (f x = g x); subu_struct := H (f x) (g x) |}
           (λ w : χ x, ap10 p (x; w)) (transport idmap (dense_eq χ x) (x; 1)))).
      apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
      unfold path_forall; rewrite eisretr.
      apply path_forall; intro x.
      pose (r:= ap10 (dense_diag χ x (x;1)) (x;1)). 
      unfold incl_Aeq_Eeq in r; cbn in r.
      rewrite r; clear r.
      pose (r := λ P Q f, ap10 (O_rec_retr n nj P Q f)).
      rewrite r. reflexivity.
    - intro p.
      apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
      unfold path_forall; rewrite eisretr.
      apply path_forall; intro x. simpl.
      generalize (equiv_path _ _ (dense_eq χ x) (x;1)).
      transparent assert (sh : (subuniverse_Type nj)).
      { refine (Build_subuniverse_Type n nj
                 (BuildTruncType _ (O_rec n nj (χ x)
                             {| st := BuildTruncType _ (f x = g x); subu_struct := H (f x) (g x) |}
                             (λ w : χ x, ap10 (ap (E_to_χ_map T χ) p) (x; w))
                             (transport idmap (dense_eq χ x) (x; 1)) = apD10 p x)) _).
        apply istrunc_paths.
        apply istrunc_paths. apply trunc_succ. apply istrunc_trunctype_type.
        assert (X: IsSubu n nj (BuildTruncType _ (f x = g x))). apply H.
        pose (pp:= subuniverse_paths n nj (Build_subuniverse_Type n nj (BuildTruncType _ (f x=g x)) _)
             (O_rec n nj (χ x)
                         {|
                         st := {|
                               trunctype_type := f x = g x;
                               istrunc_trunctype_type := istrunc_paths _ 
                                                  (f x) (g x) |};
                         subu_struct := H (f x) (g x) |}
                         (λ w : χ x, ap10 (ap (E_to_χ_map T χ) p) (x; w))
                         (transport idmap (dense_eq χ x) (x; 1)))
             (apD10 p x)).

        match goal with
        |[pp: IsSubu _ _ {| trunctype_type := _; istrunc_trunctype_type := ?XX|} |- IsSubu _ _ {| trunctype_type := _; istrunc_trunctype_type := ?YY|}]
           => assert (rr: XX = YY) by apply path_ishprop
        end.
        destruct rr. exact pp. }
      apply (O_rec n nj (χ x) sh).
      unfold sh; clear sh; cbn.
      intro w.
      pose (r:= ap10 (dense_diag χ (x;w) ((x;w);1)) ((x;w);1)).
      unfold incl_Aeq_Eeq in r; cbn in r.
      rewrite r; clear r.
      pose (r := λ P Q f, ap10 (O_rec_retr n nj P Q f)).
      rewrite r.
      unfold E_to_χ_map.
      apply (ap10_ap_precompose pr1 p (x; w)).
  Defined.

  Definition Omono (A B:TruncType (trunc_S n)) (f: A -> B)
    := forall x y:A, IsEquiv (function_lift n nj (BuildTruncType _ (x=y)) (BuildTruncType _ (f x=f y)) (ap (x:=x) (y:=y) f)).

  Definition Oepi (A B:TruncType (trunc_S n)) (f: A -> B)
    := forall b:B, (O nj (@BuildTruncType _ (Trunc -1 (hfiber f b)) (@trunc_leq -1 n tt _ _))).

End Definitions.