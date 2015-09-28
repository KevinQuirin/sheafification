Require Import Overture PathGroupoids.

Lemma transport2_is_ap  (A : Type) (Q : A -> Type) (x y : A) (p q : x = y) 
      (r : p = q) (z : Q x)
  : transport2 Q r z = ap (fun U => transport Q U z) r.
Proof.
  destruct r. reflexivity.
Defined.

Lemma concat_ap_Fpq (A B:Type) (a b:A) (c d e:B) (f: a = b -> c = d)
      (v:d = e)
      (u1 u2:a=b) (p:u1 = u2)
  : ap (fun u:a=b => f u @ v) p = whiskerR (ap f p) v.
Proof.
  destruct p; reflexivity.
Defined.

Lemma concat_ap_pFq (A B:Type) (a b:A) (d e c:B) (f: a = b -> e = c)
      (v:d = e)
      (u1 u2:a=b) (p:u1 = u2)
  : ap (fun u:a=b => v @ f u) p = whiskerL v (ap f p).
Proof.
  destruct p; reflexivity.
Defined.

Lemma whiskerL_1pp (A : Type) (x y z t: A) (p : x = y) (p':y=t) (q q' : t = z) 
        (r : q = q') 
    : whiskerL (p@p') r = (concat_pp_p _ _ _) @ whiskerL p (whiskerL p' r) @ (concat_p_pp _ _ _).
  Proof.
    destruct r, q, p, p'. reflexivity.
  Qed.

  Lemma whiskerL_LV (A : Type) (x y z: A) (p : x = y) (q q' : y = z) 
        (r : q = q')
    : whiskerL p r^ = (whiskerL p r)^.
  Proof.
    destruct r, q, p; reflexivity.
  Qed.
  

  Lemma concat_ap_FpFq_pp_p (A B:Type) (a b:A)
        (c d e f:B)
        (g: a = b -> e = f) (h: a = b -> c = d)
        (v:d = e)
        (u1 u2:a=b) (p:u1 = u2)
    : ap (fun u:a=b => (h u @ v) @ g u) p
      = ((concat_pp_p _ _ _) @ (whiskerR (ap h p) (v @ g u1) @ (concat_p_pp _ _ _))) @
         whiskerL (h u2 @ v) (ap g p).
  Proof.
    destruct p, u1, v; cbn.
    destruct (g idpath), (h idpath); reflexivity.
  Defined.

  Lemma concat_ap_FpFq_p_pp (A B:Type) (a b:A)
        (c d e f:B)
        (g: a = b -> e = f) (h: a = b -> c = d)
        (v:d = e)
        (u1 u2:a=b) (p:u1 = u2)
    : ap (fun u:a=b => h u @ (v @ g u)) p = 
      (whiskerR (ap h p) (v @ g u1) @ (concat_p_pp _ _ _)) @ (whiskerL (h u2 @ v) (ap g p) @ (concat_pp_p _ _ _)).
  Proof.
    destruct p, u1, v; cbn.
    destruct (g idpath), (h idpath); reflexivity.
  Defined.

  Lemma concat_ap_FFpq_p_pp (A B:Type) (a b:A)
        (c d e f:B)
        (g: a = b -> d = f) (h: a = b -> c = d)
        (v:f = e)
        (u1 u2:a=b) (p:u1 = u2)
    : ap (fun u:a=b => h u @ (g u @ v)) p = (concat_p_pp _ _ _) @ (whiskerR (ap h p @@ ap g p) v @ (concat_pp_p _ _ _)).
  Proof.
    destruct p, u1, v; cbn.
    destruct (g idpath), (h idpath); reflexivity.
  Defined.

  Lemma concat2_inv (A : Type) (x y z : A) (p p' : x = y) (q q' : y = z)
        (r:p=p') (s:q=q')
    : (r @@ s)^ = (r^ @@ s^).
  Proof.
    destruct r, s. reflexivity.
  Defined.
  
  Lemma concat2_p_pp (A : Type) (w x y z : A) (p p' : w = x) (q q' : x = y) (r r' : y = z)
        (s:p=p') (s':q=q') (s'':r=r')
    : s @@ (s' @@ s'') = (concat_p_pp _ _ _) @ (((s @@ s') @@ s'') @ (concat_pp_p _ _ _)).
  Proof.
    destruct s, s', s'', p, q, r; reflexivity.
  Defined.