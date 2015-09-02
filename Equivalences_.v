(* -*- mode: coq; mode: visual-line -*- *)
(** * Equivalences *)

Require Import Overture PathGroupoids.
Local Open Scope path_scope.

Generalizable Variables A B C f g h.

Definition moveR_equiv_pM `{Funext} `{IsEquiv A B g} `(f:B -> C) `(h:A -> C)
  : f o g = h -> f = h o g^-1
  := fun p => (path_forall _ _ (fun x => ap f (eisretr g x)))^
              @ (ap (fun u => u o g^-1) p).

Definition moveR_equiv_pV `{Funext} `{IsEquiv B A g} `(f:B -> C) `(h:A -> C)
  : f o g^-1 = h -> f = h o g
  := fun p => (path_forall _ _ (fun x => ap f (eissect g x)))^
              @ (ap (fun u => u o g) p).

Definition moveR_equiv_Mp `{Funext} `{IsEquiv B C f} `(g:A -> B) `(h:A -> C)
  : f o g = h -> g = f^-1 o h
  := fun p => (path_forall _ _ (fun x => eissect f (g x)))^
              @ (ap (fun u => f^-1 o u) p).

Definition moveR_equiv_Vp `{Funext} `{IsEquiv C B f} `(g:A -> B) `(h:A -> C)
  : f^-1 o g = h -> g = f o h
  := fun p => (path_forall _ _ (fun x => eisretr f (g x)))^
              @ (ap (fun u => f o u) p).

Definition moveL_equiv_pM `{Funext} `{IsEquiv B A g} `(f:B -> C) `(h:A -> C)
  : f = h o g -> f o g^-1 = h
  := fun p => (ap (fun u => u o g^-1) p)
                @ (path_forall _ _ (fun x => ap h (eisretr g x))).

Definition moveL_equiv_pV `{Funext} `{IsEquiv A B g} `(f:B -> C) `(h:A -> C)
  : f = h o g^-1 -> f o g = h
  := fun p => (ap (fun u => u o g) p)
                @ (path_forall _ _ (fun x => ap h (eissect g x))).

Definition moveL_equiv_Mp `{Funext} `{IsEquiv A C h} `(g:B -> A) `(f:B -> C)
  : f = h o g -> h^-1 o f = g
  := fun p => (ap (fun u => h^-1 o u) p)
                @ (path_forall _ _ (fun x => (eissect h (g x)))).

Definition moveL_equiv_Vp `{Funext} `{IsEquiv C A h} `(g:B -> A) `(f:B -> C)
  : f = h^-1 o g -> h o f = g
  := fun p => (ap (fun u => h o u) p)
                @ (path_forall _ _ (fun x => (eisretr h (g x)))).
