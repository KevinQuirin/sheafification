(* -*- mode: coq; mode: visual-line -*- *)

(** * Truncations of types, in all dimensions. *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations.
Require Import equivalence.

Generalizable Variables A X n.

Definition squash := Trunc -1.

Definition Truncation_on_eq : forall A (x y : A) n, 
                                Trunc n (x = y) = (tr (n := trunc_S n) x = tr (n := trunc_S n) y). Admitted.  

Definition squash_extensionality  (T T' : Type) : 
  (T <-> T') -> tr (n := -1) T = tr T'.
Admitted.
