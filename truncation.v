(* -*- mode: coq; mode: visual-line -*- *)

(** * Truncations of types, in all dimensions. *)

Require Export Utf8_core.
Require Import HoTT HoTT.hit.Truncations.
Require Import path equiv.

Generalizable Variables A X n.

Definition squash := Truncation minus_one.

Definition Truncation_on_eq : forall A (x y : A) n, 
                                Truncation n (x = y) = (truncation_incl (n := trunc_S n) x = truncation_incl (n := trunc_S n) y). Admitted.  

Definition squash_extensionality  (T T' : Type) : 
  (T <-> T') -> truncation_incl (n := minus_one) T = truncation_incl T'.
Admitted.
