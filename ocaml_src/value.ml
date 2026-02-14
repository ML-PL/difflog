(* Difflog Value Semantics
   Semiring abstraction and FValue (Viterbi semiring with lineage)
*)

open Base

(* ============================================================================
   Semiring Module Type
   ============================================================================ *)

module type SEMIRING = sig
  type t
  val zero : t
  val one : t
  val plus : t -> t -> t
  val times : t -> t -> t
  val leq : t -> t -> bool
  val gt : t -> t -> bool
  val nonzero : t -> bool
  val to_string : t -> string
end

(* ============================================================================
   FValue: Viterbi Semiring with Lineage
   ============================================================================ *)

(* FValue represents a fact with:
   - v: probability value in [0, 1]
   - l: lineage tracking provenance

   NOTE: We do NOT seal this module with `: SEMIRING` because other modules
   need access to the record fields {v; l} and the `make` constructor.
   The module still satisfies the SEMIRING signature structurally.
*)
module FValue = struct
  type t = { v: float; l: lineage }

  let make v l = { v; l }

  let zero = { v = 0.0; l = Empty }
  let one = { v = 1.0; l = Empty }

  let plus a b = if a.v >= b.v then a else b
  let times a b = { v = a.v *. b.v; l = Lineage.mul a.l b.l }

  let leq a b = a.v <= b.v
  let gt a b = a.v > b.v
  let nonzero t = t.v > 0.0

  let to_string t = Printf.sprintf "%.6f" t.v
end

(* ============================================================================
   Lineage Evaluation
   ============================================================================ *)

let eval_lineage (lin : lineage) (pos : string -> FValue.t) : FValue.t =
  let rec go = function
    | Empty -> FValue.one
    | Token t -> pos t
    | And (l1, l2) -> FValue.times (go l1) (go l2)
  in
  go lin
