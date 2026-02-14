(* Difflog Lineage Operations
   Token and lineage manipulation utilities
*)

open Base

type token = string

(* ============================================================================
   Lineage Multiplication
   ============================================================================ *)

(* Lineage multiplication using And constructor, normalizing Empty *)
let mul l1 l2 = match l1, l2 with
  | Empty, l -> l
  | l, Empty -> l
  | _, _ -> And (l1, l2)

(* ============================================================================
   Lineage Flattening
   ============================================================================ *)

(* Convert lineage to flat list of tokens *)
let rec to_list = function
  | Empty -> []
  | Token t -> [t]
  | And (l1, l2) -> to_list l1 @ to_list l2

(* ============================================================================
   Token Set Operations
   ============================================================================ *)

module TokenOrd = struct
  type t = string
  let compare = String.compare
end

module TokenSet = Set.Make(TokenOrd)
module TokenMap = Map.Make(TokenOrd)

(* Extract unique token set from lineage *)
let token_set lineage =
  TokenSet.of_list (to_list lineage)

(* ============================================================================
   Token Multiset (Frequency Counting)
   ============================================================================ *)

(* Count token occurrences in lineage *)
let token_multiset lineage =
  List.fold_left (fun acc t ->
    let count = try TokenMap.find t acc with Not_found -> 0 in
    TokenMap.add t (count + 1) acc
  ) TokenMap.empty (to_list lineage)

(* ============================================================================
   String Representation
   ============================================================================ *)

(* Re-export string conversion from Base *)
let to_string = Base.lineage_to_string
