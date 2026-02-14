(* Difflog Base Types
   Core Datalog types corresponding to qd/base.scala
*)

(* Domain: a named type for tuple positions *)
type domain = { d_name: string }

(* Constant: a value in some domain *)
type constant = { c_name: string; c_domain: domain }

(* Variable: a placeholder in rules *)
type variable = { v_name: string; v_domain: domain }

(* Parameter: either a constant or variable *)
type parameter = Const of constant | Var of variable

(* DTuple: a tuple of constants *)
type dtuple = constant array

(* Relation: a named predicate with typed signature *)
type relation = { r_name: string; r_signature: domain array }

(* Literal: a relation applied to parameters, e.g., path(X, Y) *)
type literal = { l_relation: relation; l_fields: parameter array }

(* Lineage: tracks provenance of derived facts *)
type lineage = Empty | Token of string | And of lineage * lineage

(* Rule: lineage + head literal + body literals *)
type rule = { rule_lineage: lineage; rule_head: literal; rule_body: literal array }

(* ============================================================================
   Array Comparison Helpers (compatible with OCaml 4.14)
   ============================================================================ *)

let array_compare cmp a1 a2 =
  let len1 = Array.length a1 and len2 = Array.length a2 in
  let c = compare len1 len2 in
  if c <> 0 then c
  else
    let rec go i =
      if i >= len1 then 0
      else
        let c = cmp a1.(i) a2.(i) in
        if c <> 0 then c else go (i + 1)
    in
    go 0

let array_for_all2 f a1 a2 =
  let len = Array.length a1 in
  if Array.length a2 <> len then false
  else
    let rec go i =
      if i >= len then true
      else if f a1.(i) a2.(i) then go (i + 1)
      else false
    in
    go 0

(* ============================================================================
   Comparison Functions
   ============================================================================ *)

let compare_domain d1 d2 = String.compare d1.d_name d2.d_name

let compare_constant c1 c2 =
  let cmp_domain = compare_domain c1.c_domain c2.c_domain in
  if cmp_domain <> 0 then cmp_domain else String.compare c1.c_name c2.c_name

let compare_variable v1 v2 =
  let cmp_domain = compare_domain v1.v_domain v2.v_domain in
  if cmp_domain <> 0 then cmp_domain else String.compare v1.v_name v2.v_name

let compare_relation r1 r2 =
  let cmp_name = String.compare r1.r_name r2.r_name in
  if cmp_name <> 0 then cmp_name else
  array_compare compare_domain r1.r_signature r2.r_signature

let compare_dtuple dt1 dt2 =
  array_compare compare_constant dt1 dt2

(* Parameter comparison *)
let compare_parameter p1 p2 = match p1, p2 with
  | Const c1, Const c2 -> compare_constant c1 c2
  | Var v1, Var v2 -> compare_variable v1 v2
  | Const _, Var _ -> -1
  | Var _, Const _ -> 1

(* Literal comparison *)
let compare_literal lit1 lit2 =
  let cmp_rel = compare_relation lit1.l_relation lit2.l_relation in
  if cmp_rel <> 0 then cmp_rel else
  array_compare compare_parameter lit1.l_fields lit2.l_fields

(* Lineage comparison *)
let rec compare_lineage l1 l2 = match l1, l2 with
  | Empty, Empty -> 0
  | Token t1, Token t2 -> String.compare t1 t2
  | And (a1, b1), And (a2, b2) ->
    let cmp_l = compare_lineage a1 a2 in
    if cmp_l <> 0 then cmp_l else compare_lineage b1 b2
  | Empty, _ -> -1
  | _, Empty -> 1
  | Token _, And _ -> -1
  | And _, Token _ -> 1

(* ============================================================================
   Ordered Modules (for Map/Set)
   ============================================================================ *)

module DomainOrd = struct
  type t = domain
  let compare = compare_domain
end

module ConstantOrd = struct
  type t = constant
  let compare = compare_constant
end

module VariableOrd = struct
  type t = variable
  let compare = compare_variable
end

module RelationOrd = struct
  type t = relation
  let compare = compare_relation
end

module DTupleOrd = struct
  type t = dtuple
  let compare = compare_dtuple
end

module ParameterOrd = struct
  type t = parameter
  let compare = compare_parameter
end

(* ============================================================================
   Map and Set Modules
   ============================================================================ *)

module DomainMap = Map.Make(DomainOrd)
module DomainSet = Set.Make(DomainOrd)

module ConstantMap = Map.Make(ConstantOrd)
module ConstantSet = Set.Make(ConstantOrd)

module VariableMap = Map.Make(VariableOrd)
module VariableSet = Set.Make(VariableOrd)

module RelationMap = Map.Make(RelationOrd)
module RelationSet = Set.Make(RelationOrd)

module DTupleSet = Set.Make(DTupleOrd)
module DTupleMap = Map.Make(DTupleOrd)

(* ============================================================================
   Key Functions
   ============================================================================ *)

(* Extract domain from a parameter *)
let param_domain = function
  | Const c -> c.c_domain
  | Var v -> v.v_domain

(* Extract all variables from a literal *)
let literal_variables lit =
  Array.to_list lit.l_fields
  |> List.filter_map (function
    | Var v -> Some v
    | Const _ -> None)

(* Extract all variables from a rule's body *)
let rule_body_variables rule =
  Array.to_list rule.rule_body
  |> List.concat_map literal_variables

(* Get arity of a relation *)
let relation_arity rel = Array.length rel.r_signature

(* Get signature from a dtuple *)
let dtuple_signature dt =
  Array.map (fun c -> c.c_domain) dt

(* ============================================================================
   String Representations
   ============================================================================ *)

let parameter_to_string = function
  | Const c -> c.c_name
  | Var v -> v.v_name

let literal_to_string lit =
  let params = Array.to_list lit.l_fields
    |> List.map parameter_to_string
    |> String.concat ", " in
  Printf.sprintf "%s(%s)" lit.l_relation.r_name params

let rec lineage_to_string = function
  | Empty -> "∅"
  | Token t -> t
  | And (l1, l2) ->
    Printf.sprintf "(%s ⊗ %s)" (lineage_to_string l1) (lineage_to_string l2)

let dtuple_to_string dt =
  let strs = Array.to_list dt |> List.map (fun c -> c.c_name) in
  "(" ^ String.concat ", " strs ^ ")"

let rule_to_string rule =
  let body_str = Array.to_list rule.rule_body
    |> List.map literal_to_string
    |> String.concat ", " in
  let head_str = literal_to_string rule.rule_head in
  let lineage_str = lineage_to_string rule.rule_lineage in
  Printf.sprintf "[%s] %s :- %s" lineage_str head_str body_str

(* ============================================================================
   Variable Renaming
   ============================================================================ *)

let literal_rename lit f =
  let new_fields = Array.map (function
    | Var v -> Var (f v)
    | Const c -> Const c) lit.l_fields in
  { lit with l_fields = new_fields }

(* ============================================================================
   Rule Analysis: Valency
   ============================================================================ *)

(* Compute the valency of a split of the rule body.
   Valency is the size of the intersection of left variables and
   (right variables ∪ head variables).

   The rule_valency function computes the maximum valency across all possible
   splits of the body literals into left and right portions.
*)

let rule_valency head body =
  let head_vars = VariableSet.of_list (literal_variables head) in
  let body_len = Array.length body in

  if body_len = 0 then 0 else

  let compute_at_split split_idx =
    let left_vars = ref VariableSet.empty in
    let right_vars = ref VariableSet.empty in

    Array.iteri (fun i lit ->
      let lit_vars = VariableSet.of_list (literal_variables lit) in
      if i < split_idx then
        left_vars := VariableSet.union !left_vars lit_vars
      else
        right_vars := VariableSet.union !right_vars lit_vars
    ) body;

    let right_and_head = VariableSet.union !right_vars head_vars in
    VariableSet.cardinal (VariableSet.inter !left_vars right_and_head)
  in

  let max_val = ref 0 in
  for i = 0 to body_len do
    max_val := max !max_val (compute_at_split i)
  done;
  !max_val

(* ============================================================================
   Rule Normalization
   ============================================================================ *)

(* Canonically rename variables to v0, v1, ... and sort body by valency *)
let rule_normalize rule =
  (* Collect all variables in the rule *)
  let head_vars = literal_variables rule.rule_head in
  let body_vars = List.concat_map literal_variables (Array.to_list rule.rule_body) in
  let all_vars = head_vars @ body_vars in
  let unique_vars = VariableSet.to_list (VariableSet.of_list all_vars) in

  (* Create mapping from old variables to new canonical names *)
  let var_map =
    List.mapi (fun idx v ->
      let new_var = { v with v_name = Printf.sprintf "v%d" idx } in
      (v, new_var)
    ) unique_vars
    |> List.fold_left (fun acc (old_v, new_v) ->
      VariableMap.add old_v new_v acc
    ) VariableMap.empty
  in

  let rename_func v = try VariableMap.find v var_map with Not_found -> v in

  (* Rename head and body *)
  let new_head = literal_rename rule.rule_head rename_func in
  let new_body = Array.map (fun lit -> literal_rename lit rename_func) rule.rule_body in

  (* Sort body by valency (descending) *)
  let body_with_valency = Array.mapi (fun i lit ->
    (lit, rule_valency new_head (Array.sub new_body 0 i))
  ) new_body in

  Array.sort (fun (_, v1) (_, v2) -> compare v2 v1) body_with_valency;

  let sorted_body = Array.map fst body_with_valency in

  { rule with rule_head = new_head; rule_body = sorted_body }
