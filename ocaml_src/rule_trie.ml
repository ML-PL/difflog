(* Difflog RuleTrie: hierarchical trie organizing rules by body literals.
   Corresponds to qd/evaluator/RuleTrie.scala

   Rules are inserted into a trie keyed by their body literals (sorted).
   Shared literal prefixes are collapsed, so extending assignments through
   the trie avoids redundant work when multiple rules share body literals.
*)

open Base

(* ═══════════════════════════════════════════════════════════════════════ *)
(* RuleTrie type                                                          *)
(* ═══════════════════════════════════════════════════════════════════════ *)

module LiteralMap = Map.Make(struct
  type t = literal
  let compare = compare_literal
end)

type t = {
  leaves: rule list;            (* rules whose body is fully consumed *)
  children: t LiteralMap.t;     (* sub-tries keyed by next body literal *)
  num_rules: int;
  num_literals: int;            (* distinct literal nodes in this sub-trie *)
  total_literals: int;          (* sum of body lengths of all rules *)
  variables: VariableSet.t;     (* all variables mentioned in this sub-trie *)
}

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Construction                                                           *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let empty = {
  leaves = [];
  children = LiteralMap.empty;
  num_rules = 0;
  num_literals = 0;
  total_literals = 0;
  variables = VariableSet.empty;
}

(* Compute variables from a trie node *)
let compute_variables leaves children =
  let leaf_vars = List.fold_left (fun acc rule ->
    VariableSet.union acc
      (VariableSet.of_list (literal_variables rule.rule_head))
  ) VariableSet.empty leaves in
  let child_vars = LiteralMap.fold (fun lit child acc ->
    let lv = VariableSet.of_list (literal_variables lit) in
    VariableSet.union acc (VariableSet.union lv child.variables)
  ) children VariableSet.empty in
  VariableSet.union leaf_vars child_vars

(* Add a single rule to the trie.
   Body literals are sorted by their string representation for canonical ordering. *)
let add trie rule =
  let sorted_body =
    Array.to_list rule.rule_body
    |> List.sort (fun l1 l2 ->
      String.compare (literal_to_string l1) (literal_to_string l2))
  in
  let rec insert remaining t =
    match remaining with
    | [] ->
      let new_leaves = rule :: t.leaves in
      let vars = compute_variables new_leaves t.children in
      { t with
        leaves = new_leaves;
        num_rules = t.num_rules + 1;
        variables = vars }
    | lit :: rest ->
      let sub = match LiteralMap.find_opt lit t.children with
        | Some s -> s
        | None -> empty
      in
      let new_sub = insert rest sub in
      let new_children = LiteralMap.add lit new_sub t.children in
      let vars = compute_variables t.leaves new_children in
      let num_lits = LiteralMap.fold (fun _ child acc ->
        1 + child.num_literals + acc
      ) new_children 0 in
      let total_lits = LiteralMap.fold (fun _ child acc ->
        child.total_literals + child.num_rules + acc
      ) new_children 0 in
      { t with
        children = new_children;
        num_rules = t.num_rules + 1;
        num_literals = num_lits;
        total_literals = total_lits;
        variables = vars }
  in
  insert sorted_body trie

(* Build a trie from a list of rules *)
let of_rules rules =
  List.fold_left add empty rules

(* Iterate over all rules in the trie *)
let rec iter f trie =
  List.iter f trie.leaves;
  LiteralMap.iter (fun _ child -> iter f child) trie.children
