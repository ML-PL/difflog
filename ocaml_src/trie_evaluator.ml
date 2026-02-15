(* Difflog Trie-based Evaluators
   Corresponds to qd/evaluator/TrieEvaluator.scala, TrieSemiEvaluator.scala

   These evaluators organize rules into a RuleTrie and process them
   by traversing the trie structure, extending assignments at each node.
   Shared body-literal prefixes are evaluated once, reducing redundant work.
*)

open Base
open Value
open Instance

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Shared: extend assignments (same logic as evaluator.ml)               *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let extend_assignment_with_lit (lit : literal) (tuple : dtuple)
    (asn : FValue.t assignment) : FValue.t assignment option =
  let n = Array.length lit.l_fields in
  let rec go i a =
    if i >= n then Some a
    else
      match lit.l_fields.(i) with
      | Var v ->
        (match assignment_get a v with
         | Some existing ->
           if compare_constant existing tuple.(i) = 0 then go (i+1) a
           else None
         | None ->
           (match assignment_extend a v tuple.(i) with
            | Some a' -> go (i+1) a'
            | None -> None))
      | Const c ->
        if compare_constant c tuple.(i) = 0 then go (i+1) a
        else None
  in
  go 0 asn

let scale_asn (asn : FValue.t assignment) (factor : FValue.t) : FValue.t assignment =
  assignment_scale ~times:FValue.times asn factor

(* Extend assignments against all matching tuples for a literal in a config *)
let extend_assignments (lit : literal) (cfg : FValue.t config)
    (asns : FValue.t assignment list) : FValue.t assignment list =
  List.concat_map (fun asn ->
    let filter = assignment_to_filter asn lit in
    let inst = config_get ~zero:FValue.zero cfg lit.l_relation in
    let matches = instance_filter ~nonzero:FValue.nonzero inst filter in
    List.filter_map (fun (tuple, score) ->
      match extend_assignment_with_lit lit tuple asn with
      | Some asn' -> Some (scale_asn asn' score)
      | None -> None
    ) matches
  ) asns

(* Get the head tuple from an assignment *)
let head_tuple (asn : FValue.t assignment) (lit : literal) : dtuple =
  Array.map (fun p ->
    match p with
    | Var v ->
      (match assignment_get asn v with
       | Some c -> c
       | None -> failwith "head_tuple: unbound variable")
    | Const c -> c
  ) lit.l_fields

(* Add derived tuples to a config, returning (new_config, whether_anything_changed) *)
let add_tuples (cfg : FValue.t config) (rel : relation)
    (new_tuples : (dtuple * FValue.t) list) : FValue.t config * bool =
  let inst = config_get ~zero:FValue.zero cfg rel in
  let changed = ref false in
  let new_inst = List.fold_left (fun acc (tuple, value) ->
    if FValue.nonzero value then begin
      let old_val = instance_get ~zero:FValue.zero acc tuple in
      let new_val = FValue.plus old_val value in
      if FValue.gt new_val old_val then begin
        changed := true;
        instance_add ~zero:FValue.zero ~plus:FValue.plus ~gt:FValue.gt
          acc tuple new_val
      end else acc
    end else acc
  ) inst new_tuples in
  (RelationMap.add rel new_inst cfg, !changed)

(* ═══════════════════════════════════════════════════════════════════════ *)
(* TrieEvaluator: Naive fixed-point using RuleTrie                       *)
(* ═══════════════════════════════════════════════════════════════════════ *)

module TrieEvaluator = struct

  (* Walk the trie, extending assignments at each literal node,
     and applying leaf rules to produce new tuples. *)
  let rec immediate_consequence (pos : string -> FValue.t)
      (cfg : FValue.t config) (changed : bool)
      (trie : Rule_trie.t) (asns : FValue.t assignment list)
    : FValue.t config * bool =
    let cfg_ref = ref cfg in
    let changed_ref = ref changed in

    (* Step 1: Process sub-tries — extend assignments through each literal *)
    Rule_trie.LiteralMap.iter (fun lit sub_trie ->
      let extended = extend_assignments lit !cfg_ref asns in
      let (new_cfg, new_changed) =
        immediate_consequence pos !cfg_ref !changed_ref sub_trie extended in
      cfg_ref := new_cfg;
      if new_changed then changed_ref := true
    ) trie.Rule_trie.children;

    (* Step 2: Process leaves — apply each rule to produce head tuples *)
    List.iter (fun rule ->
      let vrule = eval_lineage rule.rule_lineage pos in
      let new_tuples = List.map (fun asn ->
        let scaled = scale_asn asn vrule in
        (head_tuple scaled rule.rule_head, scaled.score)
      ) asns in
      let (new_cfg, new_changed) =
        add_tuples !cfg_ref rule.rule_head.l_relation new_tuples in
      cfg_ref := new_cfg;
      if new_changed then changed_ref := true
    ) trie.Rule_trie.leaves;

    (!cfg_ref, !changed_ref)

  let eval (rules : rule list) (pos : string -> FValue.t)
      (edb : FValue.t config) : FValue.t config =
    let trie = Rule_trie.of_rules rules in
    let initial_asns = [assignment_empty ~one:FValue.one] in
    let rec fixed_point cfg iteration =
      if iteration > 100 then cfg
      else
        let (new_cfg, changed) =
          immediate_consequence pos cfg false trie initial_asns in
        if changed then fixed_point new_cfg (iteration + 1)
        else new_cfg
    in
    fixed_point edb 0
end

(* ═══════════════════════════════════════════════════════════════════════ *)
(* TrieSemiEvaluator: Semi-naive fixed-point using RuleTrie              *)
(* ═══════════════════════════════════════════════════════════════════════ *)

module TrieSemiEvaluator = struct

  (* Walk the trie with semi-naive delta tracking.
     delta_done: whether we have already used the delta set for one literal.
     If not yet done, for each literal we extend from both full config
     (only if there are more literals below) and delta (marking delta_done). *)
  let rec immediate_consequence (pos : string -> FValue.t)
      (cfg : FValue.t config) (delta_curr : FValue.t config)
      (delta_next : FValue.t config ref)
      (trie : Rule_trie.t) (asns : FValue.t assignment list)
      (delta_done : bool) : FValue.t config =
    let cfg_ref = ref cfg in

    (* Step 1: Process sub-tries *)
    Rule_trie.LiteralMap.iter (fun lit sub_trie ->
      (* Extend with full config only if more literals below or delta already used *)
      if sub_trie.Rule_trie.num_literals > 0 || delta_done then begin
        let extended = extend_assignments lit !cfg_ref asns in
        cfg_ref := immediate_consequence pos !cfg_ref delta_curr
            delta_next sub_trie extended delta_done
      end;

      (* If delta not yet used, extend from delta and mark delta_done *)
      if not delta_done then begin
        let extended_delta = extend_assignments lit delta_curr asns in
        cfg_ref := immediate_consequence pos !cfg_ref delta_curr
            delta_next sub_trie extended_delta true
      end
    ) trie.Rule_trie.children;

    (* Step 2: Process leaves — only if delta has been used *)
    if delta_done then begin
      List.iter (fun rule ->
        let vrule = eval_lineage rule.rule_lineage pos in
        let new_tuples = List.map (fun asn ->
          let scaled = scale_asn asn vrule in
          (head_tuple scaled rule.rule_head, scaled.score)
        ) asns in
        let rel = rule.rule_head.l_relation in
        (* Add to config *)
        List.iter (fun (tuple, value) ->
          if FValue.nonzero value then begin
            let inst = config_get ~zero:FValue.zero !cfg_ref rel in
            let old_val = instance_get ~zero:FValue.zero inst tuple in
            let new_val = FValue.plus old_val value in
            if FValue.gt new_val old_val then begin
              let new_inst = instance_add ~zero:FValue.zero
                  ~plus:FValue.plus ~gt:FValue.gt inst tuple new_val in
              cfg_ref := RelationMap.add rel new_inst !cfg_ref;
              (* Also add to delta_next *)
              let dinst = config_get ~zero:FValue.zero !delta_next rel in
              let new_dinst = instance_add ~zero:FValue.zero
                  ~plus:FValue.plus ~gt:FValue.gt dinst tuple new_val in
              delta_next := RelationMap.add rel new_dinst !delta_next
            end
          end
        ) new_tuples
      ) trie.Rule_trie.leaves
    end;

    !cfg_ref

  let eval (rules : rule list) (pos : string -> FValue.t)
      (edb : FValue.t config) : FValue.t config =
    let trie = Rule_trie.of_rules rules in
    let initial_asns = [assignment_empty ~one:FValue.one] in
    let rec fixed_point cfg delta_curr iteration =
      let has_delta =
        config_non_empty_support ~nonzero:FValue.nonzero delta_curr in
      if not has_delta || iteration > 100 then cfg
      else
        let delta_next = ref config_empty in
        let new_cfg = immediate_consequence pos cfg delta_curr
            delta_next trie initial_asns false in
        fixed_point new_cfg !delta_next (iteration + 1)
    in
    fixed_point edb edb 0
end
