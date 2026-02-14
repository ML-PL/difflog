(* Difflog Evaluators: Naive and Semi-naive fixed-point evaluation
   Corresponds to qd/evaluator/NaiveEvaluator.scala, SeminaiveEvaluator.scala
*)

open Base
open Value
open Instance

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Shared evaluation utilities                                             *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(* Extend a single assignment with a literal match against a tuple.
   For each field in the literal:
   - If Var v: check if already bound → must match; if unbound → bind it
   - If Const c: must equal the corresponding tuple element
   Returns None if the binding is inconsistent.
*)
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

(* Scale an assignment's score by an FValue *)
let scale_asn (asn : FValue.t assignment) (factor : FValue.t) : FValue.t assignment =
  assignment_scale ~times:FValue.times asn factor

(* Extend a list of assignments against all matching tuples for a literal *)
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

(* Collapse assignments: project to relevant variables,
   then group by bindings key and take max (plus) of scores *)
let collapse_assignments (relevant_vars : VariableSet.t)
    (asns : FValue.t assignment list) : FValue.t assignment list =
  let projected = List.map (fun a -> assignment_project a relevant_vars) asns in
  (* Group by binding key, using plus (max) to aggregate scores *)
  let table : (string, FValue.t assignment) Hashtbl.t = Hashtbl.create 64 in
  List.iter (fun a ->
    let key = assignment_bindings_key a in
    match Hashtbl.find_opt table key with
    | Some existing ->
      let merged_score = FValue.plus existing.score a.score in
      Hashtbl.replace table key { a with score = merged_score }
    | None ->
      Hashtbl.replace table key a
  ) projected;
  Hashtbl.fold (fun _ asn acc -> asn :: acc) table []

(* Get the tuple for the head of a rule from an assignment *)
let head_tuple (asn : FValue.t assignment) (lit : literal) : dtuple =
  Array.map (fun p ->
    match p with
    | Var v ->
      (match assignment_get asn v with
       | Some c -> c
       | None -> failwith "head_tuple: unbound variable")
    | Const c -> c
  ) lit.l_fields

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Naive Evaluator                                                         *)
(* ═══════════════════════════════════════════════════════════════════════ *)

module NaiveEvaluator = struct

  (* Apply one rule: compute all derivable (relation, tuple, value) triples *)
  let rule_consequence (rule : rule) (pos : string -> FValue.t)
      (cfg : FValue.t config) : (relation * (dtuple * FValue.t) list) =
    let body = Array.to_list rule.rule_body in

    (* Start with a single empty assignment, score = one *)
    let initial = [assignment_empty ~one:FValue.one] in

    let rec process_body asns remaining_body =
      match remaining_body with
      | [] -> asns
      | lit :: rest ->
        let extended = extend_assignments lit cfg asns in
        (* Collapse: keep only variables needed by head + remaining body *)
        let head_vars = VariableSet.of_list (literal_variables rule.rule_head) in
        let remaining_vars = List.fold_left (fun acc l ->
          VariableSet.union acc (VariableSet.of_list (literal_variables l))
        ) head_vars rest in
        let collapsed = collapse_assignments remaining_vars extended in
        process_body collapsed rest
    in

    let final_asns = process_body initial body in

    (* Multiply each assignment's score by the rule's weight *)
    let vrule = eval_lineage rule.rule_lineage pos in
    let new_tuples = List.map (fun asn ->
      let scaled = scale_asn asn vrule in
      (head_tuple scaled rule.rule_head, scaled.score)
    ) final_asns in

    (rule.rule_head.l_relation, new_tuples)

  let eval (rules : rule list) (pos : string -> FValue.t)
      (edb : FValue.t config) : FValue.t config =
    let rec fixed_point cfg iteration =
      if iteration > 100 then cfg
      else
        let cfg_ref = ref cfg in
        let any_changed = ref false in
        List.iter (fun rule ->
          let (rel, new_tuples) = rule_consequence rule pos !cfg_ref in
          List.iter (fun (tuple, value) ->
            if FValue.nonzero value then begin
              let inst = config_get ~zero:FValue.zero !cfg_ref rel in
              let old_val = instance_get ~zero:FValue.zero inst tuple in
              let new_val = FValue.plus old_val value in
              if FValue.gt new_val old_val then begin
                let new_inst = instance_add ~zero:FValue.zero
                    ~plus:FValue.plus ~gt:FValue.gt inst tuple new_val in
                cfg_ref := RelationMap.add rel new_inst !cfg_ref;
                any_changed := true
              end
            end
          ) new_tuples
        ) rules;
        if !any_changed then
          fixed_point !cfg_ref (iteration + 1)
        else
          !cfg_ref
    in
    fixed_point edb 0
end

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Semi-naive Evaluator                                                    *)
(* ═══════════════════════════════════════════════════════════════════════ *)

module SeminaiveEvaluator = struct

  (* Apply rule with one body literal sourced from delta *)
  let rule_consequence_with_delta (rule : rule) (pos : string -> FValue.t)
      (cfg : FValue.t config) (delta : FValue.t config)
      (delta_lit_index : int) : (relation * (dtuple * FValue.t) list) =
    let body = Array.to_list rule.rule_body in

    let initial = [assignment_empty ~one:FValue.one] in

    let rec process_body asns remaining body_index =
      match remaining with
      | [] -> asns
      | lit :: rest ->
        let source = if body_index = delta_lit_index then delta else cfg in
        let extended = extend_assignments lit source asns in

        let head_vars = VariableSet.of_list (literal_variables rule.rule_head) in
        let remaining_vars = List.fold_left (fun acc l ->
          VariableSet.union acc (VariableSet.of_list (literal_variables l))
        ) head_vars rest in
        let collapsed = collapse_assignments remaining_vars extended in
        process_body collapsed rest (body_index + 1)
    in

    let final_asns = process_body initial body 0 in

    let vrule = eval_lineage rule.rule_lineage pos in
    let new_tuples = List.map (fun asn ->
      let scaled = scale_asn asn vrule in
      (head_tuple scaled rule.rule_head, scaled.score)
    ) final_asns in

    (rule.rule_head.l_relation, new_tuples)

  let eval (rules : rule list) (pos : string -> FValue.t)
      (edb : FValue.t config) : FValue.t config =
    let rec fixed_point cfg delta_curr iteration =
      let has_changes = config_non_empty_support ~nonzero:FValue.nonzero delta_curr in
      if not has_changes || iteration > 100 then cfg
      else
        let delta_next_ref = ref config_empty in
        let cfg_ref = ref cfg in

        List.iter (fun rule ->
          let body_len = Array.length rule.rule_body in
          for delta_lit_idx = 0 to body_len - 1 do
            let (rel, new_tuples) = rule_consequence_with_delta
                rule pos !cfg_ref delta_curr delta_lit_idx in
            List.iter (fun (tuple, value) ->
              if FValue.nonzero value then begin
                let inst = config_get ~zero:FValue.zero !cfg_ref rel in
                let old_val = instance_get ~zero:FValue.zero inst tuple in
                let new_val = FValue.plus old_val value in
                if FValue.gt new_val old_val then begin
                  let new_inst = instance_add ~zero:FValue.zero
                      ~plus:FValue.plus ~gt:FValue.gt inst tuple new_val in
                  cfg_ref := RelationMap.add rel new_inst !cfg_ref;

                  let dinst = config_get ~zero:FValue.zero !delta_next_ref rel in
                  let old_delta = instance_get ~zero:FValue.zero dinst tuple in
                  let new_delta = FValue.plus old_delta value in
                  let new_dinst = instance_add ~zero:FValue.zero
                      ~plus:FValue.plus ~gt:FValue.gt dinst tuple new_delta in
                  delta_next_ref := RelationMap.add rel new_dinst !delta_next_ref
                end
              end
            ) new_tuples
          done
        ) rules;

        fixed_point !cfg_ref !delta_next_ref (iteration + 1)
    in
    fixed_point edb edb 0
end
