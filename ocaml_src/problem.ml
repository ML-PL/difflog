(* Difflog Problem Specification
   Corresponds to qd/problem/Problem.scala

   A Problem encapsulates the complete specification for Datalog rule synthesis:
   - Relations (input/invented/output)
   - Training data (EDB facts + expected IDB results)
   - Token weight vector (pos)
   - Candidate rules

   The Problem type is immutable: all "modification" functions return new
   Problem values (functional update style).
*)

open Base
open Lineage
open Value
open Instance

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Problem Type                                                            *)
(* ═══════════════════════════════════════════════════════════════════════ *)

type problem = {
  input_rels: RelationSet.t;
  invented_rels: RelationSet.t;
  output_rels: RelationSet.t;

  (* Discrete EDB/IDB: relation -> set of tuples *)
  discrete_edb: DTupleSet.t RelationMap.t;
  discrete_idb: DTupleSet.t RelationMap.t;

  (* Token weight vector: token_name -> weight *)
  pos: Token_vec.t;

  (* Candidate rules *)
  rules: rule list;

  (* Domain to constants mapping *)
  dom2values: ConstantSet.t DomainMap.t;

  (* All possible output tuples (for noise injection) *)
  all_out_tuples: DTupleSet.t RelationMap.t;
}

(* ─────────────────────────────────────────────────────────────────────── *)
(* Empty Problem                                                           *)
(* ─────────────────────────────────────────────────────────────────────── *)

let empty : problem = {
  input_rels = RelationSet.empty;
  invented_rels = RelationSet.empty;
  output_rels = RelationSet.empty;
  discrete_edb = RelationMap.empty;
  discrete_idb = RelationMap.empty;
  pos = TokenMap.empty;
  rules = [];
  dom2values = DomainMap.empty;
  all_out_tuples = RelationMap.empty;
}

(* ═══════════════════════════════════════════════════════════════════════ *)
(* 1. Relation Management                                                  *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(* Check if a relation is already known *)
let known_relation p rel =
  RelationSet.mem rel p.input_rels
  || RelationSet.mem rel p.invented_rels
  || RelationSet.mem rel p.output_rels

let is_new_relation p rel = not (known_relation p rel)

(* Find a relation by predicate *)
let find_rel p pred =
  let try_find s =
    RelationSet.fold (fun r acc ->
      match acc with Some _ -> acc | None -> if pred r then Some r else None
    ) s None
  in
  match try_find p.input_rels with
  | Some r -> Some r
  | None ->
    match try_find p.invented_rels with
    | Some r -> Some r
    | None -> try_find p.output_rels

(* Add input relation *)
let add_input_rel p rel =
  assert (is_new_relation p rel);
  { p with
    input_rels = RelationSet.add rel p.input_rels;
    discrete_edb = RelationMap.add rel DTupleSet.empty p.discrete_edb;
  }

(* Add invented relation *)
let add_invented_rel p rel =
  assert (is_new_relation p rel);
  { p with invented_rels = RelationSet.add rel p.invented_rels }

(* Add output relation *)
let add_output_rel p rel =
  assert (is_new_relation p rel);
  { p with
    output_rels = RelationSet.add rel p.output_rels;
    discrete_idb = RelationMap.add rel DTupleSet.empty p.discrete_idb;
  }

(* Add output relation and generate all possible tuples for that relation *)
let rec gen_tuples dom2vals sig_ k =
  if k <= 0 then [Array.make 0 { c_name = ""; c_domain = { d_name = "" } }]
  else
    let domain = sig_.(k - 1) in
    let values = match DomainMap.find_opt domain dom2vals with
      | Some vs -> ConstantSet.elements vs
      | None -> []
    in
    let partials = gen_tuples dom2vals sig_ (k - 1) in
    List.concat_map (fun v ->
      List.map (fun partial -> Array.append partial [|v|]) partials
    ) values

let add_output_rel_then_dump p rel =
  assert (is_new_relation p rel);
  let sig_ = rel.r_signature in
  let all_tuples = gen_tuples p.dom2values sig_ (Array.length sig_) in
  let tuple_set = List.fold_left (fun acc t -> DTupleSet.add t acc) DTupleSet.empty all_tuples in
  { p with
    output_rels = RelationSet.add rel p.output_rels;
    discrete_idb = RelationMap.add rel DTupleSet.empty p.discrete_idb;
    all_out_tuples = RelationMap.add rel tuple_set p.all_out_tuples;
  }

(* ═══════════════════════════════════════════════════════════════════════ *)
(* 2. Domain and Tuple Management                                         *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let add_dom2values p d2v =
  { p with dom2values = d2v }

(* Add EDB tuples *)
let add_edb_tuples p rts =
  let new_edb = List.fold_left (fun edb (rel, tuple) ->
    let existing = match RelationMap.find_opt rel edb with
      | Some s -> s
      | None -> failwith (Printf.sprintf "Undeclared relation %s" rel.r_name)
    in
    RelationMap.add rel (DTupleSet.add tuple existing) edb
  ) p.discrete_edb rts in
  { p with discrete_edb = new_edb }

(* Add IDB tuples *)
let add_idb_tuples p rts =
  let new_idb = List.fold_left (fun idb (rel, tuple) ->
    let existing = match RelationMap.find_opt rel idb with
      | Some s -> s
      | None -> failwith (Printf.sprintf "Undeclared relation %s" rel.r_name)
    in
    RelationMap.add rel (DTupleSet.add tuple existing) idb
  ) p.discrete_idb rts in
  { p with discrete_idb = new_idb }

(* ═══════════════════════════════════════════════════════════════════════ *)
(* 3. EDB/IDB as FValue Configs                                           *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(* Convert discrete tuples to an FValue instance *)
let discrete_tuples_to_instance (rel : relation) (tuples : DTupleSet.t) : FValue.t instance =
  let sig_ = Array.to_list rel.r_signature in
  let empty_inst = create_instance ~zero:FValue.zero sig_ in
  DTupleSet.fold (fun tuple inst ->
    instance_add ~zero:FValue.zero ~plus:FValue.plus ~gt:FValue.gt inst tuple FValue.one
  ) tuples empty_inst

(* Build config from the relation -> tuple_set map directly *)
let build_fvalue_config (rel_tuples : DTupleSet.t RelationMap.t) : FValue.t config =
  RelationMap.mapi (fun rel tuples ->
    discrete_tuples_to_instance rel tuples
  ) rel_tuples

let edb p = build_fvalue_config p.discrete_edb
let idb p = build_fvalue_config p.discrete_idb

(* ═══════════════════════════════════════════════════════════════════════ *)
(* 4. Token and Rule Management                                           *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let all_tokens p = Token_vec.key_set p.pos

let add_token p token_name value =
  if Token_vec.contains p.pos token_name then begin
    Printf.eprintf "Ignoring redeclaration of token %s\n%!" token_name;
    p
  end else
    { p with pos = TokenMap.add token_name value p.pos }

let add_rule p rule =
  assert (known_relation p rule.rule_head.l_relation);
  assert (Array.for_all (fun lit -> known_relation p lit.l_relation) rule.rule_body);
  { p with rules = rule :: p.rules }

let add_rules p new_rules =
  List.fold_left add_rule p new_rules

(* ═══════════════════════════════════════════════════════════════════════ *)
(* 5. Noise Injection (for robustness testing)                            *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let inject_noise p =
  (* Pick a random output relation *)
  let rels = RelationSet.elements p.output_rels in
  let rel = List.nth rels (Random.int (List.length rels)) in
  (* Pick a random tuple from all possible output tuples *)
  let all = match RelationMap.find_opt rel p.all_out_tuples with
    | Some ts -> DTupleSet.elements ts
    | None -> failwith "No all_out_tuples for relation"
  in
  let noise_tuple = List.nth all (Random.int (List.length all)) in
  let clean_idb = match RelationMap.find_opt rel p.discrete_idb with
    | Some ts -> ts
    | None -> DTupleSet.empty
  in
  let noisy_idb =
    if DTupleSet.mem noise_tuple clean_idb then
      DTupleSet.remove noise_tuple clean_idb
    else
      DTupleSet.add noise_tuple clean_idb
  in
  { p with discrete_idb = RelationMap.add rel noisy_idb p.discrete_idb }
