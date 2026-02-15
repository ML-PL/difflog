(* Difflog Main Entry Point
   CLI dispatcher for the OCaml reimplementation.

   Corresponds to qd/Main.scala

   Usage:
     difflog alps <data.d> <templates.tp> <learner> <evaluator> <scorer> <tgtLoss> <maxIters>

   Example:
     difflog alps path.d path.tp HybridAnnealingLearner SeminaiveEvaluator L2Scorer 0.01 1000
*)

open Base
open Lineage
open Value
open Instance
open Evaluator
open Scorer
open Learner
open Problem

(* ═══════════════════════════════════════════════════════════════════════ *)
(* File I/O                                                                *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let read_file filename =
  let ic = open_in filename in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.to_string s

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Evaluator Registry                                                      *)
(* ═══════════════════════════════════════════════════════════════════════ *)

type evaluator_fn = rule list -> (string -> FValue.t) -> FValue.t config -> FValue.t config

let get_evaluator name : evaluator_fn =
  match name with
  | "NaiveEvaluator" -> NaiveEvaluator.eval
  | "SeminaiveEvaluator" -> SeminaiveEvaluator.eval
  | "TrieEvaluator" -> Trie_evaluator.TrieEvaluator.eval
  | "TrieSemiEvaluator" -> Trie_evaluator.TrieSemiEvaluator.eval
  | _ -> failwith (Printf.sprintf "Unknown evaluator: %s" name)

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Learner Registry                                                        *)
(* ═══════════════════════════════════════════════════════════════════════ *)

type learner_fn =
  evaluator:evaluator_fn ->
  scorer:scorer ->
  rules:rule list ->
  output_rels:RelationSet.t ->
  ref_idb:FValue.t config ->
  discrete_idb:DTupleSet.t RelationMap.t ->
  all_tokens:TokenSet.t ->
  edb:FValue.t config ->
  tgt_loss:float ->
  max_iters:int ->
  state

let get_learner name : learner_fn =
  match name with
  | "NewtonRootLearner" -> newton_root_learn
  | "HybridAnnealingLearner" -> hybrid_annealing_learn
  | _ -> failwith (Printf.sprintf "Unknown learner: %s" name)

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Rule Printing                                                           *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let print_rules_with_weights (rules : rule list) (pos : Token_vec.t) =
  let weighted = List.map (fun rule ->
    let (fv : FValue.t) = eval_lineage rule.rule_lineage (Token_vec.apply pos) in
    (fv, rule)
  ) rules in
  let sorted = List.sort (fun ((fv1 : FValue.t), _) ((fv2 : FValue.t), _) ->
    compare fv2.v fv1.v
  ) weighted in
  List.iter (fun ((fv : FValue.t), rule) ->
    Printf.printf "  %.6f: %s\n" fv.v (rule_to_string rule)
  ) sorted

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Command: alps                                                           *)
(* Run Difflog in ALPS mode: parse data + templates, learn rules           *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let cmd_alps data_file template_file learner_name evaluator_name scorer_name
    tgt_loss max_iters =
  let data_str = read_file data_file in
  let template_str = read_file template_file in

  Printf.eprintf "Parsing ALPS problem from %s and %s...\n%!" data_file template_file;
  let problem = Alps_parser.parse data_str template_str in

  let evaluator = get_evaluator evaluator_name in
  let scorer = find_scorer scorer_name in
  let learn = get_learner learner_name in

  let edb_cfg = edb problem in
  let idb_cfg = idb problem in

  (* Print candidate rules before learning *)
  Printf.printf "// Candidate rules (%d):\n" (List.length problem.rules);
  print_rules_with_weights problem.rules problem.pos;
  Printf.printf "\n";

  Printf.eprintf "Starting learning with %s, %s, %s\n%!" learner_name evaluator_name scorer_name;
  Printf.eprintf "Target loss: %.6f, Max iterations: %d\n%!" tgt_loss max_iters;

  let result = learn
      ~evaluator
      ~scorer
      ~rules:problem.rules
      ~output_rels:problem.output_rels
      ~ref_idb:idb_cfg
      ~discrete_idb:problem.discrete_idb
      ~all_tokens:(all_tokens problem)
      ~edb:edb_cfg
      ~tgt_loss
      ~max_iters
  in

  (* Print results *)
  Printf.printf "\n// Achieved loss %.6f\n" result.loss;
  Printf.printf "// Learned rules (non-zero weight):\n";
  print_rules_with_weights
    (List.filter (fun rule ->
      FValue.nonzero (eval_lineage rule.rule_lineage (Token_vec.apply result.pos))
    ) problem.rules)
    result.pos

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Command: eval                                                           *)
(* Evaluate a problem with given evaluator (no learning)                  *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let cmd_eval data_file template_file evaluator_name =
  let data_str = read_file data_file in
  let template_str = read_file template_file in
  let problem = Alps_parser.parse data_str template_str in

  (* Print all candidate rules *)
  Printf.printf "// Candidate rules (%d):\n" (List.length problem.rules);
  print_rules_with_weights problem.rules problem.pos;
  Printf.printf "\n";

  let evaluator = get_evaluator evaluator_name in
  let edb_cfg = edb problem in
  let result = evaluator problem.rules (Token_vec.apply problem.pos) edb_cfg in

  (* Print derived tuples per output relation *)
  Printf.printf "// Derived tuples:\n";
  RelationSet.iter (fun rel ->
    let inst = config_get ~zero:FValue.zero result rel in
    let support = instance_support ~nonzero:FValue.nonzero inst in
    let sorted = List.sort (fun (_, (fv1 : FValue.t)) (_, (fv2 : FValue.t)) ->
      compare fv2.v fv1.v
    ) support in
    List.iter (fun (tuple, (fv : FValue.t)) ->
      let tuple_str = Array.to_list tuple
                      |> List.map (fun c -> c.c_name)
                      |> String.concat ", " in
      Printf.printf "  %.6f: %s(%s)\n" fv.v rel.r_name tuple_str
    ) sorted
  ) problem.output_rels

(* ═══════════════════════════════════════════════════════════════════════ *)
(* JSON Helpers                                                            *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let json_escape s =
  let buf = Buffer.create (String.length s) in
  String.iter (fun c ->
    match c with
    | '"' -> Buffer.add_string buf "\\\""
    | '\\' -> Buffer.add_string buf "\\\\"
    | '\n' -> Buffer.add_string buf "\\n"
    | '\t' -> Buffer.add_string buf "\\t"
    | c -> Buffer.add_char buf c
  ) s;
  Buffer.contents buf

let json_string s = Printf.sprintf "\"%s\"" (json_escape s)
let json_int n = string_of_int n
let json_float f = Printf.sprintf "%.6f" f
let json_bool b = if b then "true" else "false"

let json_list items = "[" ^ String.concat ", " items ^ "]"
let json_obj pairs =
  let fields = List.map (fun (k, v) ->
    Printf.sprintf "%s: %s" (json_string k) v
  ) pairs in
  "{" ^ String.concat ", " fields ^ "}"

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Command: bench                                                          *)
(* Like alps but outputs one JSON line to stdout with structured stats    *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let cmd_bench data_file template_file learner_name evaluator_name scorer_name
    tgt_loss max_iters =
  let test_name =
    Filename.chop_extension (Filename.basename data_file) in

  let data_str = read_file data_file in
  let template_str = read_file template_file in

  Printf.eprintf "bench: %s / %s ...\n%!" test_name evaluator_name;
  let problem = Alps_parser.parse data_str template_str in

  let n_input = RelationSet.cardinal problem.input_rels in
  let n_invented = RelationSet.cardinal problem.invented_rels in
  let n_output = RelationSet.cardinal problem.output_rels in
  let n_candidate_rules = List.length problem.rules in

  let evaluator = get_evaluator evaluator_name in
  let scorer = find_scorer scorer_name in
  let learn = get_learner learner_name in

  let edb_cfg = edb problem in
  let idb_cfg = idb problem in

  (* Sys.time() measures CPU time; close enough for single-threaded benchmarks *)
  let time_start = Sys.time () in

  let status = ref "ok" in
  let result =
    try
      learn
        ~evaluator
        ~scorer
        ~rules:problem.rules
        ~output_rels:problem.output_rels
        ~ref_idb:idb_cfg
        ~discrete_idb:problem.discrete_idb
        ~all_tokens:(all_tokens problem)
        ~edb:edb_cfg
        ~tgt_loss
        ~max_iters
    with e ->
      status := Printf.sprintf "error: %s" (Printexc.to_string e);
      { pos = problem.pos;
        c_out = edb_cfg;
        grad = Token_vec.zero (all_tokens problem);
        loss = Float.infinity;
        iterations = 0 }
  in

  let elapsed = Sys.time () -. time_start in

  (* Count learned rules (non-zero weight) *)
  let learned_rules = List.filter (fun rule ->
    FValue.nonzero (eval_lineage rule.rule_lineage (Token_vec.apply result.pos))
  ) problem.rules in
  let n_learned = List.length learned_rules in

  (* Sort learned rules by weight descending *)
  let learned_sorted = List.sort (fun r1 r2 ->
    let (fv1 : FValue.t) = eval_lineage r1.rule_lineage (Token_vec.apply result.pos) in
    let (fv2 : FValue.t) = eval_lineage r2.rule_lineage (Token_vec.apply result.pos) in
    compare fv2.v fv1.v
  ) learned_rules in

  let learned_rule_strs = List.map (fun rule ->
    let (fv : FValue.t) = eval_lineage rule.rule_lineage (Token_vec.apply result.pos) in
    json_obj [
      ("weight", json_float fv.v);
      ("rule", json_string (rule_to_string rule));
    ]
  ) learned_sorted in

  let json = json_obj [
    ("test", json_string test_name);
    ("evaluator", json_string evaluator_name);
    ("learner", json_string learner_name);
    ("scorer", json_string scorer_name);
    ("status", json_string !status);
    ("input_rels", json_int n_input);
    ("invented_rels", json_int n_invented);
    ("output_rels", json_int n_output);
    ("candidate_rules", json_int n_candidate_rules);
    ("iterations", json_int result.iterations);
    ("time_s", json_float elapsed);
    ("loss", json_float result.loss);
    ("target_loss", json_float tgt_loss);
    ("converged", json_bool (result.loss < tgt_loss));
    ("learned_rules_count", json_int n_learned);
    ("learned_rules", json_list learned_rule_strs);
  ] in
  Printf.printf "%s\n%!" json

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Usage Message                                                           *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let print_usage () =
  Printf.printf {|Difflog (OCaml reimplementation)

Usage:

  1. difflog alps <data.d> <templates.tp>
              <learner> <evaluator> <scorer>
              <tgtLoss> <maxIters>
     Runs Difflog in the ALPS setting.

     Learners:    NewtonRootLearner | HybridAnnealingLearner
     Evaluators:  NaiveEvaluator | SeminaiveEvaluator | TrieEvaluator | TrieSemiEvaluator
     Scorers:     L2Scorer | L1Scorer | XEntropyScorer

  2. difflog eval <data.d> <templates.tp> <evaluator>
     Evaluates all rules with initial weights (no learning).

  3. difflog bench <data.d> <templates.tp>
              <learner> <evaluator> <scorer>
              <tgtLoss> <maxIters>
     Like alps but outputs a single JSON line to stdout with structured stats.

Example:
  difflog alps path.d path.tp HybridAnnealingLearner SeminaiveEvaluator L2Scorer 0.01 1000

|}

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Main Dispatch                                                           *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let () =
  let args = Sys.argv in
  let argc = Array.length args in

  Printf.eprintf "Hello! Difflog invoked with arguments [%s]\n%!"
    (Array.to_list args |> String.concat ", ");

  let start_time = Sys.time () in

  (match argc with
   | 9 when args.(1) = "alps" ->
     cmd_alps args.(2) args.(3) args.(4) args.(5) args.(6)
       (float_of_string args.(7)) (int_of_string args.(8))

   | 9 when args.(1) = "bench" ->
     cmd_bench args.(2) args.(3) args.(4) args.(5) args.(6)
       (float_of_string args.(7)) (int_of_string args.(8))

   | 5 when args.(1) = "eval" ->
     cmd_eval args.(2) args.(3) args.(4)

   | _ -> print_usage ());

  let elapsed = Sys.time () -. start_time in
  Printf.eprintf "Total time: %.3f seconds\n%!" elapsed;
  Printf.eprintf "Bye!\n%!"
