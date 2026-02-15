(* Difflog Learner Module
   State type, gradient descent (Newton root), hybrid annealing (gradient + MCMC),
   and helper functions: forbidden tokens, solution point detection, reinterpret.

   Corresponds to:
     qd/learner/Learner.scala
     qd/learner/NewtonRootLearner.scala
     qd/learner/HybridAnnealingLearner.scala
*)

open Base
open Lineage
open Value
open Instance
open Scorer

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Type aliases for readability                                            *)
(* ═══════════════════════════════════════════════════════════════════════ *)

type fv_config = FValue.t config
type eval_fn = rule list -> (string -> FValue.t) -> fv_config -> fv_config

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Learner State                                                          *)
(* ═══════════════════════════════════════════════════════════════════════ *)

type state = {
  pos: Token_vec.t;
  c_out: fv_config;
  grad: Token_vec.t;
  loss: float;
  iterations: int;
}

(* ─────────────────────────────────────────────────────────────────────── *)
(* State Construction                                                      *)
(* ─────────────────────────────────────────────────────────────────────── *)

let make_state ~(evaluator : eval_fn) ~(scorer : scorer)
    ~(rules : rule list) ~(output_rels : RelationSet.t) ~(ref_idb : fv_config)
    ~(pos : Token_vec.t) ~(old_c_out : fv_config) : state =
  let repositioned = config_reposition old_c_out (Token_vec.apply pos) in
  let c_out = evaluator rules (Token_vec.apply pos) repositioned in
  let grad = gradient_loss_total scorer pos c_out ref_idb output_rels in
  let loss = loss_total scorer c_out ref_idb output_rels in
  { pos; c_out; grad; loss; iterations = 0 }

(* ─────────────────────────────────────────────────────────────────────── *)
(* Random utilities                                                        *)
(* ─────────────────────────────────────────────────────────────────────── *)

let random_float lo hi =
  lo +. Random.float (hi -. lo)

let sample_state ~(evaluator : eval_fn) ~(scorer : scorer)
    ~(rules : rule list) ~(output_rels : RelationSet.t) ~(ref_idb : fv_config)
    ~(all_tokens : TokenSet.t) ~(edb : fv_config) : state =
  let pos = Token_vec.create all_tokens (fun _ -> random_float 0.25 0.75) in
  make_state ~evaluator ~scorer ~rules ~output_rels ~ref_idb ~pos ~old_c_out:edb

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Forbidden Tokens                                                        *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let find_forbidden_tokens ~(output_rels : RelationSet.t)
    ~(discrete_idb : DTupleSet.t RelationMap.t) (c_out : fv_config) : TokenSet.t =
  RelationSet.fold (fun rel acc ->
    let out_inst = config_get ~zero:FValue.zero c_out rel in
    let out_support = instance_support ~nonzero:FValue.nonzero out_inst in
    let ref_tuples =
      match RelationMap.find_opt rel discrete_idb with
      | Some ts -> ts
      | None -> DTupleSet.empty
    in
    List.fold_left (fun acc2 (tuple, (fv : FValue.t)) ->
      if not (DTupleSet.mem tuple ref_tuples) then
        let ts = token_set fv.l in
        if TokenSet.cardinal ts = 1 then
          TokenSet.union acc2 ts
        else acc2
      else acc2
    ) acc out_support
  ) output_rels TokenSet.empty

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Solution Point Detection                                                *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let simplify_if_solution_point ~(evaluator : eval_fn) ~(scorer : scorer)
    ~(rules : rule list) ~(output_rels : RelationSet.t) ~(ref_idb : fv_config)
    ~(discrete_idb : DTupleSet.t RelationMap.t) ~(all_tokens : TokenSet.t)
    (c_out : fv_config) : state option =
  (* Collect tokens used in derivations of expected tuples *)
  let useful_tokens =
    RelationMap.fold (fun rel ref_tuples acc ->
      DTupleSet.fold (fun tuple acc2 ->
        let inst = config_get ~zero:FValue.zero c_out rel in
        let (fv : FValue.t) = instance_get ~zero:FValue.zero inst tuple in
        TokenSet.union acc2 (token_set fv.l)
      ) ref_tuples acc
    ) discrete_idb TokenSet.empty
  in
  let eliminable_tokens = TokenSet.diff all_tokens useful_tokens in

  let is_separable = RelationSet.for_all (fun rel ->
    let out_inst = config_get ~zero:FValue.zero c_out rel in
    let out_support = instance_support ~nonzero:FValue.nonzero out_inst in
    let expected =
      match RelationMap.find_opt rel discrete_idb with
      | Some ts -> ts
      | None -> DTupleSet.empty
    in
    List.for_all (fun (tuple, (fv : FValue.t)) ->
      if DTupleSet.mem tuple expected then true
      else
        let ts = token_set fv.l in
        not (TokenSet.is_empty (TokenSet.inter ts eliminable_tokens))
    ) out_support
  ) output_rels
  in

  if is_separable then begin
    Printf.eprintf "Current position is separable...\n%!";
    let new_pos = Token_vec.create all_tokens (fun t ->
      if TokenSet.mem t useful_tokens then 1.0 else 0.0
    ) in
    let new_state = make_state ~evaluator ~scorer ~rules ~output_rels
        ~ref_idb ~pos:new_pos ~old_c_out:c_out in
    if new_state.loss <= 1.01 then begin
      Printf.eprintf "... and also a solution point.\n%!";
      Some new_state
    end else begin
      Printf.eprintf "... but not a solution point (loss = %.4f).\n%!" new_state.loss;
      None
    end
  end else
    None

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Reinterpret                                                             *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let reinterpret ~(evaluator : eval_fn) ~(scorer : scorer)
    ~(rules : rule list) ~(output_rels : RelationSet.t) ~(ref_idb : fv_config)
    ~(discrete_idb : DTupleSet.t RelationMap.t) ~(all_tokens : TokenSet.t)
    (st : state) : state =
  let useful_tokens =
    RelationMap.fold (fun rel ref_tuples acc ->
      DTupleSet.fold (fun tuple acc2 ->
        let inst = config_get ~zero:FValue.zero st.c_out rel in
        let (fv : FValue.t) = instance_get ~zero:FValue.zero inst tuple in
        TokenSet.union acc2 (token_set fv.l)
      ) ref_tuples acc
    ) discrete_idb TokenSet.empty
  in
  let gray_tokens =
    RelationSet.fold (fun rel acc ->
      let out_inst = config_get ~zero:FValue.zero st.c_out rel in
      let out_support = instance_support ~nonzero:FValue.nonzero out_inst in
      let expected =
        match RelationMap.find_opt rel discrete_idb with
        | Some ts -> ts
        | None -> DTupleSet.empty
      in
      List.fold_left (fun acc2 (tuple, (fv : FValue.t)) ->
        if not (DTupleSet.mem tuple expected) then
          TokenSet.union acc2 (token_set fv.l)
        else acc2
      ) acc out_support
    ) output_rels TokenSet.empty
  in
  let exclusively_useful = TokenSet.diff useful_tokens gray_tokens in

  let new_pos = Token_vec.create all_tokens (fun t ->
    if TokenSet.mem t exclusively_useful then 1.0
    else if TokenSet.mem t gray_tokens then Token_vec.get st.pos t
    else 0.0
  ) in
  make_state ~evaluator ~scorer ~rules ~output_rels ~ref_idb
    ~pos:new_pos ~old_c_out:st.c_out

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Newton Root Learner                                                     *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let newton_next_state ~evaluator ~scorer ~rules ~output_rels ~ref_idb
    ~discrete_idb ~all_tokens ~forbidden_tokens (curr : state) : state =
  match simplify_if_solution_point ~evaluator ~scorer ~rules ~output_rels
      ~ref_idb ~discrete_idb ~all_tokens curr.c_out with
  | Some solution -> solution
  | None ->
    let grad_norm = Token_vec.norm curr.grad in
    if grad_norm = 0.0 then curr
    else begin
      let grad_unit = Token_vec.unit curr.grad in
      let delta = Token_vec.scale (curr.loss /. grad_norm) grad_unit in
      let raw_next = Token_vec.sub curr.pos delta in
      let clipped1 = Token_vec.clip 0.0 1.0 raw_next in
      let clipped2 = Token_vec.clip_with_prev 0.01 0.99 clipped1 curr.pos in
      let new_pos = Token_vec.create all_tokens (fun t ->
        if TokenSet.mem t forbidden_tokens then 0.0
        else
          match Token_vec.get_opt clipped2 t with
          | Some w -> w
          | None -> 0.5
      ) in
      make_state ~evaluator ~scorer ~rules ~output_rels ~ref_idb
        ~pos:new_pos ~old_c_out:curr.c_out
    end

let newton_root_learn ~evaluator ~scorer ~rules ~output_rels ~ref_idb
    ~discrete_idb ~all_tokens ~edb ~tgt_loss ~max_iters : state =
  let curr = ref (sample_state ~evaluator ~scorer ~rules ~output_rels
      ~ref_idb ~all_tokens ~edb) in
  let best = ref !curr in
  let step_size = ref 1.0 in
  let num_iters = ref 0 in

  while !num_iters < max_iters
        && !curr.loss >= tgt_loss
        && Token_vec.norm !curr.grad > 0.0
        && !step_size > 0.0 do
    let old = !curr in
    curr := newton_next_state ~evaluator ~scorer ~rules ~output_rels
        ~ref_idb ~discrete_idb ~all_tokens ~forbidden_tokens:TokenSet.empty old;
    step_size := Token_vec.norm (Token_vec.sub !curr.pos old.pos);

    if !curr.loss < !best.loss then best := !curr;
    incr num_iters;

    Printf.eprintf "  %.6f, %.6f, %.6f, %.6f, %.6f\n%!"
      !curr.loss !best.loss
      (Token_vec.norm !curr.pos)
      (Token_vec.norm !curr.grad)
      !step_size
  done;

  Printf.eprintf "#Iterations: %d.\n%!" !num_iters;
  let final = reinterpret ~evaluator ~scorer ~rules ~output_rels ~ref_idb
    ~discrete_idb ~all_tokens !best in
  { final with iterations = !num_iters }

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Hybrid Annealing Learner                                                *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let mcmc_freq = 30

let triangular_perturb prev =
  let coin = Random.float 1.0 in
  if coin < 0.5 then
    prev *. sqrt (2.0 *. coin)
  else
    1.0 -. (1.0 -. prev) *. sqrt (2.0 *. (1.0 -. coin))

let mcmc_next_state ~evaluator ~scorer ~rules ~output_rels ~ref_idb
    ~discrete_idb ~all_tokens ~forbidden_tokens
    (curr : state) (iteration : int) : state =
  match simplify_if_solution_point ~evaluator ~scorer ~rules ~output_rels
      ~ref_idb ~discrete_idb ~all_tokens curr.c_out with
  | Some solution -> solution
  | None ->
    let new_pos = Token_vec.create all_tokens (fun t ->
      if TokenSet.mem t forbidden_tokens then 0.0
      else triangular_perturb (Token_vec.get curr.pos t)
    ) in
    let proposed = make_state ~evaluator ~scorer ~rules ~output_rels
        ~ref_idb ~pos:new_pos ~old_c_out:curr.c_out in

    let c = 1.0e-3 in
    let k0 = 5.0 in
    let temperature = 1.0 /. (c *. log (k0 +. float_of_int iteration)) in
    let pi neg_loss = exp (neg_loss /. temperature) in

    let pi_curr = pi (-. curr.loss) in
    let pi_proposed = pi (-. proposed.loss) in
    let prob_accept = Float.min 1.0 (pi_proposed /. pi_curr) in
    let coin = Random.float 1.0 in

    Printf.eprintf "  temperature: %.4f, probAccept: %.6f, coin: %.6f\n%!"
      temperature prob_accept coin;

    if coin < prob_accept then begin
      Printf.eprintf "  Accepted MCMC sample\n%!";
      proposed
    end else begin
      Printf.eprintf "  Rejected MCMC sample\n%!";
      curr
    end

let hybrid_annealing_learn ~evaluator ~scorer ~rules ~output_rels ~ref_idb
    ~discrete_idb ~all_tokens ~edb ~tgt_loss ~max_iters : state =
  let forbidden = ref TokenSet.empty in
  let curr = ref (sample_state ~evaluator ~scorer ~rules ~output_rels
      ~ref_idb ~all_tokens ~edb) in
  let best = ref !curr in
  let step_size = ref 1.0 in
  let num_iters = ref 0 in

  while !num_iters < max_iters && !curr.loss >= tgt_loss do
    let newly_forbidden = find_forbidden_tokens ~output_rels ~discrete_idb !curr.c_out in
    if not (TokenSet.is_empty newly_forbidden) then
      forbidden := TokenSet.union !forbidden newly_forbidden;

    if !num_iters mod mcmc_freq = 0 then begin
      curr := mcmc_next_state ~evaluator ~scorer ~rules ~output_rels
          ~ref_idb ~discrete_idb ~all_tokens ~forbidden_tokens:!forbidden
          !curr (!num_iters / mcmc_freq);
      step_size := 1.0
    end else begin
      let old = !curr in
      curr := newton_next_state ~evaluator ~scorer ~rules ~output_rels
          ~ref_idb ~discrete_idb ~all_tokens ~forbidden_tokens:!forbidden old;
      step_size := Token_vec.norm (Token_vec.sub !curr.pos old.pos)
    end;

    if !curr.loss < !best.loss then best := !curr;
    incr num_iters;

    Printf.eprintf "  %.6f, %.6f, %.6f, %.6f, %.6f\n%!"
      !curr.loss !best.loss
      (Token_vec.norm !curr.pos)
      (Token_vec.norm !curr.grad)
      !step_size
  done;

  Printf.eprintf "#Iterations: %d.\n%!" !num_iters;
  let final = reinterpret ~evaluator ~scorer ~rules ~output_rels ~ref_idb
    ~discrete_idb ~all_tokens !best in
  { final with iterations = !num_iters }
