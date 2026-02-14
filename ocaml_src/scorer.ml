(* Difflog Scorer: Loss functions and gradient computation
   Corresponds to qd/learner/Scorer.scala
*)

open Base
open Lineage
open Value
open Instance

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Scorer type                                                             *)
(* ═══════════════════════════════════════════════════════════════════════ *)

type scorer = {
  name : string;
  loss : float -> float -> float;  (* vOut -> vRef -> scalar loss *)
}

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Gradient: dv(t)/dw_i = freq(w_i in lineage) * v(t) / w_i             *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let gradient (pos : Token_vec.t) (c_out : FValue.t config) (rel : relation)
    (t : dtuple) : Token_vec.t =
  let inst = config_get ~zero:FValue.zero c_out rel in
  let fv = instance_get ~zero:FValue.zero inst t in
  let vt = fv.v in
  let freq = token_multiset fv.l in
  TokenMap.fold (fun token f acc ->
    if f > 0 then
      let w = Token_vec.get pos token in
      if w > 0.0 then
        let deriv = (float_of_int f) *. vt /. w in
        let safe_deriv = if Float.is_finite deriv then deriv else 0.0 in
        TokenMap.add token safe_deriv acc
      else acc
    else acc
  ) freq TokenMap.empty

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Loss computation over relations                                        *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(* Collect all tuples present in either c_out or c_ref for a relation *)
let all_tuples_for_rel (c_out : FValue.t config) (c_ref : FValue.t config)
    (rel : relation) : dtuple list =
  let out_inst = config_get ~zero:FValue.zero c_out rel in
  let ref_inst = config_get ~zero:FValue.zero c_ref rel in
  let out_tuples = instance_support ~nonzero:FValue.nonzero out_inst in
  let ref_tuples = instance_support ~nonzero:FValue.nonzero ref_inst in
  (* Deduplicate by building a set *)
  let seen = Hashtbl.create 64 in
  let add_unique lst =
    List.iter (fun (t, _) ->
      let key = Array.fold_left (fun acc c -> acc ^ c.c_name ^ ",") "" t in
      if not (Hashtbl.mem seen key) then
        Hashtbl.replace seen key t
    ) lst
  in
  add_unique out_tuples;
  add_unique ref_tuples;
  Hashtbl.fold (fun _ t acc -> t :: acc) seen []

(* Total loss over one relation *)
let loss_relation (sc : scorer) (c_out : FValue.t config) (c_ref : FValue.t config)
    (rel : relation) : float =
  let tuples = all_tuples_for_rel c_out c_ref rel in
  let out_inst = config_get ~zero:FValue.zero c_out rel in
  let ref_inst = config_get ~zero:FValue.zero c_ref rel in
  List.fold_left (fun acc t ->
    let v_out = (instance_get ~zero:FValue.zero out_inst t).v in
    let v_ref = (instance_get ~zero:FValue.zero ref_inst t).v in
    acc +. sc.loss v_out v_ref
  ) 0.0 tuples

(* Total loss over all output relations *)
let loss_total (sc : scorer) (c_out : FValue.t config) (c_ref : FValue.t config)
    (output_rels : RelationSet.t) : float =
  RelationSet.fold (fun rel acc ->
    acc +. loss_relation sc c_out c_ref rel
  ) output_rels 0.0

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Gradient of loss                                                        *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(* Gradient of loss for a single tuple *)
let gradient_loss_tuple ~loss_deriv (pos : Token_vec.t) (c_out : FValue.t config)
    (c_ref : FValue.t config) (rel : relation) (t : dtuple) : Token_vec.t =
  let out_inst = config_get ~zero:FValue.zero c_out rel in
  let ref_inst = config_get ~zero:FValue.zero c_ref rel in
  let v_out = (instance_get ~zero:FValue.zero out_inst t).v in
  let v_ref = (instance_get ~zero:FValue.zero ref_inst t).v in
  let g = gradient pos c_out rel t in
  let scalar = loss_deriv v_out v_ref in
  Token_vec.scale scalar g

(* Loss derivative functions for each scorer type *)
let loss_deriv_of_scorer (sc : scorer) : float -> float -> float =
  match sc.name with
  | "L2Scorer" -> (fun v_out v_ref -> 2.0 *. (v_out -. v_ref))
  | "L1Scorer" -> (fun v_out v_ref ->
    if v_out -. v_ref > 0.0 then 1.0 else -1.0)
  | "XEntropyScorer" -> (fun v_out v_ref ->
    let eps = 1e-7 in
    let v_out_c = Float.max eps (Float.min (1.0 -. eps) v_out) in
    -. (v_ref /. v_out_c -. (1.0 -. v_ref) /. (1.0 -. v_out_c)))
  | _ -> (fun v_out v_ref -> 2.0 *. (v_out -. v_ref))  (* default to L2 *)

(* Total gradient over all output relations *)
let gradient_loss_total (sc : scorer) (pos : Token_vec.t)
    (c_out : FValue.t config) (c_ref : FValue.t config)
    (output_rels : RelationSet.t) : Token_vec.t =
  let loss_deriv = loss_deriv_of_scorer sc in
  RelationSet.fold (fun rel acc ->
    let tuples = all_tuples_for_rel c_out c_ref rel in
    List.fold_left (fun acc2 t ->
      let g = gradient_loss_tuple ~loss_deriv pos c_out c_ref rel t in
      Token_vec.add acc2 g
    ) acc tuples
  ) output_rels TokenMap.empty

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Scorer Implementations                                                  *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let l2_scorer : scorer = {
  name = "L2Scorer";
  loss = (fun v_out v_ref ->
    let diff = v_out -. v_ref in diff *. diff);
}

let l1_scorer : scorer = {
  name = "L1Scorer";
  loss = (fun v_out v_ref -> Float.abs (v_out -. v_ref));
}

let xentropy_scorer : scorer = {
  name = "XEntropyScorer";
  loss = (fun v_out v_ref ->
    let eps = 1e-7 in
    let v_out_c = Float.max eps (Float.min (1.0 -. eps) v_out) in
    let v_ref_c = Float.max eps (Float.min (1.0 -. eps) v_ref) in
    -. (v_ref_c *. Float.log v_out_c +.
        (1.0 -. v_ref_c) *. Float.log (1.0 -. v_out_c)));
}

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Registry                                                                *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let find_scorer name =
  match name with
  | "L2Scorer" -> l2_scorer
  | "L1Scorer" -> l1_scorer
  | "XEntropyScorer" -> xentropy_scorer
  | _ -> failwith ("Unknown scorer: " ^ name)
