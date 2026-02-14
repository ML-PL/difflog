(* Difflog Instance: trie-based mapping from DTuple to value
   Corresponds to qd/instance/Instance.scala, Config.scala, Assignment.scala
*)

open Base

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Instance: trie-based mapping from DTuple to value                     *)
(* ═══════════════════════════════════════════════════════════════════════ *)

type 'v instance =
  | IBase of 'v
  | Ind of domain * domain list * ('v instance) ConstantMap.t

(* ─────────────────────────────────────────────────────────────────────── *)
(* Construction *)
(* ─────────────────────────────────────────────────────────────────────── *)

let create_instance ~zero (sig_ : domain list) : 'v instance =
  match sig_ with
  | [] -> IBase zero
  | d :: rest -> Ind (d, rest, ConstantMap.empty)

let instance_arity : 'v instance -> int = function
  | IBase _ -> 0
  | Ind (_, rest, _) -> 1 + List.length rest

(* ─────────────────────────────────────────────────────────────────────── *)
(* Lookup *)
(* ─────────────────────────────────────────────────────────────────────── *)

let rec instance_get ~zero (inst : 'v instance) (tuple : dtuple) : 'v =
  match inst with
  | IBase v ->
    assert (Array.length tuple = 0);
    v
  | Ind (_, _, map) ->
    let c = tuple.(0) in
    (match ConstantMap.find_opt c map with
     | None -> zero
     | Some sub ->
       let rest = Array.sub tuple 1 (Array.length tuple - 1) in
       instance_get ~zero sub rest)

(* ─────────────────────────────────────────────────────────────────────── *)
(* Add: insert or update a tuple with a value *)
(* ─────────────────────────────────────────────────────────────────────── *)

let rec instance_add ~zero ~plus ~gt (inst : 'v instance) (tuple : dtuple) (v : 'v) : 'v instance =
  match inst with
  | IBase old_v ->
    assert (Array.length tuple = 0);
    let new_v = plus old_v v in
    if gt new_v old_v then IBase new_v else inst
  | Ind (dom_head, dom_tail, map) ->
    let c = tuple.(0) in
    let rest = Array.sub tuple 1 (Array.length tuple - 1) in
    let sub =
      match ConstantMap.find_opt c map with
      | None -> create_instance ~zero dom_tail
      | Some s -> s
    in
    let new_sub = instance_add ~zero ~plus ~gt sub rest v in
    if new_sub == sub then inst
    else Ind (dom_head, dom_tail, ConstantMap.add c new_sub map)

(* ─────────────────────────────────────────────────────────────────────── *)
(* Merge: combine two instances *)
(* ─────────────────────────────────────────────────────────────────────── *)

let rec instance_merge ~zero ~plus ~gt (a : 'v instance) (b : 'v instance) : 'v instance =
  match a, b with
  | IBase va, IBase vb ->
    let vn = plus va vb in
    if gt vn va then IBase vn else a
  | Ind (dh, dt, ma), Ind (_, _, mb) ->
    let merged = ConstantMap.merge (fun _key oa ob ->
      match oa, ob with
      | Some ia, Some ib -> Some (instance_merge ~zero ~plus ~gt ia ib)
      | Some ia, None -> Some ia
      | None, Some ib -> Some ib
      | None, None -> None
    ) ma mb in
    Ind (dh, dt, merged)
  | _, _ -> failwith "instance_merge: incompatible instances"

(* ─────────────────────────────────────────────────────────────────────── *)
(* Filter *)
(* ─────────────────────────────────────────────────────────────────────── *)

let rec instance_filter ~nonzero (inst : 'v instance) (filter : constant option array) : (dtuple * 'v) list =
  match inst with
  | IBase v ->
    if nonzero v then [([||], v)] else []
  | Ind (_, _, map) ->
    let rest_filter = Array.sub filter 1 (Array.length filter - 1) in
    (match filter.(0) with
     | Some c ->
       (match ConstantMap.find_opt c map with
        | None -> []
        | Some sub ->
          List.map (fun (t, v) ->
            (Array.append [|c|] t, v)
          ) (instance_filter ~nonzero sub rest_filter))
     | None ->
       ConstantMap.fold (fun c sub acc ->
         let results = instance_filter ~nonzero sub rest_filter in
         List.fold_left (fun acc2 (t, v) ->
           (Array.append [|c|] t, v) :: acc2
         ) acc results
       ) map [])

(* ─────────────────────────────────────────────────────────────────────── *)
(* Support: all tuples with nonzero values *)
(* ─────────────────────────────────────────────────────────────────────── *)

let instance_support ~nonzero (inst : 'v instance) : (dtuple * 'v) list =
  let arity = instance_arity inst in
  instance_filter ~nonzero inst (Array.make arity None)

(* ─────────────────────────────────────────────────────────────────────── *)
(* Emptiness check *)
(* ─────────────────────────────────────────────────────────────────────── *)

let rec instance_is_empty ~nonzero (inst : 'v instance) : bool =
  match inst with
  | IBase v -> not (nonzero v)
  | Ind (_, _, map) ->
    ConstantMap.for_all (fun _ sub ->
      instance_is_empty ~nonzero sub
    ) map

(* ─────────────────────────────────────────────────────────────────────── *)
(* Map over values *)
(* ─────────────────────────────────────────────────────────────────────── *)

let rec instance_map_values (f : 'v -> 'u) (inst : 'v instance) : 'u instance =
  match inst with
  | IBase v -> IBase (f v)
  | Ind (dh, dt, map) ->
    Ind (dh, dt, ConstantMap.map (instance_map_values f) map)

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Config: mapping from Relation to Instance                             *)
(* ═══════════════════════════════════════════════════════════════════════ *)

type 'v config = 'v instance RelationMap.t

let config_empty : 'v config = RelationMap.empty

let config_get ~zero (cfg : 'v config) (rel : relation) : 'v instance =
  match RelationMap.find_opt rel cfg with
  | Some inst -> inst
  | None -> create_instance ~zero (Array.to_list rel.r_signature)

let config_add_tuple ~zero ~plus ~gt (cfg : 'v config) (rel : relation) (tuple : dtuple) (v : 'v) : 'v config =
  let inst = config_get ~zero cfg rel in
  let new_inst = instance_add ~zero ~plus ~gt inst tuple v in
  RelationMap.add rel new_inst cfg

(* Reposition: re-evaluate all FValues with new weights *)
let config_reposition (cfg : Value.FValue.t config) (new_pos : string -> Value.FValue.t) : Value.FValue.t config =
  RelationMap.map (fun inst ->
    instance_map_values (fun (fv : Value.FValue.t) ->
      Value.eval_lineage fv.l new_pos
    ) inst
  ) cfg

let config_non_empty_support ~nonzero (cfg : 'v config) : bool =
  RelationMap.exists (fun _ inst ->
    not (instance_is_empty ~nonzero inst)
  ) cfg

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Assignment: variable bindings during rule evaluation                  *)
(* ═══════════════════════════════════════════════════════════════════════ *)

type 'v assignment = {
  bindings: constant VariableMap.t;
  score: 'v;
}

let assignment_empty ~one : 'v assignment = {
  bindings = VariableMap.empty;
  score = one;
}

let assignment_get (a : 'v assignment) (v : variable) : constant option =
  VariableMap.find_opt v a.bindings

let assignment_extend (a : 'v assignment) (v : variable) (c : constant) : 'v assignment option =
  match VariableMap.find_opt v a.bindings with
  | Some existing ->
    if compare_constant existing c = 0 then Some a else None
  | None ->
    if compare_domain v.v_domain c.c_domain = 0 then
      Some { a with bindings = VariableMap.add v c a.bindings }
    else None

let assignment_scale ~times (a : 'v assignment) (coeff : 'v) : 'v assignment =
  { a with score = times a.score coeff }

let assignment_project (a : 'v assignment) (vars : VariableSet.t) : 'v assignment =
  { a with bindings = VariableMap.filter (fun v _ -> VariableSet.mem v vars) a.bindings }

let assignment_to_tuple (a : 'v assignment) (lit : literal) : dtuple * 'v =
  let fields = Array.map (fun p ->
    match p with
    | Const c -> c
    | Var v -> VariableMap.find v a.bindings
  ) lit.l_fields in
  (fields, a.score)

let assignment_to_filter (a : 'v assignment) (lit : literal) : constant option array =
  Array.map (fun p ->
    match p with
    | Var v -> VariableMap.find_opt v a.bindings
    | Const c -> Some c
  ) lit.l_fields

(* Serialize bindings for grouping *)
let assignment_bindings_key (a : 'v assignment) : string =
  VariableMap.fold (fun v c acc ->
    acc ^ v.v_name ^ "=" ^ c.c_name ^ ";"
  ) a.bindings ""
