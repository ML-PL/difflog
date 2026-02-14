(* Difflog ALPS Parser
   Parses data files (.d) and template files (.tp) in the ALPS format.

   Corresponds to qd/problem/ALPSParser.scala

   Data file format:
     - Domain declarations: "DomainName: val1, val2, val3."
     - Relation declarations: "relname(D1, D2)" or "*relname(D1)" for EDB
     - Tuple listings: "val1, val2" (one per line, terminated by ".")

   Template file format:
     - "P0(X, Y) :- P1(X, Z), P2(Z, Y)."
     - Meta-variables P0, P1, P2 get instantiated to concrete relations.
     - Variables X, Y, Z get typed by the relation signatures.
*)

open Base
open Problem

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Token Counter (for generating unique rule token names)                 *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let num_tokens = ref 0

let next_token () =
  let n = !num_tokens in
  incr num_tokens;
  Printf.sprintf "R%d" n

(* ═══════════════════════════════════════════════════════════════════════ *)
(* String Utilities                                                        *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let trim s = String.trim s

let split_on_char c s =
  String.split_on_char c s

let split_on_string sep s =
  (* Split s on occurrences of the separator string sep.
     Uses separate 'start' (segment beginning) and 'search_from' (search cursor)
     so that a false match of sep.[0] advances the cursor without losing content. *)
  let sep_len = String.length sep in
  let s_len = String.length s in
  if sep_len = 0 then [s]
  else
    let rec find_parts start search_from acc =
      if search_from >= s_len then
        List.rev (String.sub s start (s_len - start) :: acc)
      else
        match String.index_from_opt s search_from sep.[0] with
        | None ->
          List.rev (String.sub s start (s_len - start) :: acc)
        | Some i ->
          if i + sep_len <= s_len && String.sub s i sep_len = sep then
            find_parts (i + sep_len) (i + sep_len)
              (String.sub s start (i - start) :: acc)
          else
            find_parts start (i + 1) acc
    in
    find_parts 0 0 []

(* Split a string by regex-like pattern for "(", ",", ")" *)
let split_literal_str s =
  (* Parse "relname(arg1, arg2, ...)" into (relname, [arg1; arg2; ...]) *)
  let s = trim s in
  match String.index_opt s '(' with
  | None -> (s, [])
  | Some lparen ->
    let name = trim (String.sub s 0 lparen) in
    let rparen = match String.rindex_opt s ')' with
      | Some i -> i
      | None -> String.length s
    in
    let args_str = String.sub s (lparen + 1) (rparen - lparen - 1) in
    let args = List.map trim (split_on_char ',' args_str) in
    let args = List.filter (fun s -> String.length s > 0) args in
    (name, args)

(* ═══════════════════════════════════════════════════════════════════════ *)
(* 1. Parse Training Data (.d file)                                       *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let parse_data_str (problem : problem) (data_str : string) : problem =
  let lines = Array.of_list (
    String.split_on_char '\n' data_str
    |> List.map trim
  ) in
  let idx = ref 0 in
  let n = Array.length lines in
  let p = ref problem in

  (* ── 1a. Read domain declarations ── *)
  (* Lines containing ":" are domain declarations *)
  let domain_names = Hashtbl.create 16 in
  let domain_elems = Hashtbl.create 16 in

  while !idx < n && String.contains lines.(!idx) ':' do
    let line = lines.(!idx) in
    let parts = split_on_string ":" line in
    let name = trim (List.hd parts) in
    let elems_str = trim (List.nth parts 1) in
    (* Remove trailing "." *)
    let elems_str =
      if String.length elems_str > 0 && elems_str.[String.length elems_str - 1] = '.' then
        String.sub elems_str 0 (String.length elems_str - 1)
      else elems_str
    in
    let domain = { d_name = name } in
    let elem_strs = List.map trim (split_on_char ',' elems_str) in
    let elems = List.filter (fun s -> String.length s > 0) elem_strs
                |> List.map (fun e -> { c_name = e; c_domain = domain }) in

    Hashtbl.replace domain_names name domain;
    Hashtbl.replace domain_elems domain
      (List.fold_left (fun acc c -> ConstantSet.add c acc) ConstantSet.empty elems);
    incr idx
  done;

  (* Skip blank lines *)
  while !idx < n && String.length (trim lines.(!idx)) = 0 do incr idx done;

  (* Build dom2values map *)
  let d2v = Hashtbl.fold (fun dom elems acc ->
    DomainMap.add dom elems acc
  ) domain_elems DomainMap.empty in
  p := add_dom2values !p d2v;

  (* ── 1b. Read relations and their tuples ── *)
  while !idx < n do
    let line = trim lines.(!idx) in
    if String.length line = 0 then begin incr idx end
    else if line = "." || line = ";" then begin incr idx end
    else begin
      (* This line is a relation signature *)
      let is_edb = String.length line > 0 && line.[0] = '*' in
      let sig_str = if is_edb then
        trim (String.sub line 1 (String.length line - 1))
      else line in

      let (name, domain_strs) = split_literal_str sig_str in
      let domains = List.map (fun d_name ->
        match Hashtbl.find_opt domain_names d_name with
        | Some dom -> dom
        | None -> failwith (Printf.sprintf "Unknown domain: %s" d_name)
      ) domain_strs in
      let relation = { r_name = name; r_signature = Array.of_list domains } in

      let is_invented = String.length name >= 6 && String.sub name 0 6 = "invent" in

      p := (
        if is_edb then add_input_rel !p relation
        else if is_invented then add_invented_rel !p relation
        else add_output_rel_then_dump !p relation
      );

      incr idx;
      (* Skip blank and separator lines *)
      while !idx < n && (String.length (trim lines.(!idx)) = 0
                         || trim lines.(!idx) = ";") do
        incr idx
      done;

      (* Read tuples until we hit "." *)
      while !idx < n && trim lines.(!idx) <> "." do
        let tuple_line = trim lines.(!idx) in
        if String.length tuple_line > 0 then begin
          let field_strs = List.map trim (split_on_char ',' tuple_line) in
          let fields = List.map2 (fun dom field_str ->
            let elems = Hashtbl.find domain_elems dom in
            match ConstantSet.find_opt { c_name = field_str; c_domain = dom } elems with
            | Some c -> c
            | None -> failwith (Printf.sprintf "Unknown constant %s in domain %s" field_str dom.d_name)
          ) domains field_strs in
          let tuple = Array.of_list fields in

          p := (
            if is_edb then add_edb_tuples !p [(relation, tuple)]
            else begin
              assert (not is_invented);
              add_idb_tuples !p [(relation, tuple)]
            end
          )
        end;
        incr idx;
        (* Skip blank and separator lines *)
        while !idx < n && (String.length (trim lines.(!idx)) = 0
                           || trim lines.(!idx) = ";") do
          incr idx
        done
      done;

      (* Skip the "." terminator *)
      if !idx < n && trim lines.(!idx) = "." then incr idx;
      (* Skip blank lines after the block *)
      while !idx < n && String.length (trim lines.(!idx)) = 0 do incr idx done
    end
  done;

  !p

(* ═══════════════════════════════════════════════════════════════════════ *)
(* 2. Parse Template Rules (.tp file)                                     *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(* A meta-literal: (meta_rel_name, [meta_var_name; ...]) *)
type meta_literal = string * string list

(* Parse a template line into meta-literals: head and body *)
let parse_template_line (line : string) : meta_literal * meta_literal list =
  (* Remove trailing "." *)
  let line = trim line in
  let line =
    if String.length line > 0 && line.[String.length line - 1] = '.' then
      trim (String.sub line 0 (String.length line - 1))
    else line
  in
  (* Split on " :- " *)
  let parts = split_on_string " :- " line in
  let head_str = trim (List.hd parts) in
  let body_str = trim (List.nth parts 1) in

  let parse_mlit s =
    let (name, args) = split_literal_str s in
    (name, args)
  in

  let head = parse_mlit head_str in

  (* Split body on ")," to handle both "P1(X,Z),P2(Z,Y)" and "P1(X, Z), P2(Z, Y)" *)
  (* We split on ")," then re-add ")" to each part except the last *)
  let body_parts = split_on_string ")," body_str in
  let body_parts = List.mapi (fun i s ->
    if i < List.length body_parts - 1 then s ^ ")"
    else s
  ) body_parts in
  let body = List.map parse_mlit body_parts in

  (head, body)

(* ─────────────────────────────────────────────────────────────────────── *)
(* Meta-variable instantiation                                             *)
(* ─────────────────────────────────────────────────────────────────────── *)

(* Instantiate meta-variables in a meta-literal.
   rel_map: meta_rel_name -> concrete relation (built up incrementally)
   var_map: meta_var_name -> concrete variable (built up incrementally)
   available_rels: set of relations to try for this literal

   Returns a list of (literal, updated_rel_map, updated_var_map) options.
*)

module StringMap = Map.Make(String)

type rel_map = relation StringMap.t
type var_map = variable StringMap.t

let rec instantiate_meta_vars_impl
    (var_names : string list) (sig_ : domain list)
    (vm : var_map) : (variable list * var_map) option =
  match var_names, sig_ with
  | [], [] -> Some ([], vm)
  | vn :: vn_rest, dom :: dom_rest ->
    (match instantiate_meta_vars_impl vn_rest dom_rest vm with
     | None -> None
     | Some (vars_tail, vm_tail) ->
       if StringMap.mem vn vm_tail then
         let existing = StringMap.find vn vm_tail in
         if compare_domain existing.v_domain dom = 0 then
           Some (existing :: vars_tail, vm_tail)
         else None
       else
         let new_var = { v_name = vn; v_domain = dom } in
         Some (new_var :: vars_tail, StringMap.add vn new_var vm_tail))
  | _ -> None

(* Instantiate a single meta-literal against available relations *)
let instantiate_meta_literal
    (mlit : meta_literal) (rm : rel_map) (vm : var_map)
    (available_rels : RelationSet.t)
  : (literal * rel_map * var_map) list =
  let (rel_name, field_names) = mlit in
  let arity = List.length field_names in

  (* Determine candidate relations *)
  let candidates =
    if StringMap.mem rel_name rm then
      [StringMap.find rel_name rm]
    else
      RelationSet.elements available_rels
      |> List.filter (fun r -> Array.length r.r_signature = arity)
  in

  List.filter_map (fun rel ->
    let sig_list = Array.to_list rel.r_signature in
    match instantiate_meta_vars_impl field_names sig_list vm with
    | None -> None
    | Some (vars, vm2) ->
      let fields = List.map (fun v -> Var v) vars |> Array.of_list in
      let lit = { l_relation = rel; l_fields = fields } in
      let rm2 = StringMap.add rel_name rel rm in
      Some (lit, rm2, vm2)
  ) candidates

(* Instantiate a list of body meta-literals *)
let rec instantiate_meta_literals
    (mlits : meta_literal list) (rm : rel_map) (vm : var_map)
    (all_rels : RelationSet.t)
  : (literal list * rel_map * var_map) list =
  match mlits with
  | [] -> [([], rm, vm)]
  | mlit :: rest ->
    let rest_results = instantiate_meta_literals rest rm vm all_rels in
    List.concat_map (fun (lits_tail, rm_tail, vm_tail) ->
      let head_results = instantiate_meta_literal mlit rm_tail vm_tail all_rels in
      List.map (fun (lit, rm2, vm2) ->
        (lit :: lits_tail, rm2, vm2)
      ) head_results
    ) rest_results

(* ─────────────────────────────────────────────────────────────────────── *)
(* Rule deduplication                                                      *)
(* ─────────────────────────────────────────────────────────────────────── *)

(* Check if two rules have the same head and body (ignoring lineage) *)
let rules_structurally_equal r1 r2 =
  compare_literal r1.rule_head r2.rule_head = 0
  && Array.length r1.rule_body = Array.length r2.rule_body
  && array_for_all2 (fun l1 l2 -> compare_literal l1 l2 = 0) r1.rule_body r2.rule_body

(* Check if any body literal equals the head (trivial cycle) *)
let rule_has_trivial_cycle rule =
  Array.exists (fun body_lit ->
    compare_literal body_lit rule.rule_head = 0
  ) rule.rule_body

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Main Template Parser                                                    *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let parse_template_str (problem : problem) (template_str : string) : problem =
  let lines = String.split_on_char '\n' template_str
              |> List.map trim
              |> List.filter (fun s -> String.length s > 0) in
  let p = ref problem in

  List.iter (fun line ->
    let (head_mlit, body_mlits) = parse_template_line line in

    (* Available relations for body: input + invented + output *)
    let body_rels = RelationSet.union
        (RelationSet.union !p.input_rels !p.invented_rels) !p.output_rels in
    (* Available relations for head: output + invented *)
    let head_rels = RelationSet.union !p.output_rels !p.invented_rels in

    (* Instantiate body literals first *)
    let body_instantiations = instantiate_meta_literals body_mlits
        StringMap.empty StringMap.empty body_rels in

    List.iter (fun (body_lits, body_rm, body_vm) ->
      (* Instantiate head literal using the relation/variable maps from body *)
      let head_results = instantiate_meta_literal head_mlit body_rm body_vm head_rels in
      List.iter (fun (head_lit, _rm2, _vm2) ->
        (* Only keep rules where head is output or invented *)
        if RelationSet.mem head_lit.l_relation !p.output_rels
           || RelationSet.mem head_lit.l_relation !p.invented_rels then begin
          let token_name = next_token () in
          let rule = {
            rule_lineage = Token token_name;
            rule_head = head_lit;
            rule_body = Array.of_list body_lits;
          } in
          let normalized = rule_normalize rule in

          (* Deduplication: skip if structurally equal rule already exists *)
          let already_exists = List.exists (fun r ->
            rules_structurally_equal r normalized
          ) !p.rules in

          (* Skip trivial cycles *)
          if not already_exists && not (rule_has_trivial_cycle normalized) then
            p := add_rule (add_token !p token_name 1.0) normalized
        end
      ) head_results
    ) body_instantiations
  ) lines;

  !p

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Top-level Parse Function                                                *)
(* ═══════════════════════════════════════════════════════════════════════ *)

let parse (data_str : string) (template_str : string) : problem =
  let p0 = empty in
  let p1 = parse_data_str p0 data_str in
  let p2 = parse_template_str p1 template_str in

  Printf.eprintf "Input relations: %d\n%!" (RelationSet.cardinal p2.input_rels);
  Printf.eprintf "Invented relations: %d\n%!" (RelationSet.cardinal p2.invented_rels);
  Printf.eprintf "Output relations: %d\n%!" (RelationSet.cardinal p2.output_rels);
  Printf.eprintf "Rules: %d\n%!" (List.length p2.rules);

  p2
