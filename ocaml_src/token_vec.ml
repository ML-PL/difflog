open Lineage

(* ═══════════════════════════════════════════════════════════════════════ *)
(* Token Weight Vector                                                    *)
(* Maps token names (strings) to float weights in [0,1]                  *)
(* ═══════════════════════════════════════════════════════════════════════ *)

type t = float TokenMap.t

(* ─────────────────────────────────────────────────────────────────────── *)
(* Construction *)
(* ─────────────────────────────────────────────────────────────────────── *)

let create (tset : TokenSet.t) (f : string -> float) : t =
  TokenSet.fold (fun token acc ->
    TokenMap.add token (f token) acc
  ) tset TokenMap.empty

let of_map (m : float TokenMap.t) : t = m

let zero (tset : TokenSet.t) : t =
  create tset (fun _ -> 0.0)

let constant (tset : TokenSet.t) (v : float) : t =
  create tset (fun _ -> v)

(* ─────────────────────────────────────────────────────────────────────── *)
(* Access *)
(* ─────────────────────────────────────────────────────────────────────── *)

let get (tv : t) (token : string) : float =
  TokenMap.find token tv

let get_opt (tv : t) (token : string) : float option =
  TokenMap.find_opt token tv

let contains (tv : t) (token : string) : bool =
  TokenMap.mem token tv

let key_set (tv : t) : TokenSet.t =
  TokenMap.fold (fun k _ acc -> TokenSet.add k acc) tv TokenSet.empty

let iter (f : string -> float -> unit) (tv : t) : unit =
  TokenMap.iter f tv

let fold (f : string -> float -> 'a -> 'a) (tv : t) (init : 'a) : 'a =
  TokenMap.fold f tv init

(* ─────────────────────────────────────────────────────────────────────── *)
(* Arithmetic *)
(* ─────────────────────────────────────────────────────────────────────── *)

let add (tv1 : t) (tv2 : t) : t =
  TokenMap.merge (fun _token opt1 opt2 ->
    match opt1, opt2 with
    | Some v1, Some v2 -> Some (v1 +. v2)
    | Some v1, None -> Some v1
    | None, Some v2 -> Some v2
    | None, None -> None
  ) tv1 tv2

let sub (tv1 : t) (tv2 : t) : t =
  TokenMap.merge (fun _token opt1 opt2 ->
    match opt1, opt2 with
    | Some v1, Some v2 -> Some (v1 -. v2)
    | Some v1, None -> Some v1
    | None, Some v2 -> Some (-.v2)
    | None, None -> None
  ) tv1 tv2

let scale (s : float) (tv : t) : t =
  TokenMap.map (fun v -> s *. v) tv

let div_scalar (tv : t) (s : float) : t =
  if s = 0.0 then
    TokenMap.map (fun _ -> 0.0) tv
  else
    TokenMap.map (fun v -> v /. s) tv

(* ─────────────────────────────────────────────────────────────────────── *)
(* Norms *)
(* ─────────────────────────────────────────────────────────────────────── *)

let norm (tv : t) : float =
  let sum_of_squares = fold (fun _ v acc ->
    acc +. (v *. v)
  ) tv 0.0 in
  Float.sqrt sum_of_squares

let unit (tv : t) : t =
  let n = norm tv in
  if n = 0.0 then tv else div_scalar tv n

(* ─────────────────────────────────────────────────────────────────────── *)
(* Clipping *)
(* ─────────────────────────────────────────────────────────────────────── *)

let clip (lo : float) (hi : float) (tv : t) : t =
  TokenMap.map (fun v ->
    Float.max lo (Float.min hi v)
  ) tv

let clip_with_prev (lo : float) (hi : float) (new_vec : t) (prev_vec : t) : t =
  TokenMap.merge (fun _token opt_new opt_prev ->
    match opt_new, opt_prev with
    | Some new_v, Some prev_v ->
      let clamped =
        if new_v < lo && prev_v >= lo then lo
        else if new_v > hi && prev_v <= hi then hi
        else new_v
      in
      Some clamped
    | Some new_v, None ->
      let clamped =
        if new_v < lo then lo
        else if new_v > hi then hi
        else new_v
      in
      Some clamped
    | None, Some prev_v ->
      (* No new value, keep previous *)
      Some prev_v
    | None, None -> None
  ) new_vec prev_vec

(* ─────────────────────────────────────────────────────────────────────── *)
(* Conversion *)
(* ─────────────────────────────────────────────────────────────────────── *)

let to_list (tv : t) : (string * float) list =
  TokenMap.fold (fun k v acc -> (k, v) :: acc) tv []

let to_string (tv : t) : string =
  let items = to_list tv in
  let strs = List.map (fun (token, weight) ->
    Printf.sprintf "%s:%.4f" token weight
  ) items in
  "[" ^ String.concat ", " strs ^ "]"

(* ─────────────────────────────────────────────────────────────────────── *)
(* Apply as position function: token -> Value.FValue.t *)
(* ─────────────────────────────────────────────────────────────────────── *)

let apply (tv : t) (token : string) : Value.FValue.t =
  let w = TokenMap.find token tv in
  Value.FValue.make w (Base.Token token)
