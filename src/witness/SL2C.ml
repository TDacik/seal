module A = Abstraction

open Cil_types

open Astral
open Formula

module F = Format

(** Temporary manager for encoding information in SL variables. *)
module RichVar = struct

  type var = {
    anchor : bool;
    prefix : string option;
    name : string;
  }

  let remove_placeholder = SL.Variable.mk "##REMOVE##" Sort.loc_nil

  let show_var v =
    Format.sprintf "%s (prefix: %s, anchor: %b)"
      v.name (Option.value ~default:"none" v.prefix) v.anchor

  let var_name v =
    match v.prefix with
    | Some p -> F.sprintf "%s#%s" p v.name
    | None -> v.name

  type t =
    | Null
    | Var of var
    | Ref of t
    | Term of t * string

  let rec show = function
    | Null -> "NULL"
    | Var v -> show_var v
    | Ref r -> Format.sprintf "Ref (%s)" (show r)
    | Term (b, field) -> Format.sprintf "Term(%s, %s)" (show b) field

  let parse_var og_name =
    let anchor = String.contains og_name '$' in
    let base = if anchor then BatString.chop ~l:2 ~r:0 og_name else og_name in
    let prefix, name = match String.split_on_char '#' base with
      | [prefix; name] -> (Some prefix, name)
      | [name] -> (None, name)
      | _ -> assert false
    in
    {anchor; prefix; name}

  let rec parse_term name =
    if String.contains name '>' then
      let base, field = BatString.rsplit ~by:"->" name in
      Term (parse_term base, field)
    else if String.starts_with name ~prefix:"*" then
      Ref (parse_term @@ BatString.lchop ~n:1 name)
    else
      Var (parse_var name)

  let parse var =
    let res =
      if SL.Variable.is_nil var then Null
      else parse_term @@ SL.Variable.show var
    in
    (*Format.printf "Term: \027[36m%s -> %s\027[0m\n" (SL.Variable.show var) (show res);*)
    res

  let rec convert = function
    | Null -> assert false
    | Var v when v.anchor -> F.sprintf "A$%s" (var_name v)
    | Var v -> (var_name v)
    | Ref t -> F.sprintf "*%s" (convert t)
    | Term (t, field) -> F.sprintf "%s->%s" (convert t) field

  let mk_term var field =
    let term = parse_term @@ SL.Variable.show var in
    Term (term, field)

  let mk_ref var =
    let term = parse_term @@ SL.Variable.show var in
    Ref term

  let remove_index str =
    match String.split_on_char '!' str with
    | [name; _] -> name
    | [name] -> name
    | _ -> assert false

  let rec find_varinfo = function
    | Var {prefix=Some fn; name; _} ->
      GlobalInfo.var_to_varinfo (SL.Variable.mk (remove_index (fn ^ "#" ^ name)) Sort.loc_nil)
    | Var {name; _} ->
      GlobalInfo.var_to_varinfo (SL.Variable.mk (remove_index name) Sort.loc_nil)
    | Ref t -> find_varinfo t
    | Term (t, _) -> find_varinfo t
    | _ -> assert false

  let find_varinfo var =
    let term = parse_term @@ SL.Variable.show var in
    (*Format.printf "Term: \027[36m%s -> %s\027[0m\n" (SL.Variable.show var) (show term);*)
    find_varinfo term

  let rec output = function
    | Null -> "NULL"
    | Var v when v.anchor -> F.sprintf "\\at(%s, Pre)" v.name
    | Var v -> v.name
    | Ref t -> F.sprintf "(*%s)" (output t)
    | Term (t, field) -> F.sprintf "%s->%s" (output t) field

  let output' var =
    let res = output var in
    let res=
      if String.starts_with ~prefix:"(" res && String.ends_with ~suffix:")" res
      then BatString.chop res
      else res
    in
    (*Format.printf "Term: \027[34m%s -> %s\027[0m\n" (show var) res;*)
    res

  let output var =
    output' @@ parse var

end

let target_to_fields = function
  | LS_t (info, x) -> [info.next_field.forig_name, x]
  | DLS_t (info, x, y) -> [info.next_field.forig_name, x; info.prev_field.forig_name, y]
  | NLS_t (info, t, n) -> [info.top_field.forig_name, t; info.down_field.forig_name, n]
  | Generic xs -> xs

open Formula

let unfold_atom = function
  | LS {first; next; min_len=2; info} ->
      let fresh_var = SL.Variable.mk (RichVar.convert @@ RichVar.mk_term first info.next_field.forig_name) Sort.loc_ls in
      []
      |> add_atom (PointsTo (first, LS_t (info, fresh_var)))
      |> add_atom @@ mk_ls info fresh_var next 1

  | DLS {first; next; last; prev; min_len=2; info} ->
      let fresh_next = SL.Variable.mk (RichVar.convert @@ RichVar.mk_term first info.next_field.forig_name) SL_builtins.loc_dls in
      []
      |> add_atom (PointsTo (first, DLS_t (info, fresh_next, prev)))
      |> add_atom @@ mk_dls info fresh_next last first next 1

  | DLS {first; next; last; prev; min_len=3; info} ->
      let fresh1 = SL.Variable.mk (RichVar.convert @@ RichVar.mk_term first info.next_field.forig_name) SL_builtins.loc_dls in
      let fresh2 = SL.Variable.mk (RichVar.convert @@ RichVar.mk_term fresh1 info.next_field.forig_name) SL_builtins.loc_dls in
      []
      |> add_atom (PointsTo (first, DLS_t (info, fresh1, prev)))
      |> add_atom (PointsTo (fresh1, DLS_t (info, first, fresh2)))
      |> add_atom @@ mk_dls info fresh2 last fresh1 next 1

  | NLS {first; next; top; min_len=2; info} ->
      let fresh_ls = SL.Variable.mk (RichVar.convert @@ RichVar.mk_term first info.down_field.forig_name) Sort.loc_ls in
      let fresh_var = SL.Variable.mk (RichVar.convert @@ RichVar.mk_term first info.top_field.forig_name) SL_builtins.loc_nls in
      []
      |> add_atom (PointsTo (first, NLS_t (info, fresh_var, fresh_ls)))
      |> add_atom @@ mk_ls info.sll_info fresh_ls next 0
      |> add_atom @@ mk_nls info fresh_var top next 1
  | atom -> [atom]

(** For an atom, return its string representation as c expression and set of
    permissions needed to evaluate it. *)
let rec pure_atom = function
  | Formula.Eq [x; y] ->
    let x' = RichVar.output x in
    let y' = RichVar.output y in
    if String.equal x' y' then None
    else Option.some @@ F.sprintf "%s == %s" x' y'
  | Eq (x :: y :: xs) ->
      Option.some @@ F.sprintf "%s == %s && %s" (RichVar.output x) (RichVar.output y) (Option.get @@ pure_atom (Eq (y :: xs)))
  | Distinct (x, y) -> Option.some @@ F.sprintf "%s != %s" (RichVar.output x) (RichVar.output y)
  | PointsTo (x, cons) ->
    target_to_fields cons
    |> List.filter_map (fun (field, y) ->
        if Common.is_fresh_var y then None
        else if String.equal (RichVar.output' @@ RichVar.mk_term x field) (RichVar.output y) then None
        else Some (F.sprintf "%s==%s" (RichVar.output' @@ RichVar.mk_term x field) (RichVar.output y)))
    |> String.concat " && "
    |> (fun x -> if String.equal x "" then None else Some x)
  | IntEq (var, c) -> Option.some @@ F.sprintf "%s==%d" (RichVar.output var) c
  | LS {min_len=0; _} -> None
  | LS {first; next; min_len=1; _} -> Some (F.sprintf "%s != %s" (RichVar.output first) (RichVar.output next))
  | LS {min_len=2; _} -> assert false

  | DLS {min_len=0; _} -> None
  | DLS {min_len=1; first; next; _} -> Some (F.sprintf "%s != %s" (RichVar.output first) (RichVar.output next))
  | DLS {min_len=2; _} -> assert false
  | DLS {min_len=3; _} -> assert false

  | NLS {min_len=0; _} -> None
  | NLS {first; next; min_len=1; _} -> Some (F.sprintf "%s != %s" (RichVar.output first) (RichVar.output next))
  | NLS {min_len=2; _} -> assert false

  | Ref (source, target) ->
    let source' = "*" ^ RichVar.output source in
    let target' = RichVar.output target in
    if String.equal source' target' then None
    else Some (F.sprintf "%s == %s" source' target')

  | Freed _ -> None
  | _ -> assert false

(* TODO: bounds *)
let spatial_atom = function
  | Predicate _ -> failwith "TODO: generic predicate"
  | LS {first; next; info; _} ->
    let name = AbstractionHint.sll_name info in
    Some (F.sprintf "%s(%s, %s)" name (RichVar.output first) (RichVar.output next))
  (* DLS with unused last allocated node *)
  | DLS {first; last; prev; next; info; _} when SL.Variable.equal last RichVar.remove_placeholder ->
    let name = AbstractionHint.dll_name info in
    Some (
      Format.sprintf "%s_simple(%s, %s, %s)"
        name
        (RichVar.output first) (RichVar.output next)
        (RichVar.output prev)
    )
  | DLS {first; last; prev; next; info; _} ->
      let name = AbstractionHint.dll_name info in
      Some (
        Format.sprintf "%s(%s, %s, %s, %s)"
          name
          (RichVar.output first) (RichVar.output next)
          (RichVar.output last) (RichVar.output prev)
      )
  | NLS {first; top; next; info; _} ->
      let name = AbstractionHint.nll_name info in
      Some (Format.sprintf "%s(%s, %s, %s)" name (RichVar.output first) (RichVar.output top) (RichVar.output next))
  | _ -> None

let perms_atom = function
  | PointsTo (x, _) ->
    Option.some @@ F.sprintf "\\canAccess(%s, %d)"
      (RichVar.output x) (CorrectnessWitnessUtils.pointed_size @@ RichVar.find_varinfo x)
  | Ref (source, target) ->
    Option.some @@ F.sprintf "\\canAccess(%s, %d)"
      (RichVar.output source) (CorrectnessWitnessUtils.pointed_size @@ RichVar.find_varinfo target)
  | _ -> None

let preprocess =
  List.filter_map (function
    | Formula.Eq xs ->
      let xs = List.filter (fun v -> not @@ Common.is_nondet_var v) xs in
      (match xs with
      | [] | [_] -> None
      | xs -> Some (Formula.Eq xs)
      )
    | Distinct (x, y) when List.exists Common.is_nondet_var [x; y] -> None
    | atom -> Some atom
  )

let compute_substitutions_cons = function
  | LS_t (info, next) when Common.is_fresh_var next ->
      [next, info.next_field]
  | DLS_t (info, next, prev) when Common.is_fresh_var next && Common.is_fresh_var prev ->
      [next, info.next_field; prev, info.prev_field]
  | DLS_t (info, next, _) when Common.is_fresh_var next ->
      [next, info.next_field]
  | DLS_t (info, _, prev) when Common.is_fresh_var prev ->
      [prev, info.prev_field]
  | NLS_t (info, top, next) when Common.is_fresh_var top && Common.is_fresh_var next ->
      [next, info.sll_info.next_field; top, info.top_field]
  | NLS_t (info, top, _) when Common.is_fresh_var top ->
      [top, info.top_field]
  | NLS_t (info, _, next) when Common.is_fresh_var next ->
      [next, info.down_field]
  | _ -> []

let mark_unused_params f =
  List.map (function
    | DLS {first; last; prev; next; info; min_len} when Astral_v2.is_unconstrained last f ->
      Formula.mk_dls info first RichVar.remove_placeholder prev next min_len
    | other -> other
  ) f

let compute_substitutions f =
  let open Cil_types in
  List.concat_map (function
    | PointsTo (x, cons) ->
      compute_substitutions_cons cons
      |> List.map (fun (var, f) -> (var, RichVar.convert @@ RichVar.mk_term x f.forig_name))
    | Ref (source, target) when Common.is_fresh_var target -> [target, RichVar.convert @@ RichVar.mk_ref source]
    | _ -> []
  ) f

let apply_substitution f subst =
  List.fold_left (fun acc (var, by) ->
    let by = SL.Variable.mk by Sort.loc_nil in
    Formula.substitute acc ~var ~by
  ) f subst

let remove_irrelevant_atoms (formula : Formula.t) : Formula.t =
  let is_relevant_var (bound : int) (var : Formula.var) : bool =
    (not @@ Common.is_fresh_var var)
    || Formula.count_relevant_occurences var formula > bound
  in
  List.filter
    (function
      | Formula.Distinct (lhs, rhs) ->
          is_relevant_var 0 lhs && is_relevant_var 0 rhs
      | Formula.Freed var -> is_relevant_var 0 var
      | Formula.IntEq (var, _) | Formula.Ref (var, _) -> is_relevant_var 1 var
      | _ -> true)
    formula

let rec repeat_until_fixpoint f x =
  let x' = f x in
  if Formula.equal x x' then x
  else repeat_until_fixpoint f x'

let normalise f =
  Simplification.reduce_equiv_classes f
  |> preprocess
  |> List.concat_map unfold_atom
  |> repeat_until_fixpoint (fun f ->
      let subst = compute_substitutions f in
      apply_substitution f subst)
  |> mark_unused_params
  |> (fun f -> remove_irrelevant_atoms f)

let convert_formula f =
  Config.Self.debug "In: %a" Formula.pp_formula f;
  let f' = normalise f in
  Config.Self.debug "Phase 1: %a" Formula.pp_formula f';
  let f''=
    if List.exists Common.is_fresh_var @@ Formula.get_vars f'
    then normalise @@ A.apply @@ Simplification.reduce_equiv_classes f
    else f'
  in
  Config.Self.debug "Phase 2: %a" Formula.pp_formula f'';
  (
    if List.exists Common.is_fresh_var @@ Formula.get_vars f''
    then Config.Self.fatal "Cannot eliminate existential quantifiers in:\n%a"
      Formula.pp_formula f''
  );
  let pure_part = List.filter_map pure_atom f'' in
  let spatial_part = List.filter_map spatial_atom f'' in
  let permissions = List.filter_map perms_atom f'' in
  match permissions @ spatial_part, pure_part with
  | [], [] -> assert false
  | [], pure -> String.concat " && " pure
  | [sp], [] -> F.sprintf "%s" sp
  | spatial, [] -> F.sprintf "\\separated(%s)" (String.concat ", " spatial)
  | [sp], p -> F.sprintf "\\separated(%s) && %s" sp (String.concat " && " p)
  | s, p -> F.sprintf "\\separated(%s) && %s" (String.concat ", " s) (String.concat " && " p)

(* Conversion of states *)

let should_split = function
  | DLS {prev; _} -> Common.is_fresh_var prev
  | _ -> false

let rec split f =
  match List.find_opt should_split f with
  | None -> [f]
  | Some (DLS {first; next; last; prev; info; min_len} as dls) ->
    let f' = BatList.remove_if (Formula.equal_atom dls) f in
    let n = SL.Variable.mk_fresh "n" Sort.loc_nil in (* TODO: sort *)
    List.concat_map split [
      Eq [first; next] :: f';
      PointsTo (first, DLS_t (info, n, prev))
        :: mk_dls info n last first next min_len
        :: f'
    ]
  | _ -> assert false

let convert_state state =
  List.map split state
  |> List.concat
  |> List.map convert_formula
  |> List.map (fun s -> "(" ^ s ^ ")")
  |> String.concat " || "
