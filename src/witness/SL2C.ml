(* TODO: proper handling of nondet *)

open Astral
open Formula

module F = Format

let get_c_var var =
  let full_name = SL.Variable.show var in
  match String.split_on_char '#' full_name with
  | _ when SL.Variable.is_nil var -> None
  | [fn; name] ->
    let kf = Globals.Functions.find_by_name fn in
    WitnessUtils.find_varinfo_by_name (`Function kf) name
  | [name] ->
    WitnessUtils.find_varinfo_by_name `None name
  | _ -> assert false

let compute_region_size var field =
  let ctype = (Option.get @@ get_c_var var).vtype in
  match field with
  | None -> Cil.bytesSizeOf ctype
  | Some _ -> Machine.sizeof_ptr ()

let convert_var v =
  let full_name = SL.Variable.show v in
  assert (not @@ String.contains_from full_name 0 '!');
  match String.split_on_char '#' full_name with
  | _ when SL.Variable.is_nil v -> "NULL"
  | [prefix; name] ->
    if String.contains_from full_name 0 '$'
    then Format.sprintf "\\at(%s, Pre)" name
    else name
  | [name] ->
    if String.contains_from full_name 0 '$'
    then Format.sprintf "\\at(%s, Pre)" name
    else name
  | _ -> assert false

let target_to_fields = function
  | LS_t x -> ["next", x]
  | DLS_t (x, y) -> ["next", x; "prev", y]
  | Generic xs -> xs
  | _ -> assert false

(** For an atom, return its string representation as c expression and set of
    permissions needed to evaluate it. *)
let rec pure_atom = function
  | Eq [x; y] -> Option.some @@ F.sprintf "%s == %s" (convert_var x) (convert_var y)
  | Eq (x :: y :: xs) ->
      Option.some @@ F.sprintf "%s == %s && %s" (convert_var x) (convert_var y) (Option.get @@ pure_atom (Eq (y :: xs)))
  | Distinct (x, y) -> Option.some @@ F.sprintf "%s != %s" (convert_var x) (convert_var y)
  | PointsTo (x, cons) ->
    target_to_fields cons
    |> List.map (fun (field, y) -> F.sprintf "%s->%s==%s" (convert_var x) field (convert_var y))
    |> String.concat " & "
    |> Option.some
  | IntEq (var, c) -> Option.some @@ F.sprintf "%s==%d" (convert_var var) c
  | LS {first; next; min_len=0} -> None
  | LS {first; next; min_len=1} -> Some (F.sprintf "%s != %s" (convert_var first) (convert_var next))
  | LS {first; next; min_len=2} -> Some (F.sprintf "%s != %s" (convert_var first) (convert_var next)) (* TODO *)

  | Ref (source, target) -> Some (F.sprintf "*%s == %s" (convert_var source) (convert_var target))

  | Freed _ | Predicate _ | DLS _ | NLS _  -> None
  | _ -> assert false

(* TODO: will not work with multiple types of lists *)
(* TODO: bounds *)
let spatial_atom f = function
  | Predicate (name, xs) -> failwith "TODO"
  | LS {first; next; _} ->
    Some (F.sprintf "ls_sll(%s, %s)" (convert_var first) (convert_var next))
  (* DLS with unused last allocated node *)
  | DLS {first; last; prev; next; _} when Astral_v2.is_unconstrained last f  ->
    Some (
      Format.sprintf "dls_dll_simple(%s, %s, %s)"
        (convert_var first) (convert_var next)
        (convert_var prev)
    )
  | DLS {first; last; prev; next; _} ->
      Some (
        Format.sprintf "dls_dll(%s, %s, %s, %s)"
          (convert_var first) (convert_var next)
          (convert_var last) (convert_var prev)
      )
  | NLS {first; top; next; _} -> Some (Format.sprintf "nls_todo(%s, %s, %s)" (convert_var first) (convert_var top) (convert_var next))
  | _ -> None
(*
  | Predicate (name, xs) -> Option.some @@ F.sprintf "%s(%s)" name (String.concat ", " @@ List.map convert_var xs)
  | LS {first; next; _} -> Option.some @@ F.sprintf "ls(%s, %s)" (convert_var first) (convert_var next)
  | _ -> failwith "TODO: DLS, NLS"
*)

let perms_atom = function
  | PointsTo (x, cons) ->
    target_to_fields cons
    |> List.map (fun (field, y) -> F.sprintf "\\canAccess(%s->%s, %d)" (convert_var x) field (Machine.sizeof_ptr ()))
    |> String.concat ", "
    |> Option.some
  | Ref (source, _) ->
    Some (F.sprintf "\\canAccess(%s)" (convert_var source))
  | _ -> None

let preprocess =
  List.filter_map (function
    | Eq xs ->
      let xs = List.filter (fun v -> not @@ Common.is_nondet_var v) xs in
      (match xs with
      | [] | [_] -> None
      | xs -> Some (Eq xs)
      )
    | Distinct (x, y) when List.exists Common.is_nondet_var [x; y] -> None
    | atom -> Some atom
  )

let convert f =
  let f = preprocess f in
  let pure_part = List.filter_map pure_atom f in
  let spatial_part = List.filter_map (spatial_atom f) f in
  let permissions = List.filter_map perms_atom f in
  match permissions @ spatial_part, pure_part with
  | [], [] -> assert false
  | [], pure -> String.concat " && " pure
  | spatial, [] -> F.sprintf "\\separated(%s)" (String.concat ", " spatial)
  | s, p ->
      assert (s <> []);
      assert (p <> []);
      F.sprintf "\\separated(%s) && (%s)" (String.concat ", " s) (String.concat " && " p)
