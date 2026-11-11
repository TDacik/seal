(* Solving of simple entailments that does not have to be passed to Astral. *)

open Formula

let is_pointer_atom = function
  | PointsTo _ | Ref _ -> true
  | _ -> false

let is_predicate_atom = function
  | Predicate _ | LS _ | DLS _ | NLS _ -> true
  | _ -> false

let is_predicate_free formula =
  not @@ List.exists is_predicate_atom formula

let count_pointers formula =
  List.filter is_pointer_atom formula
  |> List.length

let try_solve lhs rhs =
  if is_predicate_free lhs && is_predicate_free rhs then
    let nb_lhs = count_pointers lhs in
    let nb_rhs = count_pointers rhs in
    if nb_lhs <> nb_rhs then Some false
    else None
  else None

let try_solve lhs rhs =
  assert (List.length lhs == 1);
  assert (List.length rhs == 1);
  match try_solve (List.hd lhs) (List.hd rhs) with
  | None -> None
  | Some res ->
    Some res
