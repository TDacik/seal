(* TODO: this module probably duplicates some work already implemented
         in SEAL analysis. *)

open Cil_datatype

module H = Stmt.Hashtbl

let self : (Formula.state) H.t ref = ref (H.create 113 : Formula.state H.t)

(** Replace all variables that are out of the scope of the given function
    by existential variables. *)
let remove_out_of_scope_vars kf f =
  let open Astral in
  let is_outside_var var =
    let varinfo = GlobalInfo.var_to_varinfo var in
    not @@ varinfo.vglob
    && not @@ Kernel_function.is_formal_or_local varinfo kf
  in
  Formula.get_vars f
  |> List.fold_left (fun acc var ->
      if SL.Variable.is_nil var || Common.is_fresh_var var || Common.is_nondet_var var then acc
      else if is_outside_var var then Formula.substitute acc ~var ~by:(SL.Variable.refresh var)
      else acc) f

let add stmt f =
  if Common.is_loop stmt then
    let kf = Kernel_function.find_englobing_kf stmt in
    let f = List.map (remove_out_of_scope_vars kf) f in
    let current = Option.value ~default:[] @@ H.find_opt !self stmt in
    H.replace !self stmt (f @ current)
  else ()

let get () =
  H.filter_map_inplace (fun _ states -> Some (BatList.unique ~eq:Formula.equal states)) !self;
  H.filter_map_inplace (fun _ states -> Some (Simplification.deduplicate_formulas states)) !self;
  !self
