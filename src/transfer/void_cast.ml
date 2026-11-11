(** Implementation of implicit cast from void * to a pointer type. *)

open Cil_types

open Astral
open MemoryModel

open Formula

let pointed_type t =
  match (Ast_types.unroll_deep t).tnode with TPtr t -> t | _ -> assert false

let get_size = function
  | Formula.Void (_, s) -> s
  | _ -> assert false

let fresh_value target ctype =
  let sort = Types.sort_of_type ctype in
  let name = SL.Variable.show target in
  let init sort = SL.Variable.mk_fresh name sort in
  let structure = Types.get_struct_def sort in
  let generic () =
    let fields = StructDef.get_fields structure in
    let names = List.map MemoryModel.Field.show fields in
    let values = List.map init @@ List.map Field.get_sort fields in
    Generic (List.combine names values)
  in
  match (Ast_types.unroll_deep ctype).tnode with
  | TPtr { tnode = TComp structure; _ } -> (
    match Types.get_struct_type structure with
    | Sll info -> LS_t (info, init SL_builtins.loc_ls)
    | Dll info -> DLS_t (info, init SL_builtins.loc_dls, init SL_builtins.loc_dls)
    | Nl info -> NLS_t (info, init SL_builtins.loc_nls, init SL_builtins.loc_ls)
    | Struct s -> generic ()
  )
  | _ -> generic ()

(** Given a formula and variable var representing a void pointer, compute the type
    case in the assignment lhs_ctype _ := var.*)
let apply var lhs_ctype formula =
  if Option.for_all Ast_types.is_void_ptr lhs_ctype then formula
  else
    let lhs_ctype = Option.get lhs_ctype in
    let var' = SL.Variable.mk (SL.Variable.get_name var) Sort.loc_nil in
    let atom = Formula.get_spatial_atom_from var' formula in
    let formula' = Formula.remove_spatial_from var' formula in
    let new_atom = match atom with
      (* TODO: size check *)
      | PointsTo (_, Void (target, size)) ->
        PointsTo (var, fresh_value target lhs_ctype)
      | _ -> atom
    in
    new_atom :: formula'
