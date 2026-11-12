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

let apply var lhs_ctype formula =
  match lhs_ctype with
  | Some ctype when Ast_types.is_ptr ctype && not (Ast_types.is_void_ptr ctype) -> (
    match Formula.get_spatial_atom_from_opt var formula with
    | Some (PointsTo (_, Void (target, size))) ->
      formula
      |> Formula.remove_spatial_from var
      |> Formula.add_atom (PointsTo (var, fresh_value target ctype))
    | _ -> formula)
  | _ -> formula
