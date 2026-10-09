open Astral

open Cil_types
open Cil_datatype

module VarSet = Varinfo.Set

(** Used internally to signalize that we don't know how to compute
    footprint and should fallback to the default method. *)
exception Skip

(** Over-approximation of modified variables *)
let rec modified_vars stmt = match stmt.skind with
  | Instr (Set (lval, _, _)) -> modified_vars_lval lval
  | Instr (Call (None, _, _, _)) -> raise Skip
  | Instr (Call (Some _, _, _, _)) -> raise Skip
  | Instr _ -> Varinfo.Set.empty
  | Return _ | Goto _ | Break _ | Continue _ -> VarSet.empty
  | If (_, block_then, block_else, _) ->
      VarSet.union (modified_vars_block block_then) (modified_vars_block block_else)
  | Switch _ -> raise Skip
  | Loop (_, block, _, _, _) -> modified_vars_block block
  | Block b -> modified_vars_block b
  | UnspecifiedSequence s ->
    List.map (fun (stmt, _, _, _, _) -> stmt) s
    |> List.fold_left (fun acc stmt -> VarSet.union acc @@ modified_vars stmt) VarSet.empty
  | _ -> assert false

and modified_vars_lval (lhost, _) = match lhost with
  | Var v -> VarSet.singleton v
  | Mem exp -> modified_vars_exp exp

and modified_vars_exp exp = match exp.enode with
  | Const _ | SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _ -> VarSet.empty
  | UnOp (_, e, _) | CastE (_, e) -> modified_vars_exp e
  | BinOp (_, e1, e2, _) -> VarSet.union (modified_vars_exp e1) (modified_vars_exp e2)
  | AddrOf lval | StartOf lval | Lval lval -> modified_vars_lval lval (* TODO: needed? *)

and modified_vars_block block =
  List.fold_left
    (fun acc stmt -> Varinfo.Set.union acc @@ modified_vars stmt)
    Varinfo.Set.empty
    block.bstmts

(** Reachability *)

module V = SL.Term

module G = struct
  module G = Graph.Persistent.Digraph.Concrete(SL.Term)
  include G
  include Graph.Oper.P(G)
  module Path = Graph.Path.Check(G)

  module Out = Graph.Graphviz.Dot(struct
    include G
    let graph_attributes _ = []
    let default_vertex_attributes _ = []
    let vertex_name t = Format.asprintf "\"%s\"" (SL.Term.show t)
    let vertex_attributes _ = []
    let get_subgraph _ = None
    let default_edge_attributes _ = []
    let edge_attributes _ = []
  end)

  let add_edge g x y =
    if SL.Term.is_constant x then g
    else G.add_edge g x y

  let rec build phi = match SL.view phi with
    | Eq xs ->
      BatList.cartesian_product xs xs
      |> List.fold_left (fun acc (x, y) -> add_edge acc x y) G.empty
    | Distinct _ | Emp -> G.empty
    | PointsTo (x, _, ys) -> List.fold_left (fun acc y -> add_edge acc x y) G.empty ys
    | Predicate (_, xs, _, _) ->
      BatList.cartesian_product xs xs
      |> List.fold_left (fun acc (x, y) -> add_edge acc x y) G.empty
    | Star psis -> List.fold_left union G.empty @@ List.map build psis
    | _ -> assert false

end

(* TODO: query Astral for more precise information for predicates.*)
let get_sources atom = match SL.view atom with
  | PointsTo (x, _, _) -> [x]
  | Predicate (_, xs, _, _) -> xs
  | _ -> []

let is_reachable_atom g vars atom =
  let atom_vars = List.map SL.Term.as_var @@ get_sources atom in
  let worklist = BatList.cartesian_product vars atom_vars in
  let path_checker = G.Path.create g in
  List.exists (fun (s, t) ->
    let s = SL.Term.of_var s in
    let t = SL.Term.of_var t in
    if not @@ G.mem_vertex g s then false
    else if not @@ G.mem_vertex g t then false
    else G.Path.check_path path_checker s t
  ) worklist

let process_frame atom =
  match SL.view atom with
    | Eq _ | Distinct _ -> [atom]
    | PointsTo (x, def, ys) ->
      let fields = MemoryModel.StructDef.get_fields def in
      List.map2 (fun f y -> SL.mk_eq2 (SL.Term.mk_heap_term f x) y) fields ys
    | _ -> []

let compute_reachable current modified =
  let g = G.build current in
  let es, atoms = SL.as_quantified_symbolic_heap current in
  let reachable, unreachable = List.partition (is_reachable_atom g modified) atoms in
  let unreachable = List.concat_map process_frame unreachable in
  (SL.mk_exists es @@ SL.mk_star unreachable,
   SL.mk_exists es @@ SL.mk_star reachable)

let compute loop_stmt current =
  try
    let modified =
      Varinfo.Set.elements @@ modified_vars loop_stmt
      |> List.filter_map (fun varinfo ->
          try Some (GlobalInfo.varinfo_to_var varinfo)
          with _ -> None)
    in
    compute_reachable current modified
  with Skip -> (SL.emp, current)
