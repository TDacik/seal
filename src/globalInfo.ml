(** Global information about the program being analyzed. *)

open Astral

open Cil_types
open Cil_datatype

module SM = Map.Make(String)

module VarMap = struct

  type var_map = {
    c_to_astral : SL.Variable.t Varinfo.Map.t;
    astral_to_c : Varinfo.t SM.t;
  }

  let empty = {
    c_to_astral = Varinfo.Map.empty;
    astral_to_c = SM.empty;
  }

  let self = ref empty

  let add var varinfo =
    let name = SL.Variable.show var in
    self := {
      c_to_astral = Varinfo.Map.add varinfo var !self.c_to_astral;
      astral_to_c = SM.add name varinfo !self.astral_to_c;
    }

  let to_astral varinfo = Varinfo.Map.find varinfo !self.c_to_astral

  let to_varinfo var = SM.find var !self.astral_to_c

end

(** Converts the type of a variable into its sort, and creates an SL variable *)
let varinfo_to_var_aux (varinfo : Cil_types.varinfo) : SL.Variable.t =
  let name = Common.var_unique_name varinfo in
  if Ast_types.is_integral varinfo.vtype then
    SL.Variable.mk name (Sort.mk_bitvector 32)
  else if not @@ Types.is_relevant_var varinfo then
    Common.fail "invalid type in varinfo_to_var: %a" Printer.pp_varinfo varinfo
  else
    let sort = varinfo.vtype |> Types.get_type_info |> fst in
    SL.Variable.mk name sort

let varinfo_to_var varinfo =
  try VarMap.to_astral varinfo
  with Not_found ->
    let var = varinfo_to_var_aux varinfo in
    VarMap.add var varinfo;
    var

let var_to_varinfo var =
  let name = SL.Variable.show var in
  let name =
    if String.contains name '$' then
      List.nth (String.split_on_char '$' name) 1
    else name
  in
  try VarMap.to_varinfo name
  with Not_found ->
    SM.iter (fun s v -> Format.printf "%s -> %a\n" s Varinfo.pretty v) !VarMap.self.astral_to_c;
    Config.Self.fatal "Cannot find varinfo corresponding to %s" name

let find_predicate_type_by_root root =
  let varinfo = var_to_varinfo root in
  match (Ast_types.unroll_deep varinfo.vtype).tnode with
  | TPtr { tnode = TComp structure; _ } -> Types.get_struct_type structure
  | TPtr _ -> failwith "TPTR"
  | _ -> failwith @@ Format.asprintf "%a" Printer.pp_typ varinfo.vtype
