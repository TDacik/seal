(** Transfer functions for allocation. *)

open Astral

open Cil_types
open Cil_datatype

(** Fresh name for allocated memory *)
let fresh_var name =
  let line = Fileloc.line @@ Current_loc.get () in
  let name = Format.asprintf "%s@%d" name line in
  SL.Variable.mk_fresh name Sort.loc_nil

let eval_size formula size = match size.enode with
  | Lval (Var v, NoOffset) -> (
    let v = GlobalInfo.varinfo_to_var v in
    match Formula.get_int_val_opt v formula with
    | Some i -> Z.of_int i
    | None -> Config.Self.fatal "Cannot evaluate allocation size")
  | _ ->
    match Cil.constFoldToInt ~machdep:true size with
    | Some x -> x
    | None ->
      Common.unsupported "Symbolic-size allocation: %a" Exp.pretty size

let malloc formula size lhs_ctype =
  let lhs = fresh_var "malloc" in
  let size = eval_size formula size in
  if Option.is_none lhs_ctype || Option.exists Ast_types.is_void_ptr lhs_ctype then
    let target = fresh_var "malloc" in
    let atom : Formula.atom = Formula.PointsTo (lhs, Void (target, size)) in
    [(atom :: formula)], [lhs]
  else
    let lhs_ctype = Option.get lhs_ctype in
    let target = fresh_var "malloc" in
    let rhs = Void_cast.fresh_value target lhs_ctype in
    let atom : Formula.atom = Formula.PointsTo (lhs, rhs) in
    [(atom :: formula)], [lhs]
