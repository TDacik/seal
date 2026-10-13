(* Checks for unsupported features. *)

open Cil_types
open Cil_datatype

let is_var_pointer var = Ast_types.is_ptr var.vtype

let is_frama_c_builtin var =
  Cil_builtins.is_builtin var
  || Ast_attributes.(contains fc_stdlib var.vattr)

let check_globals () =
  Globals.Vars.iter (fun var _ ->
    if is_var_pointer var && not @@ is_frama_c_builtin var then
      Config.Self.not_yet_implemented "global pointers"
    else ()
  )

let check_functions () =
  Globals.Functions.iter (fun kf ->
    match Kernel_function.get_name kf with
    | "atexit" -> Config.Self.not_yet_implemented "function atexit"
    | _ -> ()
  )

let run () =
  check_globals ();
  check_functions ()
