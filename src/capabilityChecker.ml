

let unsupported_functions = [
  "alloca";
  "__builtin_alloca";
  "at_exit"
]

let check_function kf = match Kernel_function.get_name kf with
  | name when List.mem name unsupported_functions ->
    Common.unsupported "Unsupported function: %s" name
  | _ -> ()

let check_functions () =
  Globals.Functions.iter (fun kf ->
    if Kernel_function.is_not_called kf then ()
    else check_function kf
  )

let run () = check_functions ()
