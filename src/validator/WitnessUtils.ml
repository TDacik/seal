open Cil_types

let is_match _filename kf line =
  let s, e =
    match kf.fundec with
    | Definition (_, loc) -> loc
    | Declaration (_, _, _, loc) -> loc
  in
  let start = Filepos.line s in
  let stop = Filepos.line e in
  start <= line && line <= stop && Kernel_function.is_definition kf
(* Prevent lookup in Frama-c's declarations *)
(* TODO: handle multiple files

    && Filepath.equal (Filepath.of_string filename) (Filepos.path s)*)

let find_kf_by_line filename line : Kernel_function.t option =
  Globals.Functions.fold
    (fun kf acc ->
      match acc with None when is_match filename kf line -> Some kf | _ -> acc)
    None

let find_varinfo_by_name scope name =
  let kf =
    match scope with
    | `Location (filename, loc) -> find_kf_by_line filename loc
    | `Function kf -> Some kf
    | `None -> None
  in
  match kf with
  | Some kf ->
      Globals.Syntactic_search.find_in_scope ~strict:false name
        (Whole_function kf)
  | None -> Globals.Syntactic_search.find_in_scope ~strict:false name Global
