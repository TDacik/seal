(* Parse SL formula encoded in Cabs

   TODO: cleanup *)

open Astral
open Astral.Preprocessing
open MemoryModel

open Cabs

(* Global context *)

let params = ref []
let location = ref ("", -1)
let invariant = ref None

let heap_sort = ref HeapSort.empty

(** Utilities *)

let name_equal str = function
  | (_, (name, _, _, _)) -> String.equal name str

let exp_to_string e = match e.expr_node with
   | VARIABLE name -> name
   | _ -> Config.Self.fatal "Unsupported expression: %a" Cprint.print_expression e

let expr_name_equal str e = match e.expr_node with
  | VARIABLE name -> String.equal name str
  | _ -> false

(** Conversion *)

let convert_var ?(prefix="") name =
  (** Each variable in invariant must come from the original C program and
      thus we should be able to locate it somewhere. *)
  let open Cil_types in
  let var = WitnessUtils.find_varinfo_by_name (`Location !location) name in
  match var with
    | Some var ->
      let sort, _ = Types.get_type_info var.vtype in
      let name = Common.var_unique_name var in
      SL.Term.mk_var (prefix ^ name) sort
    | None ->
      try SL.Term.of_var @@ List.find (fun v -> String.equal (SL.Variable.get_name v) name) !params
      with Not_found -> raise @@ Exceptions.UnknownVariable (Option.get !invariant, name)

let rec convert_term e =
  match e.expr_node with
  | VARIABLE name when String.equal name "NULL" -> SL.Term.nil
  | VARIABLE name -> convert_var name

  | CONSTANT (CONST_INT  i) -> SL.Term.mk_smt @@ SMT.Bitvector.mk_const_of_int (int_of_string i) (* TODO *) 32
  (*| CONSTANT (CONST_BOOL b) -> SL.Term.mk_smt @@ SMT.Boolean.mk_const b*)
  | CONSTANT _ -> failwith "unsupported constant"

  (* Dereference *)
  | UNARY (MEMOF, e) ->
    let e = convert_term e in
    let field =
      SL.Term.get_sort e
      |> (fun sort -> HeapSort.find_target sort !heap_sort)
      |> StructDef.get_fields
      |> List.hd (* TODO: Check that this is indeed boxed type *)
    in
    SL.Term.mk_heap_term field e

  | BINARY (op, _, _) -> Config.Self.fatal "binary: %a" Cabs_debug.pp_bin_op op

  | INDEX (_, _) -> failwith "index"

  | PAREN e -> convert_term e

  | MEMBEROF _ -> failwith "memberof"
  | MEMBEROFPTR (base, field) ->
    let base = convert_term base in
    let field =
      SL.Term.get_sort base
      |> (fun sort -> HeapSort.find_target sort !heap_sort)
      |> StructDef.find_field (fun f -> (Field.show f) = field)
    in
    SL.Term.mk_heap_term field base

  | CALL (fn, [what; where], _) when expr_name_equal "at" fn ->
    if expr_name_equal "Pre" where then
      let aux = convert_term what in
      SL.Term.map_vars (fun v -> SL.Variable.rename (fun old ->"A$" ^ old) v) aux
    else failwith "todo: at"

  | CALL _ -> failwith "unknown call"

  | _ -> failwith @@ Format.asprintf "Unknown term: %a" Cprint.print_expression e

let rec convert e =
  match e.expr_node with
  | BINARY (EQ, {expr_node = UNARY (MEMOF, e1); _}, e2) ->
    let e1 = convert_term e1 in
    let field =
      SL.Term.get_sort e1
      |> (fun sort -> HeapSort.find_target sort !heap_sort)
      |> StructDef.get_fields
      |> List.hd (* TODO: Check that this is indeed boxed type *)
    in
    let e1 = SL.Term.mk_heap_term field e1 in
    let e2 = convert_term e2 in
    SL.mk_eq [e1; e2]

  | BINARY (EQ, e1, e2) -> SL.mk_eq @@ List.map convert_term [e1; e2]
  | BINARY (NE, e1, e2) -> SL.mk_distinct @@ List.map convert_term [e1; e2]
  | BINARY (AND, e1, e2) -> SL.mk_and @@ List.map convert [e1; e2]
  | BINARY (OR, e1, e2) -> SL.mk_or @@ List.map convert [e1; e2]

  | CALL (exp, [base_e; _], _) when expr_name_equal "canAccess" exp ->
    (* TODO: check size *)
    let base = convert_term base_e in
    let sort = SL.Term.get_sort base in
    let cons = Types.get_struct_def sort in
    let fields = StructDef.get_fields cons in
    let rhs = List.map (fun f -> SL.Term.mk_fresh_var "e" @@ Field.get_sort f) fields in
    SL.mk_pto_struct base cons rhs

  | CALL (exp, _, _) when expr_name_equal "canAccess" exp ->
    Config.Self.fatal "\\canAcess expects two parameters"


  | CALL (exp, xs, _) when expr_name_equal "separated" exp ->
    SL.mk_star @@ List.map convert xs

  (* TODO: check if is defined predicate! *)
  | CALL (exp, params, _) ->
    (* Inductive predicate *)
    let name = exp_to_string exp in
    SL.mk_predicate name @@ List.map convert_term params


  | UNARY _ -> failwith "unary"
  | BINARY (_, e1, e2) ->
      Config.Self.fatal "%a\n%a" Cabs_debug.pp_exp e1 Cabs_debug.pp_exp e2
  | CAST _ -> failwith "cast"
  | PAREN e -> convert e
  | MEMBEROF _ -> failwith "memberof"
  | MEMBEROFPTR _ -> failwith "memberof_ptr"
  | _ ->
      Config.Self.fatal "convert: %a" Cabs_debug.pp_exp e

let get_formula = function
  | RETURN (exp, _) -> convert exp
  | _ -> assert false

let is_existential var =
  String.contains (SL.Variable.show var) '!'

let map_cases fn phi = match SL.view phi with
  | Or psis -> SL.mk_or @@ List.map fn psis
  | _ -> fn phi

let to_precise_hack = SL.map_view (function And xs -> `Modify (SL.mk_star xs) | _ -> `Skip)

let fn phi : SL.t =
  let vars = SL.free_vars ~with_nil:false ~with_pure:true phi in
  let existentials = List.filter is_existential vars in
  SL.mk_exists existentials phi
  |> to_precise_hack
  |> HeapTermElimination.apply
  (*|> QuantifierElimination.remove_determined*)

let get pos body ps cabs =
  let open CorrectnessWitness in
  params := ps;
  location := pos;
  invariant := Some RawInvariant.{location = snd pos; raw_content = body; should_be_inductive = false (* not relevant *)};
  heap_sort := Astral.Solver.get_heap_sort (Option.get !Common.solver);
  List.find_map (function
    | FUNDEF (_, name, block, _, _) when name_equal "main" name ->
      let phi = get_formula @@ (List.hd block.bstmts).stmt_node in
      Option.some @@ map_cases fn phi
    | _ -> None
  ) cabs
  |> Option.get
