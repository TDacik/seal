open Cil
open Cil_types
open Astral
open Common
open Config

(** This module implements the analysis of C types that determines, which list
    types they represent *)

(** Classification of structs *)
type struct_type =
  | Sll of AbstractionHint.sll_info
  | Dll of AbstractionHint.dll_info
  | Nl  of AbstractionHint.nll_info
  | Struct of compinfo

(** Classification of struct fields *)
type field_type = Next | Prev | Top | Other of string | Data

let pp_field_type fmt = function
  | Next -> Format.fprintf fmt "Next"
  | Prev -> Format.fprintf fmt "prev"
  | Top -> Format.fprintf fmt "top"
  | Other name -> Format.fprintf fmt "Other: %s" name
  | Data -> Format.fprintf fmt "data"

let rec pp_struct_type fmt stype =
  let open Cil_printer in
  match stype with
  | Sll {compinfo; next_field} ->
    Format.fprintf fmt "%a[%a]" Cil_printer.pp_compinfo compinfo pp_field next_field
  | Dll {compinfo; next_field; prev_field} ->
    Format.fprintf fmt "%a[%a, %a]" Cil_printer.pp_compinfo compinfo pp_field next_field pp_field prev_field
  | Nl {compinfo; top_field; down_field; sll_info} ->
    Format.fprintf fmt "%a[%a, %a, %a]" Cil_printer.pp_compinfo compinfo pp_field top_field pp_field down_field pp_struct_type (Sll sll_info)
  | Struct compinfo ->
    Format.fprintf fmt "%a" Cil_printer.pp_compinfo compinfo


let pp_typ_node fmt tnode = Cil_printer.pp_typ fmt { tnode; tattr = [] }

let is_relevant_type (typ : typ) : bool =
  match Ast_types.unroll_deep_node typ with
  | TComp _ | TPtr _ -> true
  | _ -> false

let is_relevant_var (var : varinfo) = is_relevant_type var.vtype

let get_struct_pointer_fields (structure : compinfo) : fieldinfo list =
  structure.cfields |> Option.get
  |> List.filter (fun field -> is_relevant_type field.ftype)

let rec get_self_and_sll_fields (structure : compinfo) :
    fieldinfo list * (fieldinfo * AbstractionHint.sll_info) list =
  let self_pointers, other_pointers =
    structure |> get_struct_pointer_fields
    |> List.partition (fun field ->
           match Ast_types.unroll_deep_node field.ftype with
           | TPtr { tnode = TComp target_struct; _ } ->
               target_struct.ckey = structure.ckey
           | _ -> false)
  in
  let sll_pointers =
    List.filter_map
      (fun field ->
        match Ast_types.unroll_deep_node field.ftype with
        | TPtr { tnode = TComp structure; _ } ->
          (match get_struct_type structure with Sll sll_info -> Some (field, sll_info) | _ -> None)
        | _ -> None)
      other_pointers
  in
  (self_pointers, sll_pointers)

(** Determines, which list type a structure represents based on its fields *)
and get_struct_type (compinfo : compinfo) : struct_type =
  let self_pointers, sll_pointers = get_self_and_sll_fields compinfo in

  match (self_pointers, sll_pointers) with
  | _ when (Config.Validator.is_enabled ())
      || Config.Abstraction_mode.get () == `Synthesis -> Struct compinfo
  | [next_field], [] -> Sll {compinfo; next_field}
  | [top_field], [(down_field, sll_info)] -> Nl {compinfo; top_field; down_field; sll_info}
  | [next_field; prev_field], [] -> Dll {compinfo; next_field; prev_field}
  | _ -> Struct compinfo

(** Determines the type of field in the context of lists *)
let get_field_type (field : fieldinfo) : field_type =
  let self_pointers, sll_pointers = get_self_and_sll_fields field.fcomp in

  match (self_pointers, sll_pointers) with
  | _ when (Config.Validator.is_enabled ())
      || Config.Abstraction_mode.get () == `Synthesis ->
        Other field.fname
  | [ next ], [] when field.forder = next.forder -> Next
  (* DLL *)
  | [ next; _ ], [] when field.forder = next.forder -> Next
  | [ _; prev ], [] when field.forder = prev.forder -> Prev
  (* NL *)
  | [ top ], [ _ ] when field.forder = top.forder -> Top
  | [ _ ], [ (down, _) ] when field.forder = down.forder -> Next
  | _ -> if is_relevant_type field.ftype then Other field.fname else Data

module HT = Cil_datatype.Typ.Hashtbl

let type_info : (Sort.t * MemoryModel.StructDef.t) HT.t =
  HT.create 113

let structures : struct_type list ref = ref []

let c_field_to_astral field =
  let name = field.fname in
  let sort = match (Ast_types.unroll field.ftype).tnode with
  | TVoid -> Common.unsupported "void pointer"
  | TInt _ -> Sort.mk_loc "int"
  | TFloat _ -> Common.unsupported "float pointer"
  | TArray _ -> Common.unsupported "array pointer"
  | TFun _ -> Common.unsupported "function pointer"

  | TPtr { tnode = TComp structure; _ } -> Sort.mk_loc structure.cname
  | TNamed _ | TEnum _ | TPtr _ | TComp _ | TBuiltin_va_list -> assert false
  in
  MemoryModel.Field.mk name sort

let c_struct_to_astral structure =
  let name = structure.cname in
  let sort = Sort.mk_loc name in
  let c_fields = Option.get structure.cfields in
  let fields = List.map c_field_to_astral c_fields in
  (sort, MemoryModel.StructDef.mk name fields)

let rec get_type_info (typ : typ) : Sort.t * MemoryModel.StructDef.t =
  let typ : Cil_types.typ = Ast_types.unroll_deep typ in
  HT.find_opt type_info typ |> function
  | Some result -> result
  | None ->
      let dummy_struct_def = MemoryModel.StructDef.mk "dummy_struct_def" [] in
      let result =
        match typ.tnode with
        | TPtr { tnode = TComp structure; _ } ->
            let st = get_struct_type structure in
            structures := st :: !structures;
            (match st with
            | _ when Config.Validator.is_enabled () || Config.Abstraction_mode.get () == `Synthesis -> c_struct_to_astral structure
            | Sll _ -> (SL_builtins.loc_ls, SL_builtins.struct_ls)
            | Dll _ -> (SL_builtins.loc_dls, SL_builtins.struct_dls)
            | Nl _ -> (SL_builtins.loc_nls, SL_builtins.struct_nls)
            | _ -> c_struct_to_astral structure)
        | TPtr { tnode = TInt _; _ } ->
            let name = "intptr" in
            let sort = Sort.mk_loc name in
            let struct_def = MemoryModel.StructDef.mk name [] in
            (sort, struct_def)
        | TPtr inner ->
            let inner_sort = get_type_info inner |> fst in
            let name = Format.asprintf "ptr2%s" (Sort.show inner_sort) in
            let sort = Sort.mk_loc name in
            let field =
              MemoryModel.Field.mk Constants.ptr_field_name inner_sort
            in
            let struct_name = Format.asprintf "%s_wrapper" (Sort.show inner_sort) in
            let struct_def = MemoryModel.StructDef.mk struct_name ~cons:(struct_name ^ "_c") [ field ] in
            (sort, struct_def)
        | TVoid -> (Sort.mk_uninterpreted "void", dummy_struct_def)
        | TInt kind -> (Sort.int, dummy_struct_def)
        | t -> (Sort.loc_nil, dummy_struct_def)
      in
      if snd result <> dummy_struct_def then HT.add type_info typ result;
      result

let get_struct_def (sort : Sort.t) : MemoryModel.StructDef.t =
  HT.to_seq_values type_info
  |> Seq.find (fun (s, _) -> sort = s)
  |> Option.get |> snd

let sort_of_type typ =
  try fst @@ HT.find type_info typ
  with _ -> failwith @@ Format.asprintf "No type info for '%a'" Cil_datatype.Typ.pretty typ

(** Converts the type of a variable into its sort, and creates an SL variable *)
let varinfo_to_var (varinfo : Cil_types.varinfo) : SL.Variable.t =
  let name = Common.var_unique_name varinfo in
  if Ast_types.is_integral varinfo.vtype then
    SL.Variable.mk name (Sort.mk_bitvector 32)
  else if not @@ is_relevant_var varinfo then
    fail "invalid type in varinfo_to_var: %a" Printer.pp_varinfo varinfo
  else
    let sort = varinfo.vtype |> get_type_info |> fst in
    SL.Variable.mk name sort

(** Memoizes list types inside [get_type_info] *)
let process_types =
  object
    inherit Visitor.frama_c_inplace

    method! vtype (typ : typ) =
      if is_relevant_type typ then ignore @@ get_type_info typ;
      SkipChildren
  end

(** TODO: experimental output of witness *)
type pred = {
  origin_stmt : Cil_types.location;
  name : string;
  params : (string * string) list;
  definition : string;
}

let get_predicates () =
  let fn = function
    | Sll (compinfo, next_field) ->
      let typ = Format.asprintf "%s *" compinfo.corig_name in
      let name = Format.asprintf "sll_%s" compinfo.corig_name in
      Some {
        origin_stmt =
          (List.hd @@ Option.get compinfo.cfields).floc;
        name = name;
        params = [("start", typ);("end",typ)];
        definition =
          Format.asprintf
            {|(start == end) || (start != end &*& \canAccess(start, 1) &*& %s(start->%s, end))|}
            name
            next_field.forig_name;
      }
    | _ -> None
  in
  List.filter_map fn !structures

(** Generates struct definitions for generic structs and sets them in the solver*)
let process_types (file : file) =
  Visitor.visitFramacFileFunctions process_types file;

  Self.debug "Type information:";
  HT.iter (fun typ (sort, _) ->
    Self.debug ">  %a -> %a" Cil_printer.pp_typ typ Sort.pp sort) type_info;

  let heap_sort =
    HT.to_seq_values type_info |> List.of_seq |> HeapSort.of_list
  in
  Common.solver :=
    Some (Solver.add_heap_sort heap_sort (Option.get !Common.solver))
