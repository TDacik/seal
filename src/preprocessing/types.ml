open Cil
open Cil_types
open Astral
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
  | TPtr _ -> true
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

(** Create canonical sort representing pointer to the given structure. *)
let struct_ptr_sort structure =
  Sort.mk_loc ("Ptr_" ^ structure.cname)

(** Convert C type to Astral sort. *)
let rec c_type_to_astral typ =
  match (Ast_types.unroll_deep typ).tnode with
  | TInt _ -> Sort.mk_bitvector @@ Cil.bitsSizeOf typ
  | TPtr { tnode = TComp structure; _ } -> struct_ptr_sort structure
  | TPtr t -> Sort.mk_loc ("Ptr_" ^ Sort.name @@ c_type_to_astral t)
  | TVoid -> Sort.mk_uninterpreted "void" (* TODO: should Astral have a void/unit sort? *)

  | TFloat _ -> Common.unsupported "float type"
  | TArray _ -> Common.unsupported "array type"
  | TFun _ -> Common.unsupported "function pointer type"

  | TNamed _ -> assert false
  | TEnum _ | TComp _ | TBuiltin_va_list ->
      failwith @@ Format.asprintf "%a" Cil_printer.pp_typ typ

let c_field_to_astral field =
  let name = field.fname in
  let sort = c_type_to_astral field.ftype in
  MemoryModel.Field.mk name sort

let c_struct_to_astral structure =
  let name = structure.cname in
  let c_fields = Option.get structure.cfields in
  let fields = List.map c_field_to_astral c_fields in
  MemoryModel.StructDef.mk name fields

let c_atomic_type_to_astral_struct typ =
  let sort = c_type_to_astral typ in
  let field_name = Format.asprintf "%s_next" (Sort.name sort) in
  MemoryModel.StructDef.lift_sort ~field_name sort

let get_type_info typ =
  let default_sort = c_type_to_astral typ in
  let sort, struct_def =
    match (Ast_types.unroll_deep typ).tnode with
    | TPtr { tnode = TComp structure; _ } ->
        if Config.Validator.is_enabled () || Config.Abstraction_mode.get () == `Synthesis
        then default_sort, Option.some @@ c_struct_to_astral structure
        else (
          let st = get_struct_type structure in
          structures := st :: !structures;
          match st with
          | Sll _ -> (SL_builtins.loc_ls, Option.Some SL_builtins.struct_ls)
          | Dll _ -> (SL_builtins.loc_dls, Option.Some SL_builtins.struct_dls)
          | Nl _ -> (SL_builtins.loc_nls, Option.Some SL_builtins.struct_nls)
          | _ -> default_sort, Option.some @@ c_struct_to_astral structure)
    | TPtr t ->
      default_sort, Option.some @@ c_atomic_type_to_astral_struct t
    | _ -> default_sort, None
  in
  let _ = match struct_def with
  | None -> ()
  | Some def -> HT.add type_info typ (sort, def)
  in
  (sort, struct_def)

let get_struct_def (sort : Sort.t) : MemoryModel.StructDef.t =
  match Seq.find (fun (s, _) -> Sort.equal sort s) @@ HT.to_seq_values type_info with
  | Some (_, def) -> def
  | None -> Config.Self.abort "No structure for sort %a" Sort.pp sort

let sort_of_type typ =
  try fst @@ HT.find type_info typ
  with _ -> failwith @@ Format.asprintf "No type info for '%a'" Cil_datatype.Typ.pretty typ

let get_target_struct_def varinfo =
  sort_of_type varinfo.vtype
  |> get_struct_def

(** Memoizes list types inside [get_type_info] *)
let process_types =
  object
    inherit Visitor.frama_c_inplace

    method! vtype (typ : typ) =
      if is_relevant_type typ then ignore @@ get_type_info typ;
      SkipChildren
  end

(** Generates struct definitions for generic structs and sets them in the solver*)
let process_types (file : file) =
  Visitor.visitFramacFileFunctions process_types file;

  Self.debug "Type information:";
  HT.iter (fun typ (sort, def) ->
    Self.debug ">  %a -> %a : %s"
      Cil_printer.pp_typ typ Sort.pp sort (MemoryModel.StructDef.show def)) type_info;

  let heap_sort =
    HT.to_seq_values type_info |> List.of_seq |> HeapSort.of_list
  in
  Common.solver :=
    Some (Solver.add_heap_sort heap_sort (Option.get !Common.solver))
