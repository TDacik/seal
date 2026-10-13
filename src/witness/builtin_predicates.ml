(** Output of builtin predicates *)

open Cil_types
open AbstractionHint

type pred = {
  origin_stmt : Cil_types.location;
  name : string;
  params : (string * string) list;
  definition : string;
}

(** Return the statement where the last field of the structure is defined. *)
let get_origin_stmt compinfo =
  (List.hd @@ List.rev @@ Option.get compinfo.cfields).floc

let sll_definitions (info : sll_info) =
  let typ = Format.asprintf "struct %s *" info.compinfo.corig_name in
  let name = AbstractionHint.sll_name info in

  let origin_stmt = get_origin_stmt info.compinfo in
  let params = [("start", typ); ("end", typ)] in
  let definition =
    Format.asprintf
      {|(start == end) || (start != end && \separated(\canAccess(start, %d), %s(start->%s, end)))|}
      (CorrectnessWitnessUtils.compinfo_size info.compinfo)
      name info.next_field.forig_name
  in
  [{origin_stmt; name; params; definition}]

let dll_definitions (info : dll_info) =
  let typ = Format.asprintf "struct %s *" info.compinfo.corig_name in
  let name = AbstractionHint.dll_name info in

  (* Full dls *)
  let origin_stmt = get_origin_stmt info.compinfo in
  let params = [("start", typ); ("end" ,typ); ("start_back", typ); ("end_back", typ)] in
  let definition =
    Format.asprintf
      {|(start == end && start_back == end_back) || (start != end && start_back != end_back && start->%s == end_back && \separated(\canAccess(start, %d), %s(start->%s, end, start_back, start)))|}
      info.prev_field.forig_name
      (CorrectnessWitnessUtils.compinfo_size info.compinfo)
      name
      info.next_field.forig_name
  in
  let name' = name ^ "_simple" in
  let params' = [("start", typ); ("end", typ); ("end_back", typ)] in
  let definition' =
    Format.asprintf
      {|(start == end) || (start != end && start->%s == end_back && \separated(\canAccess(start, %d), %s(start->%s, end, start)))|}
      info.prev_field.forig_name
      (CorrectnessWitnessUtils.compinfo_size info.compinfo)
      name'
      info.next_field.forig_name
  in
  [
    {origin_stmt; name; params; definition};
    {origin_stmt; name=name'; params=params'; definition=definition'}
  ]

let nll_definitions info =
  let ls_name = AbstractionHint.sll_name info.sll_info in
  let name = AbstractionHint.nll_name info in
  let ls_typ = Format.asprintf "struct %s *" info.sll_info.compinfo.corig_name in
  let nls_typ = Format.asprintf "struct %s *" info.compinfo.corig_name in

  let origin_stmt = get_origin_stmt info.compinfo in
  let params = [("start", nls_typ); ("end", nls_typ); ("sink", ls_typ)] in
  let definition =
    Format.asprintf
      {|(start == end) || (start != end && \separated(\canAccess(start, %d), %s(start->%s, end, sink), %s(start->%s, sink)))|}
      (CorrectnessWitnessUtils.compinfo_size info.compinfo)
      name
      info.top_field.forig_name
      ls_name
      info.down_field.forig_name
  in
  [{origin_stmt; name; params; definition}]

let get_predicates () =
  let open Types in
  let fn info = match info with
    | Sll info -> sll_definitions info
    | Dll info -> dll_definitions info
    | Nl info -> nll_definitions info
    | _ -> []
  in
  List.concat_map fn !Types.structures
