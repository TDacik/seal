open Cil_types
open Cil_datatype

type sll_info = {
  compinfo : Compinfo.t;
  next_field : Fieldinfo.t;
} [@@deriving compare, equal]

type dll_info = {
  compinfo : Compinfo.t;
  next_field : Fieldinfo.t;
  prev_field : Fieldinfo.t;
} [@@deriving compare, equal]

type nll_info = {
  compinfo : Compinfo.t;
  top_field : Fieldinfo.t;
  down_field : Fieldinfo.t;
  (** The toplevel structure may use a different field name for the 'next'
      selector than the sll structure. *)
  sll_info : sll_info;
} [@@deriving compare, equal]

type t =
  | LS of sll_info
  | DLS of dll_info
  | NLS of nll_info
  [@@ deriving compare, equal]

let sll_name (sll : sll_info) =
  Format.asprintf "sll__%s__%s"
    (sll.compinfo.corig_name)
    (sll.next_field.forig_name)

let dll_name (dll : dll_info) =
  Format.asprintf "dll__%s__%s_%s"
    (dll.compinfo.corig_name)
    (dll.next_field.forig_name)
    (dll.prev_field.forig_name)

let nll_name (nll : nll_info) =
  Format.asprintf "nll__%s_%s_%s__%s_%s"
    (nll.compinfo.corig_name)
    (nll.sll_info.compinfo.corig_name)
    (nll.top_field.forig_name)
    (nll.down_field.forig_name)
    (nll.sll_info.next_field.forig_name)
