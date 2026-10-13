open Cil_types

let pointed_size_aux t = match t.tnode with
  | TPtr t -> Cil.bytesSizeOf t
  | _ -> assert false

let pointed_size v = match v.vtype.tnode with
  | TPtr t -> Cil.bytesSizeOf t
  | _ -> Cil.bytesSizeOf v.vtype

let compinfo_size c = Cil.bytesSizeOf @@ Cil_types.{tnode = TComp c; tattr = []}
