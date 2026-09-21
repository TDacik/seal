open Cil_datatype

module H = Stmt.Hashtbl

let self : (Formula.state) H.t ref = ref (H.create 113 : Formula.state H.t)

let check_invariant inv =
  let vars = Formula.get_vars inv in
  if List.exists Common.is_fresh_var vars then
    Common.warning "Invariant contains existential variable ==> cannot generate witness."
  else ()

let add stmt f =
  List.iter check_invariant f;
  let current = try H.find !self stmt with Not_found -> [] in
  H.remove !self stmt;
  H.add !self stmt (f @ current)

let get () =
  H.filter_map_inplace (fun _ states -> Some (BatList.unique ~eq:Stdlib.(=) states)) !self;
  !self
