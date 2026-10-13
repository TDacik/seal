open Astral
open Astral.Preprocessing
open SL
open MemoryModel

let is_const t = match SL.Term.view t with
  | SmtTerm t -> (match SMT.view t with
    | Variable _ -> false
    | BitConst _ -> true
    | _ -> assert false
  )
  | _ -> false

let is_int t = match SL.Term.view t with
  | SmtTerm _ -> true
  | _ -> false

let convert_smt_term t = match SMT.view t with
  | Variable v -> Obj.magic v (* TODO *)
  | _ -> failwith ("TODO: " ^ SMT.show t)

let convert_const t = match SL.Term.view t with
 | SmtTerm t -> begin match SMT.view t with
    | BitConst b -> Bitvector.to_int b
    | _ -> failwith ("not a constant: " ^ SMT.show t)
 end
 | _ -> assert false


let convert_term t = match SL.Term.view t with
  | Var v -> v
  | SmtTerm term -> convert_smt_term term
  | _ -> failwith ("TODO : " ^ SL.Term.show t)

let convert_target c ys =
  let f i y = (Field.show @@ List.nth (StructDef.get_fields c) i, convert_term y) in
  Formula.Generic (List.mapi f ys)

let convert_atom phi = match SL.view phi with
  | Emp -> Formula.Eq [Formula.nil; Formula.nil]
  | Eq [x; y] when is_const y -> Formula.IntEq (convert_term x, convert_const y)
  | Eq [x; y] when is_const x -> Formula.IntEq (convert_term y, convert_const x)
  | Eq xs -> Formula.Eq (List.map convert_term xs)
  | Distinct [x1; x2] -> Formula.Distinct (convert_term x1, convert_term x2)
  | PointsTo (x, c, [y]) when StructDef.is_lifted c -> Formula.Ref (convert_term x, convert_term y)
  | PointsTo (x, c, ys) -> Formula.PointsTo (convert_term x, convert_target c ys)
  | Predicate (name, ys, 0, _) -> Formula.Predicate (name, List.map convert_term ys)
  | _ -> failwith ("TODO " ^ SL.show phi)

let rec convert_sh phi = match SL.view phi with
  | Emp -> []
  | Star psis -> List.concat_map convert_sh psis
  | Exists (_, psi) -> convert_sh psi
  | _ -> [convert_atom phi]

let rec convert phi = match SL.view phi with
  | Or psis -> List.concat_map convert psis
  | Star _ ->
    let phi' = HeapTermElimination.apply phi in
    [convert_sh phi']
  | Exists (xs, psi) ->
    assert (List.for_all Common.is_fresh_var xs);
    convert psi
  | _ -> [[convert_atom @@ HeapTermElimination.apply phi]]
