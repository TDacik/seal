open Astral
open Common

(** This module implements the abstraction that turns chains of pointer atoms
    into list predicates *)

(** checks that [var] is a fresh variable unreachable from the formula *)
let is_unique_fresh (var : Formula.var) (formula : Formula.t) : bool =
  is_fresh_var var && Formula.count_relevant_occurences var formula = 2

(* checks that a spatial atom is present in a formula *)
let is_in_formula (src : Formula.var) (dst : Formula.var)
    (field : Types.field_type) (formula : Formula.t) : bool =
  Formula.get_spatial_atom_from_first_opt src formula |> function
  | Some atom ->
      Formula.get_target_of_atom field atom |> fun atom_dst ->
      Formula.is_eq atom_dst dst formula
  | None -> false

(** LS abstraction *)

let convert_to_ls (formula : Formula.t) : Formula.t =
  let atom_to_ls (atom : Formula.atom) : Formula.ls option =
    atom |> Formula.pto_to_list |> function
    | Formula.LS ls -> Some ls
    | _ -> None
  in

  let do_abstraction (formula : Formula.t) (first_ls : Formula.ls) : Formula.t =
    match
      formula
      |> Formula.get_spatial_atom_from_opt first_ls.next
      |> Option.map atom_to_ls |> Option.join
    with
    | Some second_ls
    (* conditions for abstraction *)
      when (* first_ls must still be in formula *)
           is_in_formula first_ls.first first_ls.next Types.Next formula
           (* middle must be fresh variable, and occur only in these two predicates *)
           && is_unique_fresh first_ls.next formula
           (* src must be different from dst (checked using solver) or dst must be nil *)
           && (Astral_query.check_inequality first_ls.first second_ls.next formula
              || SL.Variable.is_nil second_ls.next) ->
        let min_length = min 2 (first_ls.min_len + second_ls.min_len) in
        formula
        |> Formula.remove_spatial_from first_ls.first
        |> Formula.remove_spatial_from second_ls.first
        |> Formula.add_atom
           @@ Formula.mk_ls second_ls.info first_ls.first second_ls.next min_length
    | _ -> formula
  in

  formula |> List.filter_map atom_to_ls |> List.fold_left do_abstraction formula

(** DLS abstraction *)

let convert_to_dls ?(allow_prog_var_as_last=false) (formula : Formula.t) : Formula.t =
  let atom_to_dls (atom : Formula.atom) : Formula.dls option =
    atom |> Formula.pto_to_list |> function
    | Formula.DLS dls -> Some dls
    | _ -> None
  in

  let do_abstraction (formula : Formula.t) (first_dls : Formula.dls) : Formula.t
      =
    match
      formula
      |> Formula.get_spatial_atom_from_opt first_dls.next
      |> Option.map atom_to_dls |> Option.join
    with
    | Some second_dls
    (* conditions for abstraction *)
      when (* first_dls must still be in formula *)
           is_in_formula first_dls.first first_dls.next Types.Next formula

           (* Do not include program variables as last parameter of DLS. Needed
              just to produce witnesses that are easier to validate. *)
           && (allow_prog_var_as_last || Common.is_fresh_var second_dls.last)
           (* middle vars must be fresh, and occur only in these two predicates *)
           && (SL.Variable.equal first_dls.first first_dls.last
              || is_unique_fresh first_dls.last formula)
           && (SL.Variable.equal second_dls.first second_dls.last
              || is_unique_fresh second_dls.first formula)
           (* [prev] pointer from second DLS must lead to end of the previous DLS *)
           && Formula.is_eq first_dls.last second_dls.prev formula
           (* prev and next cannot point back into the list *)
           && (not @@ Formula.is_eq first_dls.first first_dls.prev formula)
           && (not @@ Formula.is_eq second_dls.last second_dls.next formula)
           (* DLS must not be cyclic (checked both forward and backward) *)
           && (Astral_query.check_inequality first_dls.first second_dls.next
                formula || SL.Variable.is_nil second_dls.next)
           && (Astral_query.check_inequality second_dls.last first_dls.prev
                formula || SL.Variable.is_nil first_dls.prev) ->
        let min_length = min 3 (first_dls.min_len + second_dls.min_len) in
        formula
        |> Formula.remove_spatial_from first_dls.first
        |> Formula.remove_spatial_from second_dls.first
        |> Formula.add_atom
           @@ Formula.mk_dls second_dls.info first_dls.first second_dls.last first_dls.prev
                second_dls.next min_length
    | _ -> formula
  in

  formula
  |> List.filter_map atom_to_dls
  |> List.fold_left do_abstraction formula

(** NLS abstraction *)

(** tries to unify the sublists of two nls atoms, returns modified formula and
    new [next] var if join succeeded *)
let unify_sublists (lhs_source : Formula.var) (rhs_source : Formula.var)
    (formula : Formula.t) : (Formula.t * Formula.var) option =
  let lhs = Formula.get_spatial_atom_from lhs_source formula in
  let rhs = Formula.get_spatial_atom_from rhs_source formula in

  let lhs_next = Formula.get_target_of_atom Types.Next lhs in
  let rhs_next = Formula.get_target_of_atom Types.Next rhs in

  let lhs_target = Formula.get_spatial_target_opt lhs_next Types.Next formula in
  let rhs_target = Formula.get_spatial_target_opt rhs_next Types.Next formula in

  let ( = ) x y = Formula.is_eq x y formula in
  let uf x = is_unique_fresh x formula in

  match (lhs, rhs, lhs_target, rhs_target) with
  (* pto + pto can both have sublists *)
  | PointsTo _, PointsTo _, _, _ when lhs_next = rhs_next ->
      Some (formula, lhs_next)
  | PointsTo _, PointsTo _, Some lhs_target, _
    when lhs_target = rhs_next && uf lhs_next ->
      Some (Formula.remove_spatial_from lhs_next formula, lhs_target)
  | PointsTo _, PointsTo _, Some lhs_target, Some rhs_target
    when lhs_target = rhs_target && uf lhs_next && uf rhs_next ->
      Some
        ( Formula.remove_spatial_from lhs_next formula
          |> Formula.remove_spatial_from rhs_next,
          lhs_target )
  (* list + pto -- only pto can have a sublist *)
  | NLS _, PointsTo _, _, _ when lhs_next = rhs_next -> Some (formula, lhs_next)
  | NLS _, PointsTo _, _, Some rhs_target
    when lhs_next = rhs_target && uf rhs_next ->
      Some (Formula.remove_spatial_from rhs_next formula, lhs_next)
  (* list + list -- next fields must match directly *)
  | NLS _, NLS _, _, _ when lhs_next = rhs_next -> Some (formula, lhs_next)
  | _ -> None

(* tries to unify the sublists in both directions *)
let join_sublists (lhs_source : Formula.var) (rhs_source : Formula.var)
    (formula : Formula.t) : (Formula.t * Formula.var) option =
  unify_sublists lhs_source rhs_source formula |> function
  | Some res -> Some res
  | None -> unify_sublists rhs_source lhs_source formula

let convert_to_nls (formula : Formula.t) : Formula.t =
  let atom_to_nls (atom : Formula.atom) : Formula.nls option =
    atom |> Formula.pto_to_list |> function
    | Formula.NLS nls -> Some nls
    | _ -> None
  in

  let do_abstraction (formula : Formula.t) (first_nls : Formula.nls) : Formula.t
      =
    match
      formula
      |> Formula.get_spatial_atom_from_opt first_nls.top
      |> Option.map atom_to_nls |> Option.join
    with
    | Some second_nls
    (* conditions for abstraction *)
      when (* first_nls must still be in formula *)
           is_in_formula first_nls.first first_nls.top Types.Top formula
           (* middle must be fresh variable, and occur only in these two predicates *)
           && is_unique_fresh first_nls.top formula
           (* src must be different from dst (checked using solver) or dst must be nil *)
           && (Astral_query.check_inequality first_nls.first second_nls.top formula
               || SL.Variable.is_nil second_nls.top) -> (
        (* common variable `next` must lead to the same target *)
        match join_sublists first_nls.first second_nls.first formula with
        | Some (formula, next) ->
            let min_length = min 2 (first_nls.min_len + second_nls.min_len) in
            formula
            |> Formula.remove_spatial_from first_nls.first
            |> Formula.remove_spatial_from second_nls.first
            |> Formula.add_atom
               @@ Formula.mk_nls second_nls.info first_nls.first second_nls.top next min_length
        | None -> formula)
    | _ -> formula
  in

  formula
  |> List.filter_map atom_to_nls
  |> List.fold_left do_abstraction formula

let apply formula =
  formula
  |> convert_to_ls
  |> convert_to_dls
  |> convert_to_nls

module Tests_LS = struct
  open Testing

  let () = Astral_query.init ()

  (* LS abstraction *)

  let%test "abstraction_ls_nothing" =
    let input = [ mk_pto_ls x y'; mk_pto_ls y' z ] in
    assert_eq (convert_to_ls input) input

  let%test "abstraction_ls_1" =
    let input = [ mk_pto_ls x y'; mk_pto_ls y' z; Distinct (x, z) ] in
    let result = convert_to_ls input in
    let expected = [ mk_ls x z 2; Distinct (x, z) ] in
    assert_eq result expected

  let%test "abstraction_ls_1_nil" =
    let input = [ mk_pto_ls x y'; mk_pto_ls y' nil ] in
    let result = convert_to_ls input in
    let expected = [ mk_ls x nil 2 ] in
    assert_eq result expected

  let%test "abstraction_ls_2" =
    let input =
      [
        mk_pto_ls x y';
        mk_pto_ls y' z;
        mk_pto_ls u v';
        mk_pto_ls v' w;
        Distinct (u, w);
      ]
    in
    let result = convert_to_ls input in
    let expected =
      [
        mk_pto_ls x y';
        mk_pto_ls y' z;
        mk_ls u w 2;
        Distinct (u, w);
      ]
    in
    assert_eq result expected

  let%test "abstraction_ls_3" =
    let input =
      [
        mk_pto_ls x y';
        mk_pto_ls y' z';
        mk_pto_ls z' w;
        Distinct (x, w);
      ]
    in
    let result = convert_to_ls input in
    let expected = [ mk_ls x z' 2; mk_pto_ls z' w; Distinct (x, w) ] in
    assert_eq result expected

  let%test "abstraction_ls_double" =
    let input =
      [
        mk_pto_ls x y';
        mk_pto_ls y' z';
        mk_pto_ls z' w;
        Distinct (x, w);
      ]
    in
    let result = convert_to_ls @@ convert_to_ls input in
    let expected = [ mk_ls x w 2; Distinct (x, w) ] in
    assert_eq result expected

  let%test "abstraction_ls_from_ls+pto" =
    let input =
      [ mk_ls x y' 1; mk_pto_ls y' nil ]
    in
    let result = convert_to_ls input in
    let expected = [ mk_ls x nil 2 ] in
    assert_eq result expected

  let%test "abstraction_ls_from_ls+ls" =
    let input =
      [
        mk_ls x y' 0;
        mk_ls y' nil 1;
      ]
    in
    let result = convert_to_ls input in
    let expected = [ mk_ls x nil 1 ] in
    assert_eq result expected
end

module Tests_DLS = struct
  open Testing
  open DLS (* test vars with dls sort *)

  let () = Astral_query.init ()

  let convert_to_dls = convert_to_dls ~allow_prog_var_as_last:true

  (* DLS abstraction *)

  let%test "abstraction_dls_nothing" =
    let input =
      [
        mk_pto_dls u v' z;
        mk_pto_dls v' w u;
        mk_pto_dls w x v';
        Distinct (u, x);
      ]
    in
    assert_eq (convert_to_dls input) input

  let%test "abstraction_dls_from_pto" =
    let input =
      [ mk_pto_dls u' v' nil; mk_pto_dls v' nil u' ]
    in
    let expected = [ mk_dls u' v' nil nil 2 ] in
    assert_eq (convert_to_dls input) expected

  let%test "abstraction_dls_1" =
    let input =
      [
        mk_pto_dls u v z;
        mk_pto_dls v w u;
        Distinct (v, z);
        Distinct (u, w);
      ]
    in
    let expected = [ mk_dls u v z w 2; Distinct (v, z); Distinct (u, w) ] in
    assert_eq (convert_to_dls input) expected

  let%test "abstraction_dls_2" =
    let input =
      [
        mk_pto_dls u v' z;
        mk_pto_dls v' w u;
        mk_pto_dls w x v';
        Distinct (v', z);
      ]
    in
    let expected =
      [ mk_dls u v' z w 2; mk_pto_dls w x v'; Distinct (v', z) ]
    in
    assert_eq (convert_to_dls @@ convert_to_dls input) expected

  let%test "abstraction_dls_2_double" =
    let input =
      [
        mk_pto_dls u v' z;
        mk_pto_dls v' w u;
        mk_pto_dls w x v';
        Distinct (v', z);
        Distinct (z, w);
        Distinct (x, u);
      ]
    in
    let expected =
      [ mk_dls u w z x 3; Distinct (v', z); Distinct (z, w); Distinct (x, u) ]
    in
    assert_eq (convert_to_dls @@ convert_to_dls input) expected

  let%test "abstraction_dls_long_from_pto" =
    let input =
      [
        mk_pto_dls u v z;
        mk_pto_dls v w u;
        mk_pto_dls w x v;
        mk_pto_dls x y w;
        mk_pto_dls y z x;
      ]
    in
    assert_eq (convert_to_dls input)
      [
        mk_pto_dls u v z;
        mk_dls v w u x 2;
        mk_pto_dls x y w;
        mk_pto_dls y z x;
      ]

  let%test "abstraction_dls_long_from_pto_2" =
    let input =
      [
        mk_pto_dls u v z;
        mk_pto_dls v w' u;
        mk_pto_dls w' x v;
        mk_pto_dls x y w';
        mk_pto_dls y z x;
      ]
    in
    assert_eq
      (convert_to_dls @@ convert_to_dls input)
      [
        mk_pto_dls u v z; mk_dls v x u y 3; mk_pto_dls y z x;
      ]

  let%test "abstraction_dls_from_dls+pto" =
    let input =
      [
        mk_dls x y' nil z 1;
        mk_pto_dls z nil y';
      ]
    in
    let expected = [ mk_dls x z nil nil 2 ] in
    assert_eq (convert_to_dls input) expected

  let%test "abstraction_dls_from_dls+dls" =
    let input =
      [
        mk_dls x y' nil z' 1;
        mk_dls z' w y' nil 2;
      ]
    in
    let expected = [ mk_dls x w nil nil 3 ] in
    assert_eq (convert_to_dls input) expected
end

module Tests_NLS = struct
  open Testing

  module LS = Testing (* LS variables *)
  open NLS            (* NLS variables *)

  let () = Astral_query.init ()

  (* NLS abstraction *)

  let%test "abstraction_nls_nothing" =
    let input =
      [ mk_pto_nls x y' nil; mk_pto_nls y' z nil ]
    in
    assert_eq (convert_to_nls input) input

  let%test "abstraction_nls_nothing_2" =
    let input =
      [
        mk_pto_nls x y' nil;
        mk_pto_nls y' z LS.w;
        Distinct (x, z);
      ]
    in
    let result = convert_to_nls input in
    assert_eq result input

  let%test "abstraction_nls_1" =
    let input =
      [
        mk_pto_nls x y' nil;
        mk_pto_nls y' z nil;
        Distinct (x, z);
      ]
    in
    let result = convert_to_nls input in
    let expected = [ mk_nls x z nil 2; Distinct (x, z) ] in
    assert_eq result expected

  let%test "abstraction_nls_1_nil" =
    let input =
      [ mk_pto_nls x y' nil; mk_pto_nls y' nil nil ]
    in
    let result = convert_to_nls input in
    let expected = [ mk_nls x nil nil 2 ] in
    assert_eq result expected

  let%test "abstraction_nls_2" =
    let input =
      [
        mk_pto_nls x y' nil;
        mk_pto_nls y' z nil;
        mk_pto_nls u v' nil;
        mk_pto_nls v' w nil;
        Distinct (u, w);
      ]
    in
    let result = convert_to_nls input in
    let expected =
      [
        mk_pto_nls x y' nil;
        mk_pto_nls y' z nil;
        mk_nls u w nil 2;
        Distinct (u, w);
      ]
    in
    assert_eq result expected

  let%test "abstraction_nls_3" =
    let input =
      [
        mk_pto_nls x y' nil;
        mk_pto_nls y' z' nil;
        mk_pto_nls z' w nil;
        Distinct (x, w);
      ]
    in
    let result = convert_to_nls input in
    let expected =
      [ mk_nls x z' nil 2; mk_pto_nls z' w nil; Distinct (x, w) ]
    in
    assert_eq result expected

  let%test "abstraction_nls_double" =
    let input =
      [
        mk_pto_nls x y' nil;
        mk_pto_nls y' z' nil;
        mk_pto_nls z' w nil;
        Distinct (x, w);
      ]
    in
    let result = convert_to_nls @@ convert_to_nls input in
    let expected = [ mk_nls x w nil 2; Distinct (x, w) ] in
    assert_eq result expected

  let%test "abstraction_nls_with_ls_0" =
    let input =
      [
        mk_pto_nls x y' LS.z';
        mk_pto_nls y' u LS.v';
        Distinct (x, u);
        mk_ls LS.z' nil 0;
        mk_ls LS.v' nil 0;
      ]
    in
    let result = convert_to_nls input in
    let expected = [ mk_nls x u nil 2; Distinct (x, u) ] in
    assert_eq result expected

  let%test "abstraction_nls_with_ls_different_lengths" =
    let input =
      [
        mk_pto_nls x y' LS.z';
        mk_pto_nls y' u LS.v';
        Distinct (x, u);
        mk_ls LS.z' nil 1;
        mk_ls LS.v' nil 1;
      ]
    in
    let result = convert_to_nls input in
    let expected = [ mk_nls x u nil 2; Distinct (x, u) ] in
    assert_eq result expected

  let%test "abstraction_nls_with_ls_different_lengths_2" =
    let input =
      [
        mk_pto_nls x y' LS.z';
        mk_pto_nls y' nil LS.v';
        mk_ls LS.z' nil 1;
        mk_ls LS.v' nil 2;
      ]
    in
    let result = convert_to_nls input in
    let expected = [ mk_nls x nil nil 2 ] in
    assert_eq result expected
end
