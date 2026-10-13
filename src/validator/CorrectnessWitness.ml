open Astral

module RawInvariant = struct

  type t = {
    location: int;             (*TODO: Cil_types.location*)
    raw_content: string;
    should_be_inductive : bool;
  }

end

module Invariant = struct

  type t = {
    location: int;              (*TODO: Cil_types.location*)
    raw_content: string;
    should_be_inductive : bool;
    content: SL.t;
  }

  let show self =
    match SL.view self.content with
    | Or psis ->
      List.map (fun psi -> Format.asprintf "    -> %s" (SL.show psi)) psis
      |> String.concat "\n"
    | _ ->
      List.map (fun psi -> Format.asprintf "    -> %s" (SL.show psi)) [self.content]
      |> String.concat "\n"

end

module InvariantMap = struct

  include Map.Make(Int)

  let show self =
    bindings self
    |> List.map (fun (line, invariant) -> Format.asprintf " - line %d:\n %s" line (Invariant.show invariant))
    |> String.concat "\n"

end

type witness = {
  (*input_file : string;
  input_file_hash : string;*)

  predicates: InductiveDefinition.t list;
  invariants: Invariant.t InvariantMap.t;
}

let empty = {predicates = []; invariants = InvariantMap.empty}

let pp fmt witness =
  Format.fprintf fmt "@[<v>Predicates:@,";
  List.iter (fun id -> InductiveDefinition.pp fmt id) witness.predicates;
  Format.fprintf fmt "@,\nInvariants:\n@,%s@]"
    (InvariantMap.show witness.invariants)
