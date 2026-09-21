(** Validator's entry point. *)

open Config
open Astral

(** Verdicts *)
let success = "Witness validated"
let reject = "Witness rejected"
let unknown = "Validation inconclusive"
let error = "Witness has errors"

let run_validation witness_path =
  Self.debug "Validating witness %a" Filepath.pretty_rel witness_path;
  let file = Ast.get () in
  Types.process_types file;

  let w = YamlParser.parse @@ Format.asprintf "%a" Filepath.pretty_abs witness_path in
  Self.debug "Input witness:\n%a" CorrectnessWitness.pp w;
  GlobalWitness.set w;
  Verifier.run_analysis ();
  Self.result "%s" success

let validate witness_path =
  try run_validation witness_path with e -> (
    match e with
    | Exceptions.MissingInvariant line ->
      Self.result "Invariant is missing for line %d" line;
      Self.result "%s" unknown
    | Exceptions.NotInvariant (state, invariant) ->
      (* TODO: When can we reject? *)
      Self.result "Formula provided for line %d may not be an invariant:" invariant.location;
      Self.result "%s" (SL.show invariant.content);
      Self.debug  "State is: %a" Formula.pp_state state;
      Self.result "%s" unknown
    | Exceptions.UnknownVariable (invariant, name) ->
      Self.result "Error when parsing invariant for line %d: %s" invariant.location invariant.raw_content;
      Self.result "  Variable %s does not exist in the current context" name;
      Self.result "%s" error
    | Formula.Bug (bug_type, pos) ->
      (* TODO: When can we reject? *)
      Self.result ~source:pos "%a" Formula.pp_bug_type bug_type;
      Self.result "%s" unknown
    | e ->
     let backtrace = Printexc.get_backtrace () in
     Common.warning "BACKTRACE: \n%s" backtrace;
     raise e
  )
