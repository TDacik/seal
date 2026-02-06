(** Signature of backend. *)

open Astral

module type CONVERTOR = sig
  val init :
    backend:AstralConfig.Backend.t ->
    encoding:AstralConfig.Encoding.t ->
    dump_queries:[ `None | `Full of string ] ->
    unit ->
    Solver.solver

  val convert : Formula.t -> Astral.SL.t
end
