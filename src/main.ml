open Common

(* Common entrypoint of verifier and validator. *)
let main () =
  Printexc.record_backtrace true;

  UnsupportedChecker.run ();

  (* initialize the solver instance *)
  Astral_query.init ();

  if Config.Validator.is_enabled ()
  then Validator.validate @@ Config.Validator.Input.get ()
  else Verifier.verify ();

  Astral.Solver.dump_stats (Option.get !solver);
  Config.Self.result "Astral time: %.2f" !Astral_query.solver_time

(* register the analysis entrypoint into Frama-C  *)
let () =
  Boot.Main.extend (function
    | _ when Config.Print_version.get () -> print_endline "0.1"
    | _ when Config.Enable_analysis.get () -> main ()
    | _ -> ())
