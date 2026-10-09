open Dataflow2

(** This module is the entrypoint of the analysis, it runs the preprocessing and
    the dataflow analysis itself *)

module Self = Config.Self
module ForwardsAnalysis = Forwards (Analysis)

(** Check if there are any allocations left after the main function *)
let check_memcleanup main =
  let return_stmt = Kernel_function.find_return main in
  let final_state =
    Hashtbl.find !Func_call.function_context.results return_stmt
  in
  List.iter
    (fun formula ->
      Formula.get_spatial_atoms formula |> function
        (* TODO: should raise Memcleanup instead *)
      | atom :: _ -> Formula.report_bug (Invalid_memtrack (atom, formula))
      | _ -> ())
    final_state

let produce_correctness_witness () =
  if not @@ Config.Output_witness.is_default () then
    let results = Invariants.get () in
    let path = Filepath.to_string_abs @@ Config.Output_witness.get () in
    Correctness_witness.write results path
  else ()

let run_analysis () =
  Func_call.compute_function := ForwardsAnalysis.compute;

  (* run the preprocessing passes *)
  Preprocessing.preprocess ();

  let main, _ = Globals.entry_point () in
  let first_stmt = Kernel_function.find_first_stmt main in

  (* set [emp] as the initial state for the analysis *)
  Hashtbl.add !Func_call.function_context.results first_stmt [ [] ];

  (* run the dataflow analysis *)
  ForwardsAnalysis.compute [ first_stmt ];

  Func_call.merge_all_results ();
  produce_correctness_witness ();

  if Config.Check_memcleanup.get () then check_memcleanup main else ()

let verify () =
  (* run the analysis and catch exceptions representing bug detections *)
  (try
    run_analysis ();
    Self.result "Successful_verification"
  with
    | (Log.AbortError _ | Log.AbortFatal _ | Log.FeatureRequest _) as e -> raise e
    | e -> (
     let backtrace = Printexc.get_backtrace () in
     Common.warning "BACKTRACE: \n%s" backtrace;

     if !Analysis.unknown_condition_reached then Self.result "Unknown_result";

     match e with
     | Formula.Bug (bug_type, pos) ->
         if Config.Svcomp_mode.get () then Witness.write_witness bug_type pos;
         (* print the type of detected bug *)
         Self.result ~source:pos "%a" Formula.pp_bug_type bug_type
     | e ->
         Common.warning "EXCEPTION: %s" (Printexc.to_string e);
         if not @@ Config.Catch_exceptions.get () then raise e))
