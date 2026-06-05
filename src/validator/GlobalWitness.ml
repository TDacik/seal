open CorrectnessWitness

let witness = ref CorrectnessWitness.empty

let set w = witness := w

let get_loop_invariant stmt =
  let line = Utils.stmt_line stmt in
  InvariantMap.find_opt line !witness.invariants
