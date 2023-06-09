include Interpreter

let view_run_state (run_state : Interpreter.run_state) =
  Format.printf "%t@." (Ast.print_process ~max_level:0 run_state.process)
