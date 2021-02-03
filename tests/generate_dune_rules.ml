(* Generates dune rules for each [.aeff] file *)
(* Taken from https://github.com/mirage/alcotest/blob/master/test/e2e/gen_dune_rules.ml *)

let src_suffix = ".aeff"

let test_script = "regression_test"

type config = { allowed_exit_code : int; args : string }

let parse_config =
  let l = Array.length Sys.argv in
  let allowed_exit_code = if l >= 2 then int_of_string Sys.argv.(1) else 0 in
  let args = if l >= 3 then Sys.argv.(2) ^ " " else "" in
  { allowed_exit_code; args }

let test_case_rule_stanza config (_bare, full_name) =
  Printf.printf "(rule\n";
  Printf.printf " (deps\n";
  Printf.printf "  ../../src/aeff/aeff.exe\n";
  Printf.printf "  (source_tree .))\n";
  Printf.printf "   (target \"%s.out\")\n" full_name;
  Printf.printf "    (action\n";
  Printf.printf "     (with-outputs-to \"%%{target}\"\n";
  Printf.printf "      (with-accepted-exit-codes\n";
  (* Just for now, ignore exit codes *)
  Printf.printf "       0\n";
  Printf.printf "       (run ../../src/aeff/aeff.exe %s\"./%s\")))))\n\n"
    config.args full_name

let test_case_alias_stanza (_bare, full_name) =
  let out_file_name = full_name ^ ".out" in
  Printf.printf "(rule\n";
  Printf.printf " (deps \"%s\")\n" out_file_name;
  Printf.printf "  (alias runtest)\n";
  Printf.printf "   (action\n";
  Printf.printf "    (diff \"%s.ref\" \"%s\")))\n\n" full_name out_file_name

let main () =
  let config = parse_config in
  Sys.readdir "." |> Array.to_list |> List.sort String.compare
  |> List.filter_map (fun full_name ->
         Option.map
           (fun bare -> (bare, full_name))
           (Filename.chop_suffix_opt ~suffix:src_suffix full_name))
  |> function
  | [] -> () (* no tests to execute *)
  | tests ->
      List.iter
        (fun test ->
          test_case_rule_stanza config test;
          test_case_alias_stanza test)
        tests

let () = main ()
