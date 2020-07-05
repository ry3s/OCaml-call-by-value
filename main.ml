open Syntax
open Parser
open Lexer
open Eval
open Print
open Type

let repl in_chan =
  let lexbuf = Lexing.from_channel in_chan in
  let env = ref [] in
  let tenv = ref [] in
  let continue = ref true in
  while !continue do
    try
      let result = Parser.main Lexer.token lexbuf in
      let (ts, tenv') = infer_cmd !tenv result in
      let (env', value) = execute_cmd !env result in
      (List.iter (fun t ->
          print_string "- : ";
          print_type t;
          print_string " = ") ts;
      print_value value;
      print_newline ();
      flush stdout;
      env := env';
      tenv := tenv')
	with
    | Eval.End -> continue := false
    | Type.End -> continue := false
    | Parsing.Parse_error -> print_endline "Parse Error!"
  done

let main () = if Array.length Sys.argv = 1 then
                repl stdin
              else
                let ic = open_in Sys.argv.(1) in
                repl ic

let _ = main ()
