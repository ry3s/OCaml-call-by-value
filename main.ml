open Syntax
open Parser
open Lexer
open Eval
open Print
open Type

let myml in_chan =
  let lexbuf = Lexing.from_channel in_chan in
  let rec repl env tenv =
    try
      let result = Parser.main Lexer.token lexbuf in
      let (ts,   t_newenv) = infer_cmd tenv result in
      let (newenv, value) = execute_cmd env result in
      List.iter (fun t ->
          print_string "- : ";
          print_type t;
          print_string " = ";) ts;
      print_value value;
      print_newline ();
      flush stdout;
      repl newenv t_newenv
	with
    | Eval.End -> ()
    | Type.End -> ()
    | Parsing.Parse_error ->
       (print_endline "Parse Error!"; repl env tenv)
  in
  repl [] []

let main () = if Array.length Sys.argv = 1 then
                myml stdin
              else
                let ic = open_in Sys.argv.(1) in
                myml ic


let () = if !Sys.interactive then
           ()
         else
           main ()
