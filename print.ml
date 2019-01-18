open Syntax
open Eval
open Type
   
exception Print_error of string

let rec print_value : value -> unit = function 
  | VInt i -> print_int i
  | VBool b -> print_string (string_of_bool b)
  | VTuple t ->
     let rec loop = function
       | (v1 :: []) -> print_value v1
       | (v1 :: v2) -> print_value v1;
                       print_string ",";
                       loop v2
       | _ -> raise (Print_error __LOC__)
     in
     print_string "(";
     loop t;
     print_string ")"

  | VNil -> ()
  | VCons (v1, v2) ->
     let rec loop = function
       | VCons (v1, VRFun _) -> print_value v1;
                                print_string ";";
                                print_string "<fun>"
       | VCons (v1, VNil) -> print_value v1
       | VCons (v1,v2) -> print_value v1; 
                          print_string ";";
                          loop v2
       | _ -> raise (Print_error __LOC__)
     in
     print_string "[";
     loop (VCons (v1, v2));
     print_string "]"
     
  | VFun (x, e, env) -> print_string ("<fun>")
  | VRFun (f, x, e, env) -> print_string ("<fun>")
  | VMRFun (f, li, env) -> print_string ("<fun>")

let rec print_type : ty -> unit = function
  | TInt -> print_string "int"
  | TBool -> print_string "bool"
  | TFun (t1, t2) -> print_type t1;
                     print_string " -> ";
                     print_type  t2
  | TVar tv -> print_string ("t" ^ (string_of_int tv))
  | TTuple t ->
     let rec loop = function
       | (t1 :: []) -> print_type t1
       | (t1 :: t2) -> print_type t1;
                       print_string " * ";
                       loop t2
       | _ -> raise (Print_error __LOC__)
     in
     print_string "(";
     loop t;
     print_string ")"          
  (* | TTuple t ->
   *   
   *    List.iter (fun x -> print_type x;
   *                        print_string " * ") t;
   *     print_string "(";
   *    (\* print_string "\b\b\b" *\) *)
    
  | TList t -> print_type t; print_string " list"
