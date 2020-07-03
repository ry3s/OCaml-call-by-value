(* TODO: f p = e -> f x = match x with p -> e *)
(* DONE: pattern _ *)
(* TODO: pair hukusuu *)
open Syntax
open Type
exception Eval_error of string
exception End

let rec find_match : pattern -> value -> env option = fun pattern value ->
  begin match (pattern, value) with
  | (PInt pn, VInt n) -> if pn = n then Some [] else None
  | (PBool pb, VBool b) -> if pb = b then Some [] else None
  | (PVar x, v) -> Some [(x, v)]
  | (PTuple ps, VTuple vs) ->
     let n = List.length ps in
     let m = List.length vs in
     if n <> m then
       None
     else
       List.fold_left2 (fun acc p v ->
           match acc with
           | None -> None
           | Some acc ->
              begin match find_match p v with
              | Some env -> Some (env @ acc)
              | None -> None
              end
         ) (Some []) ps vs
  | (PNil, VNil) -> Some []
  | (PCons (px, py), VCons (vx, vy)) ->
     let envx = find_match px vx in
     let envy = find_match py vy in
     begin
       match (envx, envy) with
       | (Some ex, Some ey) -> Some (ex @ ey)
       | _ -> None
     end
  | (PUnderscore, _) -> Some []
  | _ -> None
  end

let rec  eval : env -> expr -> value = fun env ->
  function
  | EValue v -> v
  | EVar x -> List.assoc x env
  | EBin (op, e1, e2) ->
     let (e1', e2') = (eval env e1, eval env e2) in
     begin match (op, e1', e2') with
     | (OpAdd, VInt x1, VInt x2) -> VInt (x1 + x2)
     | (OpSub, VInt x1, VInt x2) -> VInt (x1 - x2)
     | (OpMul, VInt x1, VInt x2) -> VInt (x1 * x2)
     | (OpDiv, VInt x1, VInt x2) -> VInt (x1 / x2)
     | (OpEq , VInt x1, VInt x2) -> VBool (x1 = x2)
     | (OpLt , VInt x1, VInt x2) -> VBool (x1 < x2)
     | (OpEq , VBool b1, VBool b2) -> VBool (b1 = b2)
     | (OpLt , VBool b1, VBool b2) -> VBool (b1 < b2)
     | _ -> raise (Eval_error __LOC__)
     end
  | ETuple tuple_li -> VTuple (List.map (fun x -> eval env x) tuple_li)

  | ENil -> VNil
  | ECons (e1, e2) -> let v1 = eval env e1 in
                      let v2 = eval env e2 in
                      VCons (v1, v2)
  | ELet (pattern, e1, e2) ->
     let v1 = eval env e1 in
     let env' = find_match pattern v1 in
     begin match env' with
     | Some newenv -> eval (newenv@env) e2
     | None -> raise (Eval_error __LOC__)
     end
  | ERLet (f, x, e1, e2) -> let env' = (f, VRFun (f, x, e1, env))::env in
                            eval env' e2
  | EFun (x, e) -> VFun (x, e, env)
  | EApp (e1, e2) ->
     let v1 = eval env e1 in
     let v2 = eval env e2 in
     begin match v1 with
     | VFun  (x, e, oenv) -> eval ((x, v2)::oenv) e
     | VRFun (f, x, e, oenv) ->
        let env' = (x, v2)::(f, VRFun (f, x, e,oenv))::oenv in
        eval env' e
     | VMRFun (i, funli, oenv) ->
        (* fold_right or mapi  *)
        let rec iter = fun n -> function
                             | ((f, x, e) :: xs) ->
                                (f, VMRFun (n, funli, oenv)) :: (iter (n + 1) xs)
                             | [] -> []
        in
        let (f, x, e) = List.nth funli (i - 1) in
        let env' = (x, v2) :: (iter 1 funli) @ oenv in
        eval env' e
     | _ -> raise (Eval_error  __LOC__)
     end

  | EIf (e1, e2, e3) ->
     begin match eval env e1 with
     | VBool true -> eval env e2
     | VBool false -> eval env e3
     | _ -> raise (Eval_error __LOC__)
     end


  | EMatch (e1, pattern_list) ->
     let v1 = eval env e1 in
     let rec check : value -> (pattern * expr) list -> value =
       fun value p_list ->
       begin match p_list with
       | ((pattern, exp)::xs) ->
          let env_option = find_match pattern value in
          begin match env_option with
          | Some [] -> eval env exp
          | Some newenv  -> eval (newenv@env) exp
          | None -> check value xs
          end
       | [] -> raise (Eval_error __LOC__)
       end
     in
     check v1 pattern_list;;

let execute_cmd : env -> command  -> env * value =
  fun env value ->
  match value with
  | CExp exp -> (env, eval env exp)
  | CLet (pattern, expr) ->
     let v = eval env expr in
     let env' = find_match pattern v in
     begin match env' with
     | Some newenv -> (newenv @ env, v)
     | None -> raise (Eval_error __LOC__)
     end
  | CRLet (f, x, e) -> ((f, VRFun (f, x, e, env))::env, VRFun (f, x, e, env))
  | CMRLet funlist ->
     let rec iter = fun n -> function
                          | ((f, x, e) :: xs) -> (f, VMRFun (n, funlist, env)) :: (iter (n + 1) xs)
                          | [] -> []
     in
     let newenv =  (iter 1 funlist) @ env in
     (newenv, VMRFun (1, funlist, env))
  | CEnd -> raise End;;
