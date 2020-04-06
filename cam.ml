open Syntax
type cam_instr =
  | CLdi of int
  | CLdb of bool
  | CAccess of int
  | CClosure of cam_code
  | CApply
  | CReturn
  | CLet
  | CEndLet
  | CTest of cam_code * cam_code
  | CAdd
  | CEq
and cam_code = cam_instr list

type cam_value =
  | CInt of int
  | CBool of bool
  | CClos of cam_code * cam_env
and cam_stack = cam_value list
and cam_env = cam_value list

exception Eval_error

let rec eval: cam_code -> cam_env -> cam_stack -> cam_value =
  fun code env stack ->
  match code with
  | [] -> if List.length stack = 1 then
            List.hd stack
          else
            raise Eval_error
  | CLdi(n) :: c -> eval c env (CInt(n) :: stack)
  | CLdb(b) :: c -> eval c env (CBool(b) :: stack)
  | CAccess(i) :: c ->
     let x = try List.nth env i with Not_found -> raise Eval_error in
     eval c env (x :: stack)
  | CClosure(c') :: c -> eval c env (CClos(c', env) :: stack)
  | CApply :: c ->
     begin
       match stack with
       | CClos(c', env') :: v :: s ->
          eval c' (v :: CClos(c', env') :: env') (CClos(c, env) :: s)
       | _ -> raise Eval_error
     end
  | CReturn :: c ->
     begin
       match stack with
       | v :: CClos(c', env') :: s ->
          eval c' env' (v :: s)
       | _ -> raise Eval_error
     end
  | CLet :: c ->
     begin
       match stack with
       | v :: s ->
          eval c (v :: env) s
       | _ -> raise Eval_error
     end
  | CEndLet :: c ->
     begin
       match env with
       | v :: env -> eval c env stack
       | _ -> raise Eval_error
     end
  | CTest(c1, c2) :: c ->
     begin
       match stack with
       | CBool(true) :: s -> eval (c1 @ c) env s
       | CBool(false) :: s -> eval (c2 @ c) env s
       | _ -> raise Eval_error
     end
  | CAdd :: c ->
     begin
       match stack with
       | CInt(n1) :: CInt(n2) :: s -> eval c env (CInt(n1 + n2) :: s)
       | _ -> raise Eval_error
     end
  | CEq :: c ->
     begin
       match stack with
       | n1 :: n2 :: s -> eval c env (CBool(n1 = n2) :: s)
       | _ -> raise Eval_error
     end

let rec position : name  -> env -> int = fun x env ->
  match env with
  | [] -> failwith "no matching variable in environment"
  | (y, _) :: env' -> if x = y then 0 else (position x env') + 1


let rec compile : env -> expr -> cam_code = fun env exp ->
  match exp with
  | EVar name -> [CAccess(position name env)]
  | EValue v -> begin match v with
                | VInt n -> [CLdi(n)]
                | VBool b -> [CLdb(b)]
                | _ -> failwith "not implemented!"
                end
  | EBin (op, e1, e2) ->
     let p1 = compile env e1 in
     let p2 = compile env e2 in
     begin match op with
     | OpAdd -> p1 @ p2 @ [CAdd]
     | OpEq -> p1 @ p2 @ [CEq]
     | _ -> failwith "not implemented!"
     end
  | ETuple (_) | ENil | ECons (_, _)
    -> failwith "not implemented!"
  | ELet (pat, e1, e2) ->
