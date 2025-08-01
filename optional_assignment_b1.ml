(*Type def *)
type value =  (*values in the language are integers and booleans *)
  | IntVal of int 
  | BoolVal of bool

type address = int
  
type env = string -> address 
type store = address -> value
 
exception EvalError of string (* for eval errors *)

      (*Expressions : variables, arithmetic operations, logical operations *)
type expr = 
  | Int of int 
  | Bool of bool 
  | Var of string
  | Add of expr * expr 
  | Sub of expr * expr 
  | Mult of expr * expr
  | Div of expr * expr 
  | Neg of expr
  | Eq of expr * expr 
  | Lt of expr * expr 
  | Leq of expr * expr
  | Gt of expr * expr  
  | Geq of expr * expr
  | And of expr * expr 
  | Or of expr * expr 
  | Not of expr 
    
type sort = (*Sort to specify types of variables and parameters *)
  |IntSort
  |BoolSort
    
type parameter = string * sort (* function parameters are name and sort pairs *)

                   (*Commands of the language *)
type command = 
  | VarDeclar of string * sort * expr (*variable declaration *)
  | Assign of string * expr (* Assignment *)
  | Seq of command * command (*Sequencing of commands *)
  | IfThenElse of expr * command * command (*If-Then-Else conditional *)
  | IfThen of expr * command (*If-Then conditional *)
  | While of expr * command (*While loop *)
  | ProcCall of string * expr list (* Procedure call *)
  | ProcDecl of string * parameter list * command * command (* Procedure declaration *)

                  (*Declarations of global variables and procedures *)
type declaration = 
  | GlobalVar of string * sort
  | Procedure of string * parameter list * parameter list * command
                 
                   (*A complete program: declarations, main procedure name, parameters and the body *)
type program = Program of declaration list * string * parameter list * command
                          
let update_env ( env : env) (x: string ) (a : address) : env =
  fun y -> if y = x then a else env y
    
let update_store (store: store) (a: address) (v: value): store =
  fun x -> if x = a then v else store x
        
let empty_env : env = fun _ -> raise( EvalError "Unbound variable ")
let empty_store : store = fun _ -> raise( EvalError "Uninitialized memory ")

                            (*Evaluationg expressions  under the current state*)
let rec eval_expr (e : expr) (env : env) (store : store) : value =
  match e with
  | Int n -> IntVal n
  | Bool b -> BoolVal b
  | Var x -> store (env x)
  | Add (e1, e2) -> (match eval_expr e1 env store , eval_expr e2 env store with
      | IntVal v1, IntVal v2 -> IntVal (v1 + v2)
      | _ -> raise (EvalError "Addition requires integers"))
  | Sub (e1, e2) -> (match eval_expr e1 env store, eval_expr e2 env store with
      | IntVal v1, IntVal v2 -> IntVal (v1 - v2)
      | _ -> raise (EvalError "Subtraction requires integers"))
  | Mult (e1, e2) -> (match eval_expr e1 env store, eval_expr e2 env store with
      | IntVal v1, IntVal v2 -> IntVal (v1 * v2)
      | _ -> raise (EvalError "Multiplication requires integers"))
  | Div (e1, e2) -> (match eval_expr e1 env store, eval_expr e2 env store with
      | IntVal v1, IntVal v2 -> if v2 <> 0 then IntVal (v1 / v2)
          else raise (EvalError "Division by zero")
      | _ -> raise (EvalError "Division requires integers"))
  | Neg e1 -> (match eval_expr e1 env store with
      | IntVal v -> IntVal (-v)
      | _ -> raise (EvalError "Negation requires integer"))
  | Eq (e1, e2) -> (match eval_expr e1 env store, eval_expr e2 env store with
      | IntVal v1, IntVal v2 -> BoolVal (v1 = v2)
      | BoolVal b1, BoolVal b2 -> BoolVal (b1 = b2)
      | _ -> raise (EvalError "Equality requires same type"))
  | Lt (e1, e2) -> (match eval_expr e1 env store, eval_expr e2 env store with
      | IntVal v1, IntVal v2 -> BoolVal (v1 < v2)
      | _ -> raise (EvalError "Less-than requires integers"))
  | Leq (e1, e2) -> (match eval_expr e1 env store, eval_expr e2 env store with
      | IntVal v1, IntVal v2 -> BoolVal (v1 <= v2)
      | _ -> raise (EvalError "Less-equal requires integers"))
  | Gt (e1, e2) -> (match eval_expr e1 env store, eval_expr e2 env store with
      | IntVal v1, IntVal v2 -> BoolVal (v1 > v2)
      | _ -> raise (EvalError "Greater-than requires integers"))
  | Geq (e1, e2) -> (match eval_expr e1 env store, eval_expr e2 env store with
      | IntVal v1, IntVal v2 -> BoolVal (v1 >= v2)
      | _ -> raise (EvalError "Greater-equal requires integers"))
  | And (e1, e2) -> (match eval_expr e1 env store, eval_expr e2 env store with
      | BoolVal b1, BoolVal b2 -> BoolVal (b1 && b2)
      | _ -> raise (EvalError "And requires booleans"))
  | Or (e1, e2) -> (match eval_expr e1 env store, eval_expr e2 env store with
      | BoolVal b1, BoolVal b2 -> BoolVal (b1 || b2)
      | _ -> raise (EvalError "Or requires booleans"))
  | Not e1 -> (match eval_expr e1 env store with
      | BoolVal b -> BoolVal (not b)
      | _ -> raise (EvalError "Not requires boolean"))


        (*A proc_def is a list of parameters and a command body *)
type proc_def  = parameter list * command
                   (*A proc_env maps the name to the procedure definition *)
type proc_env = string -> proc_def 
    (* An empty procedure environment *)
let empty_proc_env : proc_env = fun _ -> raise(EvalError "Undefined Procedure")
    
    (*Extending a  procedure environment with a new binding *)
let extend_proc_env (proc: string) (params: parameter list) (body: command) (penv: proc_env): proc_env = 
  fun name -> if name = proc then (params, body) else penv name
        
        (* Evaluating commands under a state and procedure environment *)
let rec eval_command (cmd : command) (env : env) (store : store) (penv : proc_env) (next_addr : address)  : env * store * address =
  match cmd with
  | VarDeclar (x, _, e) -> let v = eval_expr e env store in 
      let store' = update_store store next_addr v in 
      let env' = update_env env x next_addr in 
      (env', store', next_addr + 1)
      
  | Assign (x, e) -> let a = env x in
      let v = eval_expr e env store in
      let store' = update_store store a v in 
      (env, store', next_addr)
      
  | Seq (c1, c2) -> let(env1, store1, addr1) = eval_command c1 env store penv next_addr in
      eval_command c2 env1 store1 penv addr1
        
  | IfThenElse (e, c1, c2) ->
      (match eval_expr e env store with
       | BoolVal true -> eval_command c1 env store penv next_addr
       | BoolVal false -> eval_command c2 env store penv next_addr
       | _ -> raise (EvalError "Condition must be boolean"))
      
  | IfThen (e, c1) ->
      (match eval_expr e env store with
       | BoolVal true -> eval_command c1 env store penv next_addr
       | BoolVal false -> (env, store, next_addr)
       | _ -> raise (EvalError "Condition must be boolean"))
      
  | While (e, c1) ->
      let rec loop env store addr =
        match eval_expr e env store  with
        | BoolVal true -> let (env', store', addr') = eval_command c1 env store penv addr in
            loop env' store' addr'
        | BoolVal false -> (env, store, addr)
        | _ -> raise (EvalError "Condition must be boolean")
      in loop env store next_addr
        
  | ProcDecl (name, params, body, cont) -> 
      let new_penv = extend_proc_env name params body penv in
      eval_command cont env store new_penv next_addr
        
  | ProcCall (name, args) ->
      let (formals, body) = penv name in 
      let arg_vals = List.map( fun e -> eval_expr e env store) args in 
      let (env_proc, store_proc, addr_after) = 
        List.fold_left2 (fun (env_acc, store_acc, addr_acc) (pname,_) v ->
            let env_acc' = update_env env_acc pname addr_acc in 
            let store_acc' = update_store store_acc addr_acc v in 
            (env_acc', store_acc', addr_acc+1))
          (empty_env, store, next_addr) formals arg_vals
      in let (_, store_final, addr_final) = eval_command body env_proc store_proc penv addr_after in 
      (env, store_final, addr_final)
        
        (*Building a procedure environment from top-level declarations *)
let build_proc_env decls  =
  let rec aux decls penv  =
    match decls with 
    | [] -> penv
    |Procedure( name, formals,_, body) :: rest ->
        aux rest (extend_proc_env name formals body penv)
    |_ :: rest -> aux rest penv
  in aux decls empty_proc_env

    (*Running the full program given input values for parameters *)                 
let run_program (Program (decls, _, params, body)) (input_vals : value list) : value list =
  let penv = build_proc_env decls in 
  let (env, store, next_addr) = 
    List.fold_left2 (fun(env, store, addr) (x, _) v ->
        let env' = update_env env x addr in 
        let store' = update_store store addr v in 
        (env', store', addr+1))
      (empty_env, empty_store, 0)
      params input_vals
  in 
  let (env_final, store_final, _) = eval_command body env store penv next_addr in 
  List.map(fun (x, _) -> store_final(env_final x)) params
    
    
    (*Example 7.7 *)
let gcd_program = 
  Program ( 
    [ (* Global variable *)
      GlobalVar ("c", IntSort);
      
      (* Procedure div(a, b; ref q, r) *)
      Procedure( "div", [("a", IntSort); ("b", IntSort)],
                 [("q", IntSort); ("r", IntSort)],
                 
                 Seq(
                   Assign ("q", Int 0),
                   Seq (
                     Assign ("r", Var "a"),
                     Seq (
                       While (Geq (Var "r", Var "b"),
                              Seq (
                                Assign ("q", Add (Var "q", Int 1)),
                                Assign ("r", Sub (Var "r", Var "b"))
                              )
                             ),
                       Assign ("c", Add(Var "c", Int 1))
                     )
                   )
                 )
               );
      (* Procedure gcd(a, b; ref g, n) *)
      Procedure ("gcd", [("a", IntSort); ("b", IntSort)], [("g", IntSort); ("n", IntSort)],
                 Seq (
                   Assign ("c", Int 0),
                   Seq (
                     While (And (Gt (Var "a", Int 0), Gt (Var "b", Int 0)),
                            Seq (
                              VarDeclar ("c", IntSort, Int 0),
                              IfThenElse (
                                Geq(Var "a", Var "b"),
                                ProcCall("div", [Var "a"; Var "b"; Var "c"; Var "a"]),
                                ProcCall ("div", [Var "b"; Var "a"; Var "c"; Var "b"])
                              )
                            )
                           ),
                     Seq (
                       IfThenElse (
                         Gt (Var "a", Int 0),
                         Assign ("g", Var "a"),
                         Assign ("g", Var "b")
                       ),
                       Assign ("n", Var "c")
                     )
                   )
                 )
                ); 
      (*Procedure main *)
      Procedure ("main", [("a", IntSort); ("b", IntSort); ("c", IntSort); ("d", IntSort)], [],
                 ProcCall ("gcd", [
                     Mult (Var "a", Var "b");
                     Add (Var "a", Var "b");
                     Var "c";
                     Var "d"
                   ])
                )
    ],
    "main",
    [("a", IntSort); ("b", IntSort); ("c", IntSort); ("d", IntSort)],
    ProcCall ("main", [Var "a"; Var "b"; Var "c"; Var "d"])
  )
    
let () = 
  let input_vals = [IntVal 6; IntVal 4; IntVal 0; IntVal 0] in 
  let result = run_program gcd_program input_vals in 
  match result with 
  | [IntVal g; IntVal n; _; _] ->
      Printf.printf "GCD = %d, Div Calls = %d\n" g n 
  | _ -> Printf.printf "Error. \n"
                   