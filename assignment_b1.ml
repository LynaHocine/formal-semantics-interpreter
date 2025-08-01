(*Type def *)
type value =  (*values in the language are integers and booleans *)
  | IntVal of int 
  | BoolVal of bool

type state = string -> value (*state is mapping variable name to value *)
 
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
  | ProcDecl of string * parameter list *parameter list * command * command (* Procedure declaration *)

                  (*Declarations of global variables and procedures *)
type declaration = 
  | GlobalVar of string * sort
  | Procedure of string * parameter list * parameter list * command
                 
                   (*A complete program: declarations, main procedure name, parameters and the body *)
type program = Program of declaration list * string * parameter list * command

                            (*Evaluationg expressions  under the current state*)
let rec eval_expr (e : expr) (s : state) : value =
  match e with
  | Int n -> IntVal n
  | Bool b -> BoolVal b
  | Var x -> s x
  | Add (e1, e2) -> (match eval_expr e1 s, eval_expr e2 s with
      | IntVal v1, IntVal v2 -> IntVal (v1 + v2)
      | _ -> raise (EvalError "Addition requires integers"))
  | Sub (e1, e2) -> (match eval_expr e1 s, eval_expr e2 s with
      | IntVal v1, IntVal v2 -> IntVal (v1 - v2)
      | _ -> raise (EvalError "Subtraction requires integers"))
  | Mult (e1, e2) -> (match eval_expr e1 s, eval_expr e2 s with
      | IntVal v1, IntVal v2 -> IntVal (v1 * v2)
      | _ -> raise (EvalError "Multiplication requires integers"))
  | Div (e1, e2) -> (match eval_expr e1 s, eval_expr e2 s with
      | IntVal v1, IntVal v2 -> if v2 <> 0 then IntVal (v1 / v2)
          else raise (EvalError "Division by zero")
      | _ -> raise (EvalError "Division requires integers"))
  | Neg e1 -> (match eval_expr e1 s with
      | IntVal v -> IntVal (-v)
      | _ -> raise (EvalError "Negation requires integer"))
  | Eq (e1, e2) -> (match eval_expr e1 s, eval_expr e2 s with
      | IntVal v1, IntVal v2 -> BoolVal (v1 = v2)
      | BoolVal b1, BoolVal b2 -> BoolVal (b1 = b2)
      | _ -> raise (EvalError "Equality requires same type"))
  | Lt (e1, e2) -> (match eval_expr e1 s, eval_expr e2 s with
      | IntVal v1, IntVal v2 -> BoolVal (v1 < v2)
      | _ -> raise (EvalError "Less-than requires integers"))
  | Leq (e1, e2) -> (match eval_expr e1 s, eval_expr e2 s with
      | IntVal v1, IntVal v2 -> BoolVal (v1 <= v2)
      | _ -> raise (EvalError "Less-equal requires integers"))
  | Gt (e1, e2) -> (match eval_expr e1 s, eval_expr e2 s with
      | IntVal v1, IntVal v2 -> BoolVal (v1 > v2)
      | _ -> raise (EvalError "Greater-than requires integers"))
  | Geq (e1, e2) -> (match eval_expr e1 s, eval_expr e2 s with
      | IntVal v1, IntVal v2 -> BoolVal (v1 >= v2)
      | _ -> raise (EvalError "Greater-equal requires integers"))
  | And (e1, e2) -> (match eval_expr e1 s, eval_expr e2 s with
      | BoolVal b1, BoolVal b2 -> BoolVal (b1 && b2)
      | _ -> raise (EvalError "And requires booleans"))
  | Or (e1, e2) -> (match eval_expr e1 s, eval_expr e2 s with
      | BoolVal b1, BoolVal b2 -> BoolVal (b1 || b2)
      | _ -> raise (EvalError "Or requires booleans"))
  | Not e1 -> (match eval_expr e1 s with
      | BoolVal b -> BoolVal (not b)
      | _ -> raise (EvalError "Not requires boolean"))

                (* Extends a state with parameter bindings *)   
let rec extend_state (params : parameter list) (vals : value list) (outer : state) : state =
  match params, vals with
  | [], [] -> outer
  | (name, _) :: ps, v :: vs ->
      let rest = extend_state ps vs outer in
      fun x -> if x = name then v else rest x
  | _ -> raise (EvalError "Mismatched parameter and value count")

           (*Updates a state with new variable assignment *)
let update_state (s : state) (x : string) (v : value) : state =
  fun y -> if y = x then v else s y
        (*A proc_def is a list of parameters and a command body *)
type proc_def  = parameter list * parameter list * command
                   (*A proc_env maps the name to the procedure definition *)
type proc_env = string -> proc_def 
    (* An empty procedure environment *)
let empty_proc_env : proc_env = fun _ -> raise(EvalError "Undefined Procedure")
    
    (*Extending a  procedure environment with a new binding *)
let extend_proc_env (proc: string) (inputs: parameter list) (outputs: parameter list) (body: command) (penv: proc_env): proc_env = 
  fun name -> if name = proc then (inputs,outputs, body) else penv name
        
        (* Evaluating commands under a state and procedure environment *)
let rec eval_command (cmd : command) (s : state) (penv : proc_env)  : state =
  match cmd with
  | VarDeclar (x, _, e) -> update_state s x (eval_expr e s)
  | Assign (x, e) -> update_state s x (eval_expr e s)
  | Seq (c1, c2) -> eval_command c2 (eval_command c1 s penv) penv
  | IfThenElse (e, c1, c2) ->
      (match eval_expr e s with
       | BoolVal true -> eval_command c1 s penv
       | BoolVal false -> eval_command c2 s penv
       | _ -> raise (EvalError "Condition must be boolean"))
  | IfThen (e, c1) ->
      (match eval_expr e s with
       | BoolVal true -> eval_command c1 s penv
       | BoolVal false -> s
       | _ -> raise (EvalError "Condition must be boolean"))
  | While (e, c1) ->
      let rec loop st =
        match eval_expr e st with
        | BoolVal true -> loop (eval_command c1 st penv)
        | BoolVal false -> st
        | _ -> raise (EvalError "Condition must be boolean")
      in loop s
        
  | ProcDecl (name, inputs, outputs, body, cont) -> 
      let new_env = extend_proc_env name inputs outputs body penv in 
      eval_command cont s new_env
        
  | ProcCall (name, args) ->
      let (inputs, outputs, body) = penv name in 
      if List.length args <> List.length inputs + List.length outputs then 
        raise (EvalError "Mismatched parameter and value count ")
      else
        let input_args, output_args = 
          let rec split n l = 
            if n = 0 then ([], l)
            else match l with
              |x::xs ->
                  let (first, rest) =split (n -1) xs in
                  (x::first, rest)
              |[] -> raise (EvalError "not enough arguments ")
          in 
          split (List.length inputs) args
        in
        let input_vals = List.map (fun e -> eval_expr e s) input_args in
        let proc_state = extend_state inputs input_vals s in
        let proc_state_with_outputs = extend_state outputs (List.map (fun _ ->IntVal 0) outputs) proc_state in
        let final_state = eval_command body proc_state_with_outputs penv in 
        let updated_state = 
          List.fold_left2 (fun st out_param out_arg_expr ->
              let out_arg_name = match out_arg_expr with
                | Var name -> name
                | _ -> raise (EvalError "Output arguments must be variables")
              in
              update_state st out_arg_name (final_state (fst out_param))
            ) s outputs output_args
        in 
        updated_state
        
        (*Building a procedure environment from top-level declarations *)
let build_proc_env (decls : declaration list): proc_env =
  let rec helper ds penv =
    match ds with 
    | [] -> penv
    |Procedure( name,inputs, outputs, body) :: rest ->
        helper rest (extend_proc_env name inputs outputs body penv) 
    |_ :: rest -> helper rest penv
  in helper decls empty_proc_env

    (*Running the full program given input values for parameters *)                 
let run_program (Program (decls, main_name, params, body)) (input_vals : value list) : value list =
  let default = fun _ -> IntVal 0 in
  let globals = List.fold_left (fun acc d -> match d with 
      |GlobalVar (name, _) -> (name, IntSort)::acc
      |_ -> acc) [] decls
  in 
  let state_with_globals = extend_state globals (List.init (List.length globals) (fun _ -> IntVal 0)) default in
  let full_state = extend_state params input_vals state_with_globals in
  let proc_env = build_proc_env decls in 
  let final_state = eval_command (ProcCall (main_name, List.map (fun (name,_) -> Var name) params))
      full_state proc_env in List.map(fun(name,_) -> final_state name) params
    
    (*Example 7.7 *)
let program_example = Program ([
    GlobalVar("c",IntSort);
    Procedure("div", [("a",IntSort);("b",IntSort)], [("q",IntSort);("r",IntSort)],
              Seq(Assign("q",Int 0),
                  Seq(Assign("r",Var "a"),
                      While(Geq(Var "r",Var "b"),
                            Seq(Assign("q",Add(Var "q",Int 1)), Assign("r",Sub(Var "r",Var "b")))))));
    Procedure("gcd", [("a_in",IntSort);("b_in",IntSort)], [("g",IntSort);("n",IntSort)],
              Seq(VarDeclar("a",IntSort,Var "a_in"),
                  Seq(VarDeclar("b",IntSort,Var "b_in"),
                      Seq(VarDeclar("q",IntSort,Int 0),
                          Seq(VarDeclar("r",IntSort,Int 0),
                              Seq(Assign("c",Int 0),
                                  Seq(While(And(Gt(Var "a",Int 0),Gt(Var "b",Int 0)),
                                            IfThenElse(Geq(Var "a",Var "b"),
                                                       Seq(ProcCall("div",[Var "a";Var "b";Var "q";Var "r"]),
                                                           Seq(Assign("a",Var "r"), Assign("c",Add(Var "c",Var "q")))),
                                                       Seq(ProcCall("div",[Var "b";Var "a";Var "q";Var "r"]),
                                                           Seq(Assign("b",Var "r"), Assign("c",Add(Var "c",Var "q")))))),
                                      Seq(IfThenElse(Gt(Var "a",Int 0), Assign("g",Var "a"), Assign("g",Var "b")),
                                          Assign("n",Var "c")))))))));
    Procedure("main", [("a",IntSort);("b",IntSort)], [("c",IntSort);("d",IntSort)],
              ProcCall("gcd", [Var "a"; Var "b"; Var "c"; Var "d"]))
  ], "main", [("a",IntSort);("b",IntSort);("c",IntSort);("d",IntSort)],
    Seq(Assign("dummy",Int 0), Assign("dummy",Int 0)))

(* Example run *)
let result = run_program program_example [IntVal 30; IntVal 18; IntVal 0; IntVal 0];;
match result with [IntVal a; IntVal b; IntVal c; IntVal d] -> Printf.printf "a=%d, b=%d, gcd=%d, sum_quotients=%d\n" a b c d | _ -> Printf.printf "Unexpected output\n";;
