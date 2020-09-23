(* semantic.ml *)

module A = Absyn
module S = Symbol
module T = Type

type entry = [%import: Env.entry]
type env = [%import: Env.env]

(* Obtain the location of an ast *)

let loc = Location.loc

(* Reporting errors *)

let undefined loc category id =
  Error.error loc "undefined %s %s" category (S.name id)

let misdefined loc category id =
  Error.error loc "%s is not a %s" (S.name id) category

let type_mismatch loc expected found =
  Error.error loc "type mismatch: expected %s, found %s" (T.show_ty expected) (T.show_ty found)

(* Searhing in symbol tables *)

let look env category id pos =
  match S.look id env with
  | Some x -> x
  | None -> undefined pos category id

let tylook tenv id pos =
  look tenv "type" id pos

let varlook venv id pos =
  match look venv "variable" id pos with
  | VarEntry t -> t
  | FunEntry _ -> misdefined pos "variable" id

let funlook venv id pos =
  match look venv "function" id pos with
  | VarEntry _ -> misdefined pos "function" id
  | FunEntry (params, result) -> (params, result)

(* Type compatibility *)

let compatible ty1 ty2 pos =
  if not (T.coerceable ty1 ty2) then
    type_mismatch pos ty2 ty1

(* Set the value in a reference of optional *)

let set reference value =
  reference := Some value;
  value


(* Adds all the parameters variables to the function's body environment *)

let rec putFunParamsInEnv lparam env pos =
  match lparam with
  | (n, t)::tail -> let venv' = S.enter n (VarEntry (tylook env.tenv t pos)) env.venv in
                    let env' = {env with venv = venv'} in
                    putFunParamsInEnv tail env' pos
  | []           -> env


(* Returns the variables' types in the function parameters list *)

let rec getTypesFormals lparams acc env pos =
  match lparams with
  | (_, t)::tail -> getTypesFormals tail (List.append acc [tylook env.tenv t pos]) env pos
  | []           -> acc

(* Returns a new environment with the current function *)

let verifyParamsTypes funcname lparams type_ret (env, pos) =
  let formals = getTypesFormals lparams [] env pos in
    let venv' = S.enter funcname (FunEntry(formals, type_ret)) env.venv in
    {env with venv = venv'}

(* Checks if a variable name was declared more than once in the function parameters' list *)

let rec verifyFormalsNames ln pos =
  match ln with
  | h::t -> if List.mem h t then Error.error pos "Variable '%s' was declared more than once in the function definition" h
                          else verifyFormalsNames t pos
  | _    -> ()
  
(* Returns the variables' names in the function parameters list *)

let rec getNamesFormals lparams acc =
  match lparams with
  | (n, _)::tail -> getNamesFormals tail (List.append acc [S.name n])
  | []           -> acc


(* Checking expressions *)

let rec check_exp env (pos, (exp, tref)) =
  match exp with
  | A.BoolExp _ -> set tref T.BOOL
  | A.IntExp  _ -> set tref T.INT
  | A.RealExp _ -> set tref T.REAL
  | A.StringExp _ -> set tref T.STRING
  | A.LetExp (decs, body) -> check_exp_let env pos tref decs body

  | A.CallExp (name, lexp) ->  
    let (params, result) = funlook env.venv name pos in  
      ignore(match_fun_param_types lexp params env pos);
      set tref result
  
  | A.BinaryExp (l, op, r) -> 
      let tl = check_exp env l in
      let tr = check_exp env r in
      begin match op with
        | A.And 
        | A.Or ->
          begin match tl, tr with
            | T.BOOL, T.BOOL -> set tref T.BOOL
            | _ -> (
              match tl with 
              | T.BOOL -> type_mismatch pos T.BOOL tr 
              | _ -> type_mismatch pos T.BOOL tl
            )
          end
        | A.Plus 
        | A.Minus 
        | A.Times 
        | A.Div 
        | A.Mod 
        | A.Power ->
          begin match tl, tr with
            | T.INT,  T.REAL 
            | T.REAL, T.INT 
            | T.REAL, T.REAL -> set tref T.REAL
            | T.INT,  T.INT  -> set tref T.INT
            | _              -> type_mismatch pos tl tr
          end     
        | A.Equal 
        | A.NotEqual 
        | A.LowerThan 
        | A.GreaterThan 
        | A.GreaterEqual 
        | A.LowerEqual -> compatible tr tl pos; set tref T.BOOL
      end

  | A.NegativeExp (exp) -> let result = check_exp env exp in 
      begin match result with
        | T.INT 
        | T.REAL -> set tref result
        | _ -> type_mismatch pos T.REAL result
      end

  | A.ExpSeq expList ->
    let rec check_seq = function
      | []        -> T.VOID
      | [exp]     -> check_exp env exp
      | exp::rest -> ignore (check_exp env exp); check_seq rest
    in
      check_seq expList

  | A.BreakExp -> 
    if(env.inloop) then
      T.VOID
    else 
      Error.error pos "Break outside of loop"

  | A.WhileExp (comp, sc) -> let env_inloop = {env with inloop = true} in
      ignore(check_exp env_inloop comp); 
      ignore(check_exp env_inloop sc); 
      set tref T.VOID

  | A.IfExp (condition, exp_then, exp_else) -> 
  let cond = check_exp env condition in
      begin match cond with
      | T.BOOL -> (let tthen = check_exp env exp_then in
                    begin match exp_else with
                     | Some ee -> (let telse = check_exp env ee in
                                   match telse with
                                   | iftype when iftype = tthen -> set tref telse
                                   | _                          -> type_mismatch pos tthen telse
                                 )
                     | None    -> set tref T.VOID
                     end)
      | _       ->  type_mismatch pos T.BOOL cond
     end

  | A.VarExp v -> check_var env v tref
  | _ -> Error.fatal "unimplemented"


and match_fun_param_types lexpr lparam env pos =
  match lexpr, lparam with
  | (eh::et, ph::pt) -> (let etype = check_exp env eh in
                         compatible etype ph pos;
                         match_fun_param_types et pt env pos
                        )                       
  | [], []           -> ()
  | _                -> Error.error pos "The number of parameters of the function is wrong."

and check_var env (pos, v) tref =
  match v with
  | A.SimpleVar id -> (let t = varlook env.venv id pos in
                      set tref t)
  | _ -> Error.fatal "unimplemented expression"


and check_exp_let env pos tref decs body =
  let env' = List.fold_left check_dec env decs in
  let tbody = check_exp env' body in
  set tref tbody

(* Checking declarations *)

and check_dec_var env pos ((name, type_opt, init), tref) =
  let tinit = check_exp env init in
  let tvar =
    match type_opt with
    | Some tname ->
       let t = tylook env.tenv tname pos in
       compatible tinit t (loc init);
       t
    | None -> tinit
  in
  ignore (set tref tvar);
  let venv' = S.enter name (VarEntry tvar) env.venv in
  {env with venv = venv'}


and check_dec_fun env pos ((name, params_list, type_ret, body), tref) =
  let rt     = tylook env.tenv type_ret pos in                               
  let env'   = verifyParamsTypes name params_list rt (env, pos) in            
  let lnames = getNamesFormals params_list [] in
  ignore(verifyFormalsNames lnames pos);                                      

  let envbody = putFunParamsInEnv params_list env' pos in                     
 
  let tbody = check_exp envbody body in                                       
  compatible tbody rt pos; 
  ignore(set tref rt);
  env'

  
and check_dec env (pos, dec) =
  match dec with
  | A.VarDec x -> check_dec_var env pos x
  | A.FunDec x -> check_dec_fun env pos x
  | _ -> Error.fatal "unimplemented declaration"

let semantic program =
  check_exp Env.initial program