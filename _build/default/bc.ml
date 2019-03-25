open List ;;
open Pervasives ;;

type sExpr = 
  | Atom of string
  | List of sExpr list ;;

type expr = 
  | Num of float
  | Op1 of string * expr
  | Op2 of string * expr * expr
  | Var of string
  | Fct of string * expr list ;;

type statement = 
  | Assign    of string * expr
  | Expr      of expr
  | If        of expr * statement list * statement list
  | While     of expr * statement list
  | For       of statement * expr * statement * statement list
  | FctDef    of string * string list * statement list
  | Return    of expr
  | Break
  | Continue ;;


type block = statement list ;;

type env = 
  | VarDef of string * float
  | FuncDef of string * string list * statement list ;;

type scope = env list
type envQueue = scope list ;;

(* Exceptions for breaking from loops *)
exception ReturnException of expr * envQueue ;;
exception BreakException of envQueue ;;
exception ContinueException of envQueue ;;

(* Avoid Not_Found error *)
let safe_list_find p l =
  try Some (find p l)
  with Not_found -> None ;;

(* Adds a VarDef or FuncDef to the beginning of the scope passed in *)
let addToScope (env : env) (scope : scope) : scope =
  let listPartition = partition (fun env ->
    match env with
    | VarDef (_, _) -> true
    | FuncDef (_, _, _) -> false) scope in
      match listPartition with
      | (varDefs, funcDefs) ->
        match env with
        | VarDef (_, _) -> (
          let varNames = map (fun varDef ->
            match varDef with
            | VarDef (v, _) -> v
            | FuncDef (_, _, _) -> "") varDefs in
              match env with
              | VarDef (v, _) as newVarDef -> (
                match mem v varNames with
                | true -> map (fun env ->
                  match env with
                  | VarDef (vName, _) as currVarDef -> if v = vName then newVarDef else currVarDef
                  | FuncDef (_, _, _) -> env) scope
                | false -> newVarDef :: scope)
              | FuncDef (_, _, _) -> scope)
        | FuncDef (_, _, _) -> (
          let funcNames = map (fun funcDef ->
            match funcDef with
            | FuncDef (f, _, _) -> f
            | VarDef (_, _) -> "") funcDefs in
              match env with
              | FuncDef(f, _, _) as newFuncDef -> (
                match mem f funcNames with
                | true -> map (fun env ->
                  match env with
                  | FuncDef (fName, _, _) as currFuncDef -> if f = fName then newFuncDef else currFuncDef
                  | VarDef (_, _) -> env) scope
                | false -> newFuncDef :: scope)
              | VarDef (_, _) -> scope) ;;

(* returns the parameters and environment necessary to run a function *)
let rec funcEval (f : string) (q : envQueue) : string * string list * block =
  match q with
  | [] -> "", [], []
  | hd :: tl -> 
    match safe_list_find (fun env ->
      match env with
      | FuncDef (fName, _, _) -> if f = fName then true else false
      | VarDef (_, _) -> false) hd with
    | Some FuncDef (f, params, code) -> f, params, code
    | _ -> funcEval f tl ;;

let rec varEval (v : string) (q : envQueue) : float =
  match q with
  | [] -> 0.0
  | hd :: tl -> (
    match safe_list_find (fun env ->
      match env with
      | VarDef (vName, _) -> vName = v
      | _ -> false) hd with
    | Some VarDef(_, value) -> value
    | _ -> varEval v tl) ;;

(* Binary operation evaluation (less clutter in evalExpr) *)
let evalBinOp (op : string) (val1 : float) (val2 : float) : float =
  match op with
  | "^" -> val1 ** val2
  | "*" -> val1 *. val2
  | "/" -> val1 /. val2
  | "+" -> val1 +. val2
  | "-" -> val1 -. val2
  | ">" -> if val1 > val2 then 1. else 0.
  | ">=" -> if val1 >= val2 then 1. else 0.
  | "<" -> if val1 < val2 then 1. else 0.
  | "<=" -> if val1 <= val2 then 1. else 0.
  | "==" -> if val1 = val2 then 1. else 0.
  | "!=" -> if val1 <> val2 then 1. else 0.
  | _ -> 0. ;;

(* Evaluates a mathematical/logical expression, as well as function calls *)
let rec evalExpr (e : expr) (q : envQueue) : float =
  match e with
  | Num number -> number
  | Op1 (op, expr) -> (
    let value = evalExpr expr q in
      match op with
      | "!" -> if value = 0. then 0. else 1.;
      | _ -> 0.0)
  | Op2 (op, expr1, expr2) ->
    let val1 = evalExpr expr1 q in
      let val2 = evalExpr expr2 q in
        evalBinOp op val1 val2
  | Var varName -> varEval varName q
  | Fct (f, callParams) -> (
    let (_, funcParams, code) = funcEval f q in
      let mapParamToFunc = (match length callParams = length funcParams with
      | false -> []
      | true -> fold_left evalStatement (append [] q) (map2 (fun callExpr param -> Assign(param, callExpr)) callParams funcParams)) in
    let rec funcCall (funcQ : envQueue) (code : block) : float =
      match code with
      | [] -> 0.0
      | hd :: tl -> funcCall (evalStatement funcQ hd) tl in
    try funcCall mapParamToFunc code with ReturnException (expr, exceptQ) -> evalExpr expr exceptQ)

(* Evaluates a single statement *)
and evalStatement (q : envQueue) (stm : statement) : envQueue =
  match stm with
  | Assign (v, e) -> (
    let value = evalExpr e q in
      match q with
      | [] -> addToScope (VarDef (v, value)) [] :: [[]]
      | hd :: tl -> addToScope (VarDef (v, value)) hd :: tl)
  | Expr exp -> (
    match exp with
    | Op1 (op, Var v) -> (
      match op with
      | "++" -> evalStatement q (Assign (v, Num((evalExpr (Var v) q) +. 1.)))
      | "--" -> evalStatement q (Assign (v, Num((evalExpr (Var v) q) -. 1.)))
      | _ -> Printf.printf "%F\n" (evalExpr exp q); q)
    | expr -> Printf.printf "%F\n" (evalExpr expr q); q)
  | If (e, codeT, codeF) -> (
    let cond = evalExpr e q in
      if cond > 0. then fold_left evalStatement q codeT
      else fold_left evalStatement q codeF)
  | While (cond, code) -> (
    let condToEval : envQueue -> float = evalExpr cond in
      let rec whileLoop (whileQ : envQueue) =
        if condToEval whileQ > 0. then
          whileLoop (try fold_left evalStatement whileQ code with ContinueException exceptQ -> exceptQ)
        else whileQ in
      try whileLoop q with BreakException exceptQ -> exceptQ)
  | For (vDef, cond, vRedef, code) -> (
    let firstItScope = evalStatement q vDef in
      let condToEval : envQueue -> float = evalExpr cond in
        let rec forLoop (forQ : envQueue) : envQueue =
          if condToEval forQ > 0. then 
            let nextQ : envQueue =
              try (fold_left evalStatement forQ code) with ContinueException exceptQ -> exceptQ in
                forLoop (evalStatement nextQ vRedef)
          else forQ in
        try forLoop firstItScope with BreakException exceptQ -> exceptQ)
  | FctDef (f, params, code) -> (
    match q with
    | [] -> addToScope (FuncDef (f, params, code)) []::[[]]
    | hd :: tl -> addToScope (FuncDef (f, params, code)) hd :: tl)
  | Return expr -> raise (ReturnException (expr, q))
  | Continue -> raise (ContinueException q)
  | Break -> raise (BreakException q)

(* Entry point *)
let evalCode (code : block) (q : envQueue) : unit = 
    let _ = fold_left evalStatement q code in
      print_endline "" ;;


 (* v = 1; 
    v // display v *)
let p1 : block = [
  Assign("v", Num(1.0));
  Expr(Var("v"));
] ;;

(*  v = 1.0;
    if (v > 10.0) then v = v + 1.0
    else for(i = 2.0; i < 10.0; i++) v = v * i
    v   // display v *)
let p2 : block = [
  Assign("v", Num(1.0));
  If(
    Op2(">", Var("v"), Num(10.0)), 
    [Assign("v", Op2("+", Var("v"), Num(1.0)))], 
    [For(
      Assign("i", Num(2.0)),
      Op2("<", Var("i"), Num(10.0)),
      Expr(Op1("++", Var("i"))),
      [
        Assign("v", Op2("*", Var("v"), Var("i")))
      ]
    )]
  );
  Expr(Var("v"))
] ;;


(*  Fibbonaci sequence
    define f(x) {
      if (x<1.0) then return (1.0)
      else return (f(x-1)+f(x-2))
    }
    f(3)
    f(5) *)
let p3 : block = [
  FctDef("f", ["x"], [
    If(
      Op2("<", Var("x"), Num(2.0)),
      [Return(Num(1.0))],
      [Return(Op2("+",
        Fct("f", [Op2("-", Var("x"), Num(1.0))]),
        Fct("f", [Op2("-", Var("x"), Num(2.0))])
      ))]
    )
  ]);
  Expr(Fct("f", [Num(3.0)]));
  Expr(Fct("f", [Num(5.0)]));
] ;;

(*  define square(x) {
    return (x * x)
  } 
  square(9)
  square(12) *)
let p4 : block = [
  FctDef("square", ["x"], [ 
    Return(Op2("*", Var("x"), Var("x")))
  ]);
  Expr(Fct("square", [Num(9.)]));
  Expr(Fct("square", [Num(12.)]))
] ;;

(*  x = 10
    while (x > 0) {
      x = x - 1
      if (x == 5) {
        x
      }
      else {
        continue
      }
    } *)
let p5 : block = [
  Assign("x", Num(10.0));
  While(
    (Op2(">", Var("x"), Num(0.0))), [
    Assign("x", Op2("-", Var("x"), Num(1.0)));
    If(
      Op2("==", Var("x"), Num(5.0)), 
      [Expr(Var("x"))],
      [Continue]);
    ]
  )
] ;;

let p6 : block = [
  For (
    Assign("i", Num(0.)),
    Op2("<", Var("i"), Num(20.)),
    Expr(Op1("++", Var("i"))), [
      If (
        Op2(">", Var("i"), Op2("^", Num(Float.pi), Num(2.))),
        [Expr(Var("i")); Break;],
        [Continue];
      )
    ]
  )
] ;; 


(* Test for expression *)
let%expect_test "evalNum" = evalExpr (Num 10.0) []
  |> Printf.printf "%F";
  [%expect {| 10. |}] ;;

let%expect_test "evalVar" = evalExpr (Var "v") [[VarDef("v", 20.0)]]
  |> Printf.printf "%F";
  [%expect {| 20. |}] ;;

let%expect_test "p1" =
  evalCode p1 []; 
  [%expect {| 1. |}] ;;

let%expect_test "p2" =
  evalCode p2 []; 
  [%expect {| 362880. |}] ;;

let%expect_test "p3" =
  evalCode p3 []; 
  [%expect {| 
    3. 
    8.      
|}] ;;

let%expect_test "p4" =
  evalCode p4 [];
  [%expect {|
    81.
    144.
  |}] ;;

let%expect_test "p5" =
  evalCode p5 [];
  [%expect {| 5. |}] ;;

let%expect_test "p6" =
  evalCode p6 [];
  [%expect {| 10. |}] ;;
