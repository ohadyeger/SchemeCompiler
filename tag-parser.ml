(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Ohad & Gad, 2018
 *)

#use "reader.ml";;
open Reader;;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)
(*toolbox*)

let disj nt1 nt2 =
  fun s ->
  try (nt1 s)
  with X_syntax_error -> (nt2 s);;

let nt_none _ = raise X_syntax_error;;

let disj_list nts = List.fold_right disj nts nt_none;;

let isSexpr =
  function
  | Bool a -> true
  | Nil -> true
  | Number a -> true
  | Char a -> true
  | String a -> true
  | Symbol a -> true
  | Pair (a, b) -> true
  | Vector a -> true;;

let isIf x =
  match x with
  |Pair (Symbol "if", Pair (a, Pair (b, Pair (c, Nil)))) -> (isSexpr a) && (isSexpr b) && (isSexpr c)
  |Pair (Symbol "if", Pair (a, Pair (b, Nil))) -> (isSexpr a) && (isSexpr b)
  | _ -> false;;

let isConsant s =
  match s with
  | Number x -> true
  | Bool x -> true
  | Char x -> true
  | String x-> true
  | _ -> false;;

let makeConst quoted s =
  if (isConsant s || quoted) then Const(Sexpr(s))
   else raise X_syntax_error;;

let rec isSexprList s =
  match s with
  | Nil -> true
  | Pair (a, b) -> (isSexpr a) && (isSexprList b)
  | _ -> isSexpr s;;

let rec isProperList s =
  match s with
  | Nil -> true
  | Pair (a, b) -> (isProperList b)
  | _ -> false;;

let rec isImproperList s =
  match s with
  | Nil ->false
  | Pair (a, b) -> (isImproperList b)
  | _ -> true;;

let rec stringPairToList p =
  match p with
  |Nil -> []
  |Pair (Symbol a, b) -> a :: (stringPairToList b)
  | Symbol a -> [a]
  | _ -> raise X_syntax_error;;

let rec allButLastElement l =
  match l with
  |Pair (Symbol a, b) -> a :: (allButLastElement b)
  | _ -> [];;

let rec getLastElement l =
  match l with
  |Pair (Symbol a, b) -> getLastElement b
  | Symbol s -> s
  | _ ->raise X_syntax_error;;

(*toolbox end*)

let _Constant_ s =
   match s with
  | Pair(Symbol ("quote") ,Pair (a, Nil))  ->makeConst true a
  | _ -> makeConst false s;;

let _Var_ s =
   match s with
  | Symbol x -> 
      let pred y = x = y in
      if (List.find_opt pred reserved_word_list) = None
        then (Var x)
        else raise X_syntax_error
  | _->raise X_syntax_error;;

let rec makeVarList l =
  match l with
  | Nil -> []
  | Pair (a, b)-> (_Var_ a) :: makeVarList b
  | _ -> raise X_syntax_error;;

let _VarComp_ e1 e2 =
  match e1, e2 with
  | Var(v1), Var(v2) -> String.compare v1 v2
  | _ -> raise X_syntax_error;;

let rec _tag_ s = 

  (disj_list [_Constant_; _If_; _Var_; _LambdaSimple_; _Seq_;
  _Set_; _Def_; _Or_; _Applic_; _LambdaOpt_;]) (pipeline s)

  and makeList l =
  if not(isSexprList l) then (raise X_syntax_error) else
  match l with
  |Nil -> []
  |Pair (a, b) -> (_tag_ a) :: (makeList b)
  | _ -> [ _tag_ l]
  
  and _If_ s =
  if (isIf s) then 
   match s with
        |Pair (Symbol "if", Pair (a, Pair (b, Pair (c, Nil))))->
        (If (_tag_ a, _tag_ b, _tag_ c))
        | Pair (Symbol "if", Pair (a, Pair (b, Nil))) -> (If (_tag_ a, _tag_ b, Const(Void)))
        | _-> raise X_syntax_error 
        
    else raise X_syntax_error 

  and _Seq_ s =
     match s with
     | Pair (Symbol "begin", Nil)-> Const(Void)
     | Pair (Symbol "begin", Pair (a, Nil)) -> _tag_ a
     | Pair (Symbol "begin", a) -> if (isSexprList a) then (Seq (makeList a))
        else raise X_syntax_error 
     | _ -> raise X_syntax_error 

  and _Set_ s =
     match s with
     | Pair (Symbol "set!", Pair (a, Pair(b, Nil))) -> if (isSexpr a && isSexpr b) 
        then (Set (_Var_ a,_tag_ b)) else (raise X_syntax_error )
     | _ -> raise X_syntax_error 
     
  and _Def_ s =
      match s with
     | Pair (Symbol "define", Pair (a, Pair(b, Nil))) -> Def ( _Var_ a, _tag_ b)
     | _ -> raise X_syntax_error 

  and _Or_ s =
    match s with
     | Pair (Symbol "or", Nil) ->_tag_ (Bool(false))
     | Pair (Symbol "or", Pair(a, Nil)) -> _tag_ a
     | Pair (Symbol "or", a) -> Or (makeList a)
     | _ -> raise X_syntax_error

  and _Applic_ s =
    match s with
    | Pair (a, b) -> Applic (_tag_ a, makeList b)
    | _ -> raise X_syntax_error

  and _LambdaOpt_ s =
    match s with
    | Pair (Symbol "lambda", Pair(a, b)) ->
        if not (isImproperList a) then raise X_syntax_error else

        let aList = stringPairToList a in
        let param_list = allButLastElement a in
        let noDupL = List.sort_uniq String.compare aList in
        let noDups = List.length noDupL = List.length aList in

        let body = 
        match b with 
        | Pair (c, Nil) -> _tag_ c 
        | Pair(c, d) -> _Seq_ (Pair(Symbol "begin", b))
        | _-> raise X_syntax_error
        in

        let vs = getLastElement a in
        if noDups then LambdaOpt(param_list, vs, body)
        else raise X_syntax_error

    | _ -> raise X_syntax_error

  and _LambdaSimple_ s =
    match s with
    | Pair (Symbol "lambda", Pair(a, b)) ->

        if not (isProperList a) then raise X_syntax_error else
        
        let aList = stringPairToList a in
        let noDupL = List.sort_uniq String.compare aList in
        let noDups = List.length noDupL = List.length aList in
        
        let body = 

        match b with 
        | Pair (c, Nil) -> _tag_ c 
        | Pair(c, d) -> _Seq_ (Pair(Symbol "begin", b))
        | _-> raise X_syntax_error
        in

        if noDups then LambdaSimple (aList, body)
        else raise X_syntax_error

    | _ -> raise X_syntax_error
     
(*MACRO-EXPANSIONS*)
  and pipeline e =

  pipe_through e [_LetX_;_QuasiX_; (fun s -> _LetX_(_LetstarX_ s)); (fun s -> _LetX_(_LetrecX_ s)); _AndX_; _MITX_;_CondX_]

  and pipe_through s c_arr = 
  match c_arr with
  | a :: b -> pipe_through (a s) b
  | [] -> s

  and pipeline_mul es =
  match es with
  | Nil -> Nil
  | Pair(a, b) -> Pair( pipeline a, pipeline_mul b)
  | _ -> pipeline es

  and xribs ribs =
    match ribs with 
    | Pair (rib, rest) -> (match rib with
                      | Pair (Symbol "else", todo) -> Pair (Symbol "begin", pipeline_mul todo)
                      | Pair (expr, Pair (Symbol "=>", Pair (exprf, Nil))) -> (
                              match rest with
                              | Nil -> Pair (Symbol "let",
                                        Pair
                                          (Pair (Pair (Symbol "value", Pair (pipeline expr, Nil)),
                                            Pair
                                            (Pair (Symbol "f",
                                              Pair (Pair (Symbol "lambda", Pair (Nil, Pair (pipeline exprf, Nil))),
                                                Nil)),
                                            Nil)),
                                          Pair
                                          (Pair (Symbol "if",
                                            Pair (Symbol "value",
                                              Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)), Nil))),
                                          Nil)))
                              | _ ->
                                            Pair (Symbol "let",
                                                Pair
                                                  (Pair (Pair (Symbol "value", Pair (pipeline expr, Nil)),
                                                    Pair
                                                    (Pair (Symbol "f",
                                                      Pair (Pair (Symbol "lambda", Pair (Nil, Pair (pipeline exprf, Nil))),
                                                        Nil)),
                                                    Pair
                                                      (Pair (Symbol "rest",
                                                        Pair (Pair (Symbol "lambda", Pair (Nil, Pair (pipeline(xribs rest), Nil))),
                                                        Nil)),
                                                      Nil))),
                                                  Pair
                                                  (Pair (Symbol "if",
                                                    Pair (Symbol "value",
                                                      Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
                                                      Pair (Pair (Symbol "rest", Nil), Nil)))),
                                                  Nil)))
                      )
                                                  
                      | Pair(expr, dit) ->  (match rest with
                                          |Nil ->
                                          Pair (Symbol "if",
                                              Pair (pipeline expr,
                                                Pair (Pair (Symbol "begin", pipeline_mul dit),Nil)))
                                          | _ ->
                                            Pair (Symbol "if",
                                              Pair (pipeline expr,
                                                Pair (Pair (Symbol "begin", pipeline dit),
                                                   Pair(pipeline (xribs rest),Nil))))
                      )
                      | _-> raise X_syntax_error
    )
    |Nil -> Pair(Pair (Symbol "begin", Nil),Nil)
    | _-> raise X_syntax_error

  and _CondX_ s =
    match s with
    | Pair(Symbol "cond", ribs) -> pipeline (xribs ribs)
    | _ -> s

  and makeand s =
    match s with
    | Pair (a, Nil) -> pipeline a
    | Pair(a, b)-> Pair (Symbol "if", Pair(pipeline a , Pair(makeand b, Pair(Bool false, Nil))))
    | _->raise X_syntax_error
  
  and _AndX_ s =
    match s with
    | Pair (Symbol "and", Nil) -> Bool true
    | Pair (Symbol "and", x) ->(try (makeand x)
                              with X_syntax_error -> s)
    | _ -> s  

  and getparams s =
     match s with
    | Nil -> Nil
    | Pair( Pair(param, Pair(arg, Nil)) , a) -> Pair(param, getparams a)
    | _ -> raise X_syntax_error

  and getargs s =
    match s with
    | Nil -> Nil
    | Pair( Pair(param, Pair(arg, Nil)) , a) -> Pair(pipeline arg, getargs a)
    | _-> raise X_syntax_error

  and  _LetX_ s =
    match s with
    | Pair (Symbol "let", Pair(ass, Pair(exp,Nil))) -> 
                (try 
                Pair( Pair( Symbol "lambda", Pair( getparams ass, Pair(pipeline exp,Nil))), getargs ass) with X_syntax_error -> s)
    | Pair (Symbol "let", Pair(ass, exps)) -> 
                (try 
                Pair( Pair( Symbol "lambda", Pair( getparams ass, pipeline_mul exps)), getargs ass) with X_syntax_error -> s)
    | _ -> s
 
  and _LetstarX_ s =
  match s with
  | Pair (Symbol "let*", Pair(Nil, exps)) -> Pair (Symbol "let", Pair(Nil, exps))

  | Pair (Symbol "let*", Pair(Pair(Pair(var, Pair(exp,Nil)),Nil), exps)) -> 
        Pair (Symbol "let", Pair(Pair(Pair(var, Pair(exp,Nil)),Nil), exps))
        
  | Pair (Symbol "let*", Pair(Pair(Pair(var, Pair(exp,Nil)),assigns), exps)) ->
        Pair (Symbol "let", Pair(Pair(Pair(var, Pair(exp,Nil)),Nil),
          Pair(Pair(Symbol "let*", Pair(assigns, exps)), Nil)))

  | _ -> s

  and rec_dontcare exps =
  match exps with
  | Nil -> Nil
  | Pair(Pair(f, Pair(exp, Nil)),next) -> Pair(Pair(f, Pair(Pair (Symbol "quote", Pair (Symbol "whatever", Nil)), Nil)),rec_dontcare next)
  | _ -> raise X_syntax_error

  and rec_set s exps =
  match s with
  | Nil -> exps
  | Pair(Pair(f, Pair(exp, Nil)),next) -> Pair(Pair(Symbol "set!", Pair(f, Pair( exp, Nil))), rec_set next exps)
  | _ -> raise X_syntax_error

  and _LetrecX_ s =
  match s with
  | Pair (Symbol "letrec", Pair(ass, Pair(exp, Nil))) -> Pair (Symbol "let", Pair(rec_dontcare ass, rec_set ass (Pair( exp, Nil))))
  | Pair (Symbol "letrec", Pair(ass, exps)) -> Pair (Symbol "let", Pair(rec_dontcare ass, rec_set ass ( exps)))
  | _ -> s

  and _MITX_ s =
  match s with
  | Pair(Symbol "define", Pair(Pair(name, argl), Nil)) -> s
  | Pair(Symbol "define", Pair(Pair(name, argl), exps)) -> 
    Pair(Symbol "define", Pair(name, Pair(Pair(Symbol "lambda", Pair(argl, pipeline_mul exps)),Nil)))
  | _ -> s

  and make_pair_func l f=
    match l with
    | [] -> Nil
    | a :: b -> Pair(f a, make_pair_func b f)

  and _QuasiX_ s =
  let rec expander sexpr =
    (match sexpr with 
          | Pair (Symbol "unquote", Pair (sexp, Nil)) -> sexp
          | Pair (Symbol "unquote-splicing", Pair (sexp, Nil)) -> raise X_syntax_error
          | Nil -> Pair (Symbol "quote", Pair (Nil, Nil))
          | Symbol sexp -> Pair (Symbol "quote", Pair (Symbol sexp, Nil))
          | Vector sexprs -> Pair (Symbol "vector",make_pair_func sexprs expander)
          | Pair(a, b) -> (match (a,b) with
                          | (Pair (Symbol "unquote-splicing", Pair (a_sexp, Nil)), b) -> 
                              Pair (Symbol "append", Pair (a_sexp, Pair (expander b, Nil)))
                          | (a, Pair (Symbol "unquote-splicing", Pair (b_sexp, Nil))) -> 
                              Pair (Symbol "cons", Pair (expander a, Pair (b_sexp, Nil)))
                          | _ -> Pair (Symbol "cons", Pair (expander a, Pair (expander b, Nil))))
          | _-> pipeline sexpr) in
  match s with 
  | Pair (Symbol "quasiquote", Pair (sexpr, Nil)) -> expander sexpr
  | _ -> s
            
  ;;

 
(*MACRO-EXPANSIONS-end*)

let tag_parse_expression sexpr = _tag_ sexpr;;

let rec tag_parse_expressions sexpr = 
  match sexpr with
  | [] -> []
  | a :: b -> tag_parse_expression a :: tag_parse_expressions b;;

  
end;; (* struct Tag_Parser *)
