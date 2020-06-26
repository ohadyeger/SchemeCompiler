(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Ohad Yeger $ Eden Azulay, 2018
 *)

#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

let makeEmptyEnv = [[]];;

let extendEnv vars env = vars :: env;;

let isEmptyEnv env = env = [[]];;

let rec applyFrame fr v n =
  match fr with
  | [] -> -1
  | s :: tail -> (match (expr_eq (Var s) v) with
                  | false -> applyFrame tail v (n + 1)
                  | _ -> n);;
   

let rec applyEnv var env n =
   match env with 
    | [[]] -> (-1, -1)
    | fr :: rest -> (match (applyFrame fr var 0)  with
                    | -1 -> applyEnv var rest (n + 1)
                    | k -> (n , k)) 
    | _ -> raise X_syntax_error

let indexVar (i,j) v =
  match (i,j),v  with
  | (-1,-1),Var s -> VarFree s
  | ( 0, j),Var s -> VarParam (s, j)
  | ( i, j),Var s -> VarBound (s, i-1, j)
  | _ -> raise X_syntax_error

let _tagVar_ v env =
  indexVar (applyEnv v env 0) v;;

let enqueue list el =
  List.rev (List.cons el (List.rev list));;

let rec _ala_ exp env =
  match exp with
  | Var s -> Var'(_tagVar_ exp env)
  | LambdaSimple (s_list, expr) -> _tagLambda_ exp env
  | LambdaOpt (s_list , s ,expr) -> _tagLambda_ exp env
  | Const  c -> Const' c
  | If (e1,e2,e3) -> If' (_ala_ e1 env, _ala_ e2 env, _ala_ e3 env)
  | Seq e_list -> Seq' (_ala_list e_list env)
  | Set (e1 ,e2) -> Set' (_ala_ e1 env, _ala_ e2 env)
  | Def (e1 ,e2) -> Def' (_ala_ e1 env, _ala_ e2 env)
  | Or e_list -> Or' (_ala_list e_list env)
  | Applic (proc, e_list) -> Applic' ( _ala_ proc env , _ala_list e_list env)

  and _tagLambda_ exp env= match exp with 
  | LambdaSimple (s_list, expr) -> LambdaSimple' (s_list, _ala_ expr (extendEnv s_list env)) 
  | LambdaOpt (s_list , s ,expr) ->  LambdaOpt'(s_list, s, _ala_ expr (extendEnv (enqueue s_list s) env))
  | _ -> raise X_syntax_error

  and _ala_list exps env =
    match exps with
    |[] -> []
    |a :: b -> (_ala_ a env) :: (_ala_list b env)
    ;;

let rec _anno_ exp in_tp =
  match exp with
  | Var' s -> Var' s
  | LambdaSimple' (s_list, expr) -> LambdaSimple' (s_list, _anno_ expr true) 
  | LambdaOpt' (s_list , s ,expr) ->  LambdaOpt' (s_list , s , _anno_ expr true)
  | Const' c -> Const' c
  | If' (e1,e2,e3) -> If' (_anno_ e1 false, _anno_ e2 in_tp, _anno_ e3 in_tp)
  | Seq' e_list -> Seq' (list_anno e_list in_tp)
  | Set' (e1 ,e2) -> Set' (_anno_ e1 false, _anno_ e2 false)
  | Def' (e1 ,e2) -> Def' (_anno_ e1 false, _anno_ e2 false)
  | Or' e_list -> Or' (list_anno e_list in_tp)
  | Applic' (proc, e_list) -> if in_tp then ApplicTP' ( proc , list_anno e_list false) 
                                else Applic' (_anno_ proc in_tp, list_anno e_list false)
  | _ -> raise X_syntax_error
                
  and list_anno exp in_tp =
    match exp with
    | [] -> []
    | a :: [] -> (_anno_ a in_tp) :: []
    | a :: b -> (_anno_ a false) :: (list_anno b in_tp)
    ;;
(*
let box x = [|x|];;
let box_get x = x.(0);;
let box_set x y = x.(0) <- y;;
*)
let extract_var v =
  match v with
  | Var' (VarFree s) -> s
  | Var' (VarBound (a ,b, c)) -> a
  | Var' (VarParam (a,b)) -> a
  | _ -> raise X_syntax_error;;


let get vector n =
  match vector with
  | [a ;b ;c ;d] -> (match n with
                      |0 -> a
                      |1 -> b
                      |2 -> c 
                      |3 -> d
                      |_ -> raise X_syntax_error)
  | _ -> raise X_syntax_error;;

(*model: (read, write, nested, boxed)*)
let rec nestedIsBox exp v =
  match exp with
  | Var' (VarFree s) -> [s = v; false; false; false]
  | Var' (VarParam (s, a)) -> [s = v; false; false; false]
  | Var' (VarBound (s,a,b)) -> [s = v; false; false; false]
  | If' (e1,e2,e3) -> matchbox_l ((nestedIsBox e1 v) :: (nestedIsBox e2 v) :: (nestedIsBox e3 v) :: [])
  | Const' (c) -> [false; false; false; false]
  | Applic'(proc, e_list) -> matchbox_l (nestedIsBox proc v :: (List.map (fun(x)-> (nestedIsBox x v)) e_list))
  | ApplicTP'(proc, e_list) -> matchbox_l (nestedIsBox proc v :: (List.map (fun(x)-> (nestedIsBox x v)) e_list))
  | Or' (e_list) -> matchbox_l (List.map (fun(x)-> nestedIsBox x v) e_list)
  | Set' (e1, e2) -> matchbox (checkSet e1 v) (nestedIsBox e2 v)
  | BoxSet' (e1, e2) -> nestedIsBox e2 v
  | Seq' (e_list) -> matchbox_l (List.map (fun(x)-> nestedIsBox x v) e_list)
  | LambdaSimple' (s_list, expr) -> h_lambda s_list expr v
  | LambdaOpt' (s_list , s ,expr) -> h_lambda (enqueue s_list s) expr v
  | _ -> [false; false; false; false]

  and checkSet setexp v =
    match setexp with
    | Var' s -> if ((extract_var setexp) = v) then [false; true; false; false] else [false; false; false; false]
    | _ -> [false; false; false; false]
  
  and isBox exp v =
  match exp with
  (*| Seq' [Set' (Var' (VarParm (c, i)), Box' (VarParam (c, i)))] :: rest -> isBox rest v*)
  | Var' s -> false
  | Const' c -> false
  | Def' (e1 ,e2) -> false
  | _ -> (match (nestedIsBox exp v) with
          |[_; _; _; z] -> z
          | _ -> raise X_syntax_error)

  and unmakeBoxed a =
    match a with
    | [f; b; c; d] -> [f; b; c; false]
    | _ -> a
  and makeNested a =
    match a with
    | [true; b; _; c] -> [true; b; true; c]
    | [x; true; _; c] -> [x; true; true; c]
    | _ -> a
  
  and h_lambda s_list expr var =
   if (List.find_opt (fun (x) -> x = var) s_list) = None
      then (unmakeBoxed (makeNested (nestedIsBox expr var)))
      else [false; false; false; false]
  
  and matchbox v1 v2 =
  [get v1 0 || get v2 0; get v1 1 || get v2 1; get v1 2 || get v2 2;
    get v1 3 || get v2 3 || (((get v1 0 && get v2 1)||(get v1 1 && get v2 0)) && (get v1 2 || get v2 2))]
    
  and matchbox_l v_list =
  match v_list with
  | [] -> [false; false; false; false]
  | a :: b -> matchbox a (matchbox_l b) 

  and boxAll_l es =
    match es with
    | [] -> []
    | a :: b -> (_BoxAll_ a):: (boxAll_l b)
  
  and _BoxAll_ e =
    match e with 
    | Var' s -> e
    | If' (e1,e2,e3) -> If'(_BoxAll_ e1, _BoxAll_ e2, _BoxAll_ e3)
    | Const' (c) -> Const' c
    | Applic'(proc, e_list) -> Applic'(_BoxAll_ proc, boxAll_l e_list)
    | ApplicTP'(proc, e_list) -> ApplicTP'(_BoxAll_ proc, boxAll_l e_list)
    | Or' (e_list) -> Or' (boxAll_l e_list)
    | Set' (e1, e2) -> Set' (_BoxAll_ e1, _BoxAll_ e2)
    | Seq' (e_list) -> Seq' (boxAll_l e_list)
    | LambdaSimple' (s_list, expr) ->  box_lambda e
    | LambdaOpt' (s_list , s ,expr) ->  box_lambda e
    | Def' (e1 ,e2) -> Def' (e1, _BoxAll_ e2)
    | _ -> raise X_syntax_error

  and add_set_box expr s minor =
    match expr with

    | Seq' ((Set'(Var'(VarParam(s1, m1)),
         Box'(VarParam(s2, m2)))) :: exp) -> 
      Seq' ((Set'(Var'(VarParam(s, minor)), Box'(VarParam(s, minor))))
         :: (Set'(Var'(VarParam(s1, m1)), Box'(VarParam(s2, m2)))) :: exp)

    | _ -> Seq' ((Set'(Var'(VarParam(s, minor)),
       Box'(VarParam(s, minor)))) :: expr :: [])

  and box_lambda_body s_list expr minor=
    match s_list with
    | [] -> ([], expr, minor)
    | a :: b -> if (isBox expr a) 
                then let (n1, n2, m) = (box_lambda_body b (travers_and_box expr a)(minor+1))
                     in (a :: n1, add_set_box n2 a minor, m) 
                else let (n1, n2, m) = box_lambda_body b expr (minor+1)
                     in (a :: n1, n2, m)

  and box_lambda e =
    match e with
    | LambdaSimple' (s_list, expr) ->(
                     let (n_list, n_exp, n) = box_lambda_body s_list (_BoxAll_ expr) 0
                     in LambdaSimple' (s_list, n_exp))
    | LambdaOpt' (s_list , s ,expr) ->
                    let (n_list, n_exp, n) = box_lambda_body (enqueue s_list s) (_BoxAll_ expr) 0
                     in LambdaOpt' (s_list , s ,n_exp)
    | _ -> raise X_syntax_error

  and travers_and_box exp v =
    match exp with
    | Var' (VarFree s) -> exp
    | Var' s -> if ((extract_var exp) = v) then BoxGet'(s) else exp
    | If' (e1,e2,e3) -> If'(travers_and_box e1 v, travers_and_box e2 v, travers_and_box e3 v)
    | Const' (c) -> Const' c
    | Applic'(proc, e_list) -> Applic'(travers_and_box proc v, travers_and_box_list e_list v)
    | ApplicTP'(proc, e_list) -> ApplicTP'(travers_and_box proc v, travers_and_box_list e_list v)
    | Or' (e_list) -> Or' (travers_and_box_list e_list v)
    | Set' (Var' s, e2) -> if ((extract_var (Var' s)) =  v) then BoxSet'(s, travers_and_box e2 v) else Set' (Var' s, travers_and_box e2 v) 
    | LambdaSimple' (s_list, expr) -> travers_and_box_lambda exp v
    | LambdaOpt' (s_list , s ,expr) -> travers_and_box_lambda exp v
    | Def' (e1 ,e2) -> Def' (e1, travers_and_box e2 v)
    | BoxSet' (e1, e2) -> BoxSet' (e1, travers_and_box e2 v)
    | Seq' ((Set' (Var' (VarParam (a,b)), Box' (VarParam (c, d)))) :: rest) -> 
                Seq' ((Set' (Var' (VarParam (a,b)), Box' (VarParam (c, d)))) :: (travers_and_box_list rest v))
    | Seq' (e_list) -> Seq' (travers_and_box_list e_list v)
    | BoxGet' e1 -> exp
    | _ -> raise X_syntax_error

  and travers_and_box_list exps v =
    match exps with
    | [] -> []
    | a :: b -> travers_and_box a v:: (travers_and_box_list b v)
  
  and travers_and_box_lambda e v =
    match e with
    | LambdaSimple' (s_list, expr) ->
             if (List.find_opt (fun (x) -> x = v) s_list) = None
             then LambdaSimple' (s_list, travers_and_box expr v)
             else e
    | LambdaOpt' (s_list , s ,expr) ->
             if (List.find_opt (fun (x) -> x = v) s_list) = None && s != v
             then LambdaOpt' (s_list,s, travers_and_box expr v)
             else e
    | _ -> raise X_syntax_error
    ;;

  
module Semantics : SEMANTICS = struct

let annotate_lexical_addresses e = _ala_ e (makeEmptyEnv);;

let annotate_tail_calls e = _anno_ e false;;

let box_set e = _BoxAll_ e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
