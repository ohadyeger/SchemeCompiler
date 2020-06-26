#use "semantic-analyser.ml";;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * (int * string)) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

let rec make_fvars_tbl_func asts = [("boolean?",0) ; ("float?",1) ; ("integer?",2) ; ("pair?",3);
                                     ("null?", 4) ; ("char?",5); ("vector?",6) ; ("string?", 7);
                                     ("procedure?",8); ("symbol?",9) ; ("string-length",10);
                                     ("string-ref", 11); ("string-set!",12); ("make-string",13);
                                    ("vector-length",14) ; ("vector-ref",15); ("vector-set!",16);
                                    ("make-vector",17); ("symbol->string",18); ("char->integer",19) ; ("integer->char",20); ("eq?",21);
                                    ("+",22) ; ("*",23) ; ("-",24); ("/",25) ; ("<",26); ("=",27);
                                    ("car",28); ("cdr",29); ("set-car!",30); ("set-cdr!",31) ; ("cons",32) ; ("apply",33)] 
                                    
      @ create_freeVars_tbl asts 34 ["boolean?" ; "float?"; "integer?"; "pair?"; "null?"; "char?"; "vector?"; "string?";
                                    "procedure?"; "symbol?"; "string-length"; "string-ref"; "string-set!"; "make-string";
                                    "vector-length"; "vector-ref"; "vector-set!"; "make-vector"; "symbol->string"; 
                                    "char->integer"; "integer->char"; "eq?";
                                    "+"; "*"; "-"; "/"; "<"; "="; "car"; "cdr"; "set-car!"; "set-cdr!"; "cons"; "apply"]

and create_freeVars_tbl asts n fv_list=
  match asts with
  | [] -> []
  | Var' (VarFree s) :: b -> addIfUnique s n b fv_list
  | BoxSet' ((VarFree s), e2) :: b ->  addIfUnique s n b fv_list
  | Box' (VarFree s) :: b -> addIfUnique s n b fv_list
  | BoxGet' (VarFree s) :: b -> addIfUnique s n b fv_list

  | If' (e1,e2,e3) :: b -> create_freeVars_tbl ([e1; e2; e3] @ b) n fv_list
  | Seq' e_list :: b -> create_freeVars_tbl (e_list @ b) n fv_list

  | Set' (e1, e2) :: b -> create_freeVars_tbl ([e1; e2] @ b) n fv_list
  | Def' (e1, e2) :: b -> create_freeVars_tbl ([e1; e2] @ b) n fv_list
  | Or' e_list :: b ->  create_freeVars_tbl (e_list @ b) n fv_list
  
  | LambdaSimple' (s_list, e) :: b -> create_freeVars_tbl (e :: b) n fv_list
  | LambdaOpt' (s_list, s, e) :: b -> create_freeVars_tbl (e :: b) n fv_list

  | Applic' (e, e_list) :: b -> create_freeVars_tbl ((e :: e_list) @ b) n fv_list
  | ApplicTP' (e, e_list) :: b -> create_freeVars_tbl ((e :: e_list) @ b) n fv_list
  | a :: b -> create_freeVars_tbl b n fv_list

and exist_string s s_list =
  List.exists (fun str -> String.equal s str) s_list

and addIfUnique s n b fv_list = 
  if (exist_string s fv_list) 
  then (create_freeVars_tbl b n fv_list)
  else ((s, n) :: (create_freeVars_tbl b (n+1) (s :: fv_list)))
;;

let rec make_const_tbl_func asts = let table = [Void; Sexpr(Nil);
                                           Sexpr(Bool false);Sexpr(Bool true)] in
                              let table = table @ (create_const_tbl asts) in 
                              let table = remove_dup table [] in 
                              let table = expand_const_list table in 
                              let tuples = makeTuples (remove_dup table []) 0 in
                              makeTriples tuples tuples


(*Creates a constant table from asts list*)
and create_const_tbl asts = match asts with 
  | [] -> []
  | a :: b -> (create_single_const_tbl a) @ create_const_tbl b

(*Creates a constant table from single ast*)
and create_single_const_tbl ast = match ast with
  | Const' Sexpr(e) -> [Sexpr(e)]
  | If' (e1,e2,e3) -> (create_single_const_tbl e1) @ (create_single_const_tbl e2) @ (create_single_const_tbl e3)
  | Seq' e_list -> handle_list e_list 
  | Set' (e1, e2) -> (create_single_const_tbl e1) @ (create_single_const_tbl e2) 
  | Def' (e1, e2) -> (create_single_const_tbl e1) @ (create_single_const_tbl e2)
  | Or' e_list ->  handle_list e_list
  | LambdaSimple' (s_list, e) -> create_single_const_tbl e
  | LambdaOpt' (s_list, s, e) -> create_single_const_tbl e
  | Applic' (e, e_list) -> (create_single_const_tbl e) @ (handle_list e_list)
  | ApplicTP' (e, e_list) -> (create_single_const_tbl e) @ (handle_list e_list)
  | BoxSet' (e1, e2) -> (create_single_const_tbl e2)
  | _ -> [] 

  (* Handles recursion cases of above which has exp list *)
and handle_list e_list = match e_list with 
  | [] -> []
  | a :: b -> create_single_const_tbl a @ handle_list b

and isMember ele list=
  match list with
  | [] -> false
  | Sexpr(a) :: b -> if (sexpr_eq ele a) then true else (isMember ele b) 
  | Void :: b -> isMember ele b

(* Creating a new const list with no duplicates. initialized with no_dup_list=[]. *)
and remove_dup const_list no_dup_list = match const_list with 
  | [] -> no_dup_list
  | Sexpr(a) :: b -> (match (isMember a no_dup_list) with 
                                        | true -> (remove_dup b no_dup_list) 
                                        | false -> remove_dup b (no_dup_list @ [Sexpr(a)] ))
  | Void :: b -> remove_dup b (no_dup_list @ [Void])


(* Expands const_list with all sub expressions of each constant *)                                             
and expand_const_list const_list =  match const_list with
  | [] -> []
  | exp :: rest -> add_sub_exp exp @ expand_const_list rest                                               

(* Adds to const_list all sub expressions of exp *)
(*Sexpr(exp) -> [exprs] s.t. *)
and add_sub_exp exp = match exp with 

  | Sexpr (Symbol x) -> [(Sexpr(String x)) ; exp]
  | Sexpr (Pair (car, cdr)) -> 
      (add_sub_exp (Sexpr (car))) @ [Sexpr (car)] @ (add_sub_exp (Sexpr (cdr))) @ [Sexpr (cdr)] @ [exp]
  | Sexpr (Vector v) -> (expand_vector v) @ [Sexpr (Vector v)]
  | _ -> [exp]

and expand_vector const_list =  match const_list with
  | [] -> []
  | exp :: rest -> add_sub_exp (Sexpr (exp)) @ expand_vector rest 

and sizeof c = 
  match c with 
   | Bool _ -> 2
   | Nil -> 1
   | Number _-> 9
   | Char _ -> 2
   | String s -> 9 + (String.length s)
   | Symbol s -> 9
   | Pair _ -> 17
   | Vector v -> 9 + 8 * (List.length v)
   
and makeTuples cons_list n =
  match cons_list with
  | [] -> []
  | Sexpr(a) :: b -> (Sexpr(a) , n) :: (makeTuples b (n + (sizeof a)))
  | Void :: b -> (Void, n) :: (makeTuples b (n + 1))

and getExpAdd cons_list exp =
  match cons_list with
  | [] -> -1
  | (Sexpr(a), n) :: b ->  if (sexpr_eq exp a) then n else (getExpAdd b exp)
  | (Void, n) :: b -> getExpAdd b exp

and changeStringToAsci oldStr newStr = let n = (String.length oldStr -1) in
 match String.length oldStr with
  | 0 -> oldStr
  | 1 ->  newStr ^ string_of_int(int_of_char oldStr.[n])
  | _ ->  changeStringToAsci (String.sub oldStr 1 n) (newStr ^ string_of_int(int_of_char oldStr.[0])^",")

and makeTriple exp cons_list = match exp with 

  | (Sexpr (Symbol x), n ) -> (Sexpr (Symbol x), (n , "MAKE_LITERAL_SYMBOL(consts+" 
                                                       ^string_of_int((getExpAdd cons_list (String(x))))
                                                      ^")"))
  | (Sexpr (String x), n) -> (Sexpr (String x), (n, "MAKE_LITERAL_STRING "^(changeStringToAsci x "")))
  | (Sexpr (Number (Int(x))), n) ->(Sexpr (Number (Int(x))), (n , "MAKE_LITERAL_INT(" ^ 
                                                      string_of_int(x)^
                                                      ")"))
  | (Sexpr (Number (Float(x))), n) ->(Sexpr (Number (Float(x))), (n , "MAKE_LITERAL_FLOAT(" ^ 
                                                      string_of_float(x)^
                                                      ")"))
  | (Sexpr (Char c), n) -> (Sexpr (Char c), (n, "MAKE_LITERAL_CHAR ("^(string_of_int(int_of_char c))^")"))
  | (Sexpr (Bool false), n) -> (Sexpr (Bool false), (n, "MAKE_BOOL(0)"))
  | (Sexpr (Bool true), n) -> (Sexpr (Bool true), (n, "MAKE_BOOL(1)"))
  | (Sexpr (Pair(car, cdr)), n) -> (Sexpr (Pair(car, cdr)), (n, ("MAKE_LITERAL_PAIR(consts+" ^ 
                                                      string_of_int((getExpAdd cons_list car))^
                                                      ", consts+" ^ 
                                                      string_of_int((getExpAdd cons_list cdr))^
                                                      ")")))
  | (Void, n) -> (Void, (n, "MAKE_VOID"))
  | (Sexpr (Nil), n) ->(Sexpr (Nil), (n, "MAKE_NIL"))
  | (Sexpr (Vector v), n) -> (Sexpr (Vector v), (n, "MAKE_LITERAL_VECTOR "^(vectorTriple v cons_list)))                                              

and vectorTriple v cons_list= match v with 
  | [] -> ""
  | a :: [] -> "consts+"^string_of_int(getExpAdd cons_list a)
  | a :: b ->  "consts+"^string_of_int(getExpAdd cons_list a)^", "^ (vectorTriple b cons_list)

and makeTriples exps cons_list =
  match exps with
  | [] -> []
  | a :: b -> (makeTriple a cons_list) :: (makeTriples b cons_list);;

let inc count =
   count := !count +1;
   count;;

let label_gen name counter =
  name ^ (string_of_int(!(inc counter)));;

let label_end_lambda_body = (ref 0);;
let label_lambda_error = (ref 0);;
let label_lambda_body = (ref 0);;

let label_error = (ref 0);;
let label_errstring = (ref 0);;
let label_end_applic = (ref 0);;

let label_Lexit = (ref 0);;
let label_Lelse = (ref 0);;
let label_startlambda = (ref 0);;
let label_startlambdaopt = (ref 0);;
let label_startapplic = (ref 0);;
let label_startapplictp = (ref 0);;

let get_label_startapplic = (fun ()-> label_gen "start_applic" label_startapplic);;
let get_label_startapplictp = (fun ()-> label_gen "start_applicTP" label_startapplictp);;

let get_label_end_lambda_body = (fun ()-> label_gen "end_lambda_body" label_end_lambda_body);;
let get_label_lambda_error = (fun ()-> label_gen "label_lambda_error" label_lambda_error);;
let get_label_lambda_body = (fun ()-> label_gen "label_lambda_body" label_lambda_body);;

let get_label_error = (fun ()-> label_gen "error" label_error);;
let get_label_errstring = (fun ()-> label_gen "errstring" label_errstring);;
let get_label_end_applic = (fun ()-> label_gen "end_applic" label_end_applic);;

let get_label_Lexit = (fun ()-> label_gen "Lexit" label_Lexit);;
let get_label_Lelse = (fun ()-> label_gen "Lelse" label_Lelse);;
let get_label_startlambda = (fun ()-> label_gen "startlambda" label_startlambda);;
let get_label_startlambdaopt = (fun ()-> label_gen "startlambdaopt" label_startlambdaopt);;

let rec generate_func consts fvars e =
  match e with
  | Const' (Sexpr(c)) -> "mov rax, "^(getConstAdd consts c)^"\n"
  | Const' (Void) -> "mov rax, consts+0 \n"
  | Var'(VarParam(_, minor)) -> "
  mov rax, qword [rbp+"^string_of_int(8*(4+minor))^"] 
  "
  | Set'(Var'(VarParam(_, minor)),exp) -> "\n"^
        (generate_func consts fvars exp)^"
        mov qword [rbp + "^string_of_int(8*(4+minor))^"], rax
        mov rax, SOB_VOID_ADDRESS \n"
  | Box' (VarParam (_, n)) ->"
    mov rax, qword [rbp + "^string_of_int(8*(4+n))^"]
    BOX rax
    "
  | Var'(VarBound(_, major, minor)) -> 
      "
    mov rax, qword [rbp + 16]
    mov rax, qword [rax +"^string_of_int(9+8*major)^"]
    mov rax, qword [rax +"^string_of_int(9+8*minor)^"] \n"
  | Set'(Var'(VarBound(_, major, minor)),exp) -> 
    (generate_func consts fvars exp)^"
    mov rbx, qword [rbp + 16]
    mov rbx, qword [rbx + "^string_of_int(9+8*major)^"]
    mov qword [rbx + "^string_of_int(9+8*minor)^"], rax
    mov rax, SOB_VOID_ADDRESS \n"
  | Var'(VarFree(v)) -> "mov rax, qword ["^(getFvarAdd fvars v)^"] \n"
  | Set'(Var'(VarFree(v)),exp) -> 
    (generate_func consts fvars exp)^"
    mov qword ["^(getFvarAdd fvars v)^"], rax
    mov rax, SOB_VOID_ADDRESS \n"
  | Def'(Var'(VarFree x),v) -> (generate_func consts fvars v) ^ 
  "\nmov rbx, " ^(getFvarAdd fvars x) ^"
    mov qword [rbx], rax
    mov rax, SOB_VOID_ADDRESS \n"
  | Seq' (e_list) -> (generateList consts fvars e_list)
  | Or' (e_list) -> (generateOrList consts fvars e_list)
  | If' (e1,e2,e3) -> 
    let label_Lexit = get_label_Lexit() in
    let label_Lelse = get_label_Lelse() in
    (generate_func consts fvars e1)^
    "cmp word [rax], SOB_FALSE \n je "^label_Lelse^" \n"
    ^ (generate_func consts fvars e2)^
    "jmp "^label_Lexit^"\n "^label_Lelse^":\n"
    ^ (generate_func consts fvars e3)
    ^label_Lexit^":\n"
  | BoxGet'(v) -> (generate_func consts fvars (Var'(v)))^"\n mov rax, qword [rax] \n"
  | BoxSet'(v, exp) -> (generate_func consts fvars exp)^"\n push rax \n"^(generate_func consts fvars (Var'(v)))^
                              "\n pop qword [rax] \n mov rax, SOB_VOID_ADDRESS \n"
  | Applic' (e, e_list) -> 
    let label_error = get_label_error() in
    let label_errstring = get_label_errstring() in
    let label_end_applic = get_label_end_applic() in
    let label_startapplic = get_label_startapplic() in
    "
    ;### START APPLIC ###
    "^label_startapplic^":
    push 43962
    "^
    (generateAplic consts fvars (List.rev e_list)) ^
     "\npush " ^ string_of_int(List.length e_list) ^ "\n" ^ (generate_func consts fvars e) ^
    "
    cmp byte [rax], T_CLOSURE
    jnz "^label_error^"
     mov rdi, qword [rax + TYPE_SIZE]
     push rdi
     mov rdi, qword [rax + TYPE_SIZE + WORD_SIZE]
     call rdi
     add rsp, 8*1 
     pop rbx 
     inc rbx
     shl rbx, 3 
     add rsp, rbx
     jmp "^label_end_applic^"
     "^label_error^":
      mov rdi, "^label_errstring^"
      call printf
      jmp "^label_end_applic^"
    "^label_errstring^":
      db \"lambdaSimpleErr\", 0
    "^label_end_applic^":
    ;###END APPLIC###
    
    "
  | LambdaSimple' (s_list, e) ->
  let label_end_lambda = get_label_end_lambda_body() in
  let label_error_lambda = get_label_lambda_error() in
  let label_lambda_body = get_label_lambda_body() in
  let label_errstring = get_label_errstring() in
  let label_startlambda = get_label_startlambda() in
   "
    ;### START lambdaSimple ###
    
   "^label_startlambda^":
    mov rdi, qword [rbp + 2*WORD_SIZE]  ;; rdi stores pointer to the environment vector
    EXTEND_ENV rbx,rdi                 ;; extends env pointed by rdi to new env pointed by rbx
    MAKE_CLOSURE (rax, rbx, "^label_lambda_body^")
    jmp "^label_end_lambda^"
    "^label_lambda_body^":
      push rbp
      mov rbp, rsp

      mov rax," ^ string_of_int(List.length s_list) ^
     "
     cmp rax, PARAM_COUNT
      jne "^label_error_lambda^"\n"
      ^ (generate_func consts fvars e)^
   "\n
   leave
      ret

    "^label_error_lambda^":
      mov rdi, "^label_errstring^"
      call printf
      jmp "^label_end_lambda^"
      "^label_errstring^":
      db \"lambdaSimpleErr\", 0
      "^label_end_lambda^":
    ;###END LAMBDASIMPLE###
    "
| LambdaOpt' (s_list, s, e) -> 
let arg2 = string_of_int((4+List.length s_list)*8) in
let label_end_lambda = get_label_end_lambda_body() in
let label_error_lambda = get_label_lambda_error() in
let label_lambda_body = get_label_lambda_body() in
let label_errstring = get_label_errstring() in
let label_startlambdaopt = get_label_startlambdaopt() in
 "
    ;### START lambdaOpt ###
    
 "^label_startlambdaopt^":
  mov rdi, qword [rbp + 2*WORD_SIZE]  ;; rdi stores pointer to the environment vector
  EXTEND_ENV rbx,rdi                 ;; extends env pointed by rdi to new env pointed by rbx
  MAKE_CLOSURE (rax, rbx, "^label_lambda_body^")
  jmp "^label_end_lambda^"
  "^label_lambda_body^":
    push rbp
    mov rbp, rsp

    mov rax," ^ string_of_int(List.length s_list) ^
   "
   cmp rax, PARAM_COUNT
    jg "^label_error_lambda^
    "
    mov rdi, "^string_of_int(List.length s_list)^ "
    mov rsi,"^arg2^"
    ADJUST_STACK rdi,rsi
    "^(generate_func consts fvars e)^
 "
    leave
    ret
  "^label_error_lambda^":
    mov rdi, "^label_errstring^"
    call printf
    jmp "^label_end_lambda^"
    "^label_errstring^":
    db \"lambdaSimpleErr\", 0
    "^label_end_lambda^":
    ;###END LAMBDAOPT###
    "

| ApplicTP' (e, e_list) ->(*(generate_func consts fvars (Applic' (e, e_list)))*)
  let param_count = string_of_int(List.length e_list) in 
  let param_count_5 = string_of_int((List.length e_list) +5) in
  let label_error = get_label_error() in 
  let label_errstring = get_label_errstring() in
  let label_end_applic = get_label_end_applic() in
  let label_startapplictp = get_label_startapplictp() in
"
    ;### START applicTP ###
    "^label_startapplictp^":
push 43962
"^
(generateAplic consts fvars (List.rev e_list)) ^
 "\npush " ^ param_count ^ "\n" ^ (generate_func consts fvars e) ^
"
cmp byte [rax], T_CLOSURE 
jnz "^label_error^"       
 mov rdi, qword [rax + TYPE_SIZE] ;rdi <- lex_env
 push rdi
 mov r8, qword [rbp + 8 * 1] 
 push r8
 mov rsi, qword[rbp]
 mov r8, qword[rax + TYPE_SIZE + WORD_SIZE]
 SHIFT_FRAME "^param_count_5^"
 mov rbp, rsi
 jmp r8
 "^label_error^":
  mov rdi, "^label_errstring^"
  call printf
  jmp "^label_end_applic^"
"^label_errstring^":
  db \"lambdaSimpleErr\", 0
"^label_end_applic^":
;###END applicTP###
"
|_ -> "
jmp programerror    
"

and generateAplic consts fvars e_list = match e_list with 
  | [] -> ""
  | a :: b -> (generate_func consts fvars a) ^ "\npush rax\n" ^ (generateAplic consts fvars b)
  
and generateList consts fvars es =
  match es with
  | [] -> ""
  | a :: b -> (generate_func consts fvars a) ^"\n"^(generateList consts fvars b)

and generateOrList consts fvars es = let label_Lexit = get_label_Lexit() in
let rec nested_generateOrList consts fvars es =
  match es with
  | [] -> label_Lexit^": \n"
  | a :: b -> 
    (generate_func consts fvars a) ^
    "\n cmp word [rax], SOB_FALSE
    jne "^label_Lexit^" \n"
    ^(nested_generateOrList consts fvars b) in
    nested_generateOrList consts fvars es

and getConstAdd consts exp =
  match consts with
  | [] -> string_of_int (-1)
  | (Sexpr(a), (n, _)) :: b ->  if (sexpr_eq exp a) then "consts+"^(string_of_int n) else (getConstAdd b exp)
  | (Void, (n, _)) :: b -> getConstAdd b exp

and getFvarAdd fvars v =
  match fvars with
  | [] -> string_of_int (-1)
  | (s, n) :: b ->  if (s = v) then "FVAR("^(string_of_int n)^")" else (getFvarAdd b v)

module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = make_const_tbl_func asts;;
  let make_fvars_tbl asts = make_fvars_tbl_func asts;;
  let generate consts fvars e = generate_func consts fvars e;;
end;;
