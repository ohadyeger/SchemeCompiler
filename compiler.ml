#use "code-gen.ml";;

let file_to_string f =
  let ic = open_in f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s;;

let string_to_asts s = List.map Semantics.run_semantics
                         (Tag_Parser.tag_parse_expressions
                            (Reader.read_sexprs s));;

let rec getConstAdd consts exp =
  match consts with
  | [] -> string_of_int (-1)
  | (Sexpr(a), (n, _)) :: b ->  if (sexpr_eq exp a) then "consts+"^(string_of_int n) else (getConstAdd b exp)
  | (Void, (n, _)) :: b -> getConstAdd b exp

let rec getFvarAdd fvars v =
  match fvars with
  | [] -> string_of_int (-1)
  | (s, n) :: b ->  if (s = v) then "FVAR("^(string_of_int n)^")" else (getFvarAdd b v)

let primitive_names_to_labels = 
  ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
   "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
   "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
   "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
   "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
   "make-vector", "make_vector"; "symbol->string", "symbol_to_string"; 
   "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
   "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ"
    ; "car", "car"; "cdr", "cdr"; "set-car!", "set_car"; "set-cdr!" ,"set_cdr"; "cons", "cons" ; "apply", "apply"];;

let make_prologue consts_tbl fvars_tbl =
  let get_const_address const = getConstAdd consts_tbl const in
  let get_fvar_address const = getFvarAdd fvars_tbl const in
  let make_primitive_closure (prim, label) =
"    MAKE_CLOSURE(rax, 57005, " ^ label  ^ ")
    mov [" ^ (get_fvar_address prim)  ^ "], rax" in
  let make_constant (c, (a, s)) = s in
  
"
;;; All the macros and the scheme-object printing procedure
;;; are defined in compiler.s
%include \"compiler.s\"

section .bss
malloc_pointer:
    resq 1

section .data
consts:
" ^ (String.concat "\n" (List.map make_constant consts_tbl)) ^ "

;;; These macro definitions are required for the primitive
;;; definitions in the epilogue to work properly
%define SOB_VOID_ADDRESS consts+0
%define SOB_NIL_ADDRESS " ^ get_const_address Nil ^ "
%define SOB_FALSE_ADDRESS " ^ get_const_address (Bool false) ^ "
%define SOB_TRUE_ADDRESS " ^ get_const_address (Bool true) ^ "

fvar_tbl:
" ^ (String.concat "\n" (List.map (fun _ -> "dq T_UNDEFINED") fvars_tbl)) ^ "

global main
section .text
main:
    ;; set up the heap
    mov rdi, MB(100)
    call malloc
    mov [malloc_pointer], rax

    ;; Set up the dummy activation frame
    ;; The dummy return address is T_UNDEFINED
    ;; (which a is a macro for 0) so that returning
    ;; from the top level (which SHOULD NOT HAPPEN
    ;; AND IS A BUG) will cause a segfault.
    push 43962
    push 0
    push qword 57005
    push qword T_UNDEFINED
    push rbp
    mov rbp, rsp
    call code_fragment
    add rsp, 8*5
    ret


code_fragment:
    ;; Set up the primitive stdlib fvars:
    ;; Since the primtive procedures are defined in assembly,
    ;; they are not generated by scheme (define ...) expressions.
    ;; This is where we emulate the missing (define ...) expressions
    ;; for all the primitive procedures.

" ^ (String.concat "\n" (List.map make_primitive_closure primitive_names_to_labels))^"\n"

let epilogue = "";;

exception X_missing_input_file;;

try
  let infile = Sys.argv.(1) in 
  let code =  (file_to_string "stdlib.scm") ^ (file_to_string infile) in
  let asts = string_to_asts code in
  let consts_tbl = Code_Gen.make_consts_tbl asts in
  let fvars_tbl = Code_Gen.make_fvars_tbl asts in
  let generate = Code_Gen.generate consts_tbl fvars_tbl in
  let code_fragment = "\n;##### MY CODE #######\n"^String.concat "\n\n"
                        (List.map
                           (fun ast -> (generate ast) ^ "\ncall write_sob_if_not_void\n")
                           asts)^"\nret\n;##### END  -- MY CODE #######\n" in
  let provided_primitives = file_to_string "prims.s" in
                   
  print_string ((make_prologue consts_tbl fvars_tbl)  ^
                  code_fragment ^
                    provided_primitives ^ "\n" ^ epilogue)

with Invalid_argument(x) -> raise X_missing_input_file;;
