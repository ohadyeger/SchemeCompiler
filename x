#use "pc.ml";;
#use "reader.ml";;
#use "tag-parser.ml";;
#use "semantic-analyser.ml";;
#use "code-gen.ml";;
#use "compiler.ml";;

open PC;;
open Tag_Parser;;
open Reader;;
open Semantics;;
open Code_Gen;;

let oldtest expr =
string_to_asts expr ;;

let anno expr =
run_semantics (tag_parse_expression(read_sexpr expr));;

let test exp= 
    let e = string_to_asts exp in
    let ct = make_consts_tbl e in
    let vt = make_fvars_tbl e in
    List.map (fun x -> generate ct vt x) e;;

let fvt exp = 
make_fvars_tbl(string_to_asts exp);;
