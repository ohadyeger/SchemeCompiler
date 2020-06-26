
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

 #use "pc.ml";;
 open PC;;
  
 type number =
   | Int of int
   | Float of float;;
   
 type sexpr =
   | Bool of bool
   | Nil
   | Number of number
   | Char of char
   | String of string
   | Symbol of string
   | Pair of sexpr * sexpr
   | Vector of sexpr list;;
 
let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> if (List.length l1 != List.length l2) then false else List.for_all2 sexpr_eq l1 l2
  | _ -> false;;
 
 
 
 module Reader: sig
   val read_sexpr : string -> sexpr
   val read_sexprs : string -> sexpr list
 end
 = struct
 let normalize_scheme_symbol str =
   let s = string_to_list str in
   if (andmap
   (fun ch -> (ch = (lowercase_ascii ch)))
   s) then str
   else Printf.sprintf "|%s|" str;;

   (*ToolBox*)
 
 let _chartolist_ nt =
   pack nt (fun (c) -> [c]);;
 
 let _pairtolist_ nt =
   pack nt (fun (a,b)-> [a; b]);;
 
 let __space__ =
   const (fun ch -> ch <= char_of_int(32));;
 
 let make_enclosed _l_ _p_ _r_ =
   let _enclosed_ = caten (caten _l_ _p_) _r_ in
   pack _enclosed_ (fun ((l, p), r) -> p);;
 
 let make__space_d _p_ = 
   let _st__space__ = star __space__ in
   make_enclosed _st__space__ _p_ _st__space__;;
 
 let _PlusSpaced_ _p_ = 
   let _st__space__ = plus __space__ in
   make_enclosed _st__space__ _p_ _st__space__;;
 
 let make_left_assoc _p_ _op_ list_packer =
   let _head_ = _p_ in
   let _tail_ = star (pack (caten _op_ _p_) (fun (o, p) -> p)) in
   pack (caten _head_ _tail_)
        (fun (hd, tl) -> match tl with
                         | [] -> hd
                         | tl -> list_packer (hd::tl))
 
 let _digit_ = range '0' '9';;
 let _xdigit_ = range_ci 'a' 'f';;
 let _letters_ = range_ci 'a' 'z';;
 let _hash_ = char '#';;
 let _expop_ = make__space_d (char '^');;
 let _greaterop_ = make__space_d (char '>');;
 let _smallerop_ = make__space_d (char '<');;
 let _lparen_ = make__space_d (char '(');;
 let _rparen_ = make__space_d (char ')');;
 let _lbracket_ = make__space_d (char '[');;
 let _rbracket_ = make__space_d (char ']');;
 let _mulop_ = make__space_d (char '*');;
 let _plus_ = make__space_d (char '+');;
 let _minus_ = make__space_d (char '-');;
 let _semi_ = char ';' ;;
 let _backlash_ = char '\\';;
 let _quotes_ = char '\"';;
 let _t_ = char 't';;
 let _f_ = char 'f';;
 let _n_ = char 'n';;
 let _r_ = char 'r';;
 let _dollar_ = char '$';;
 let _exclam_ = char '!';;
 let _exp_ = char '^';;
 let _underscore_ = char '_';;
 let _equal_ = char '=';;
 let _smaller_ = char '<';;
 let _minuschar_ = char '-';;
 let _pluschar_ = char '+';;
 let _greater_ = char '>';;
 let _question_ = char '?';;
 let _forslash_ = char '/';;
 let _colon_ = char ':';;
 let _x_ = char_ci 'x';;
 let _mul_ = char '*';;
 let _quote_ = char '\'';;
 let _quasi_ = char '`';;
 let _comma_ = char ',';;
 let _at_ = char '@';;
 let _scientificE_ = pack (char_ci 'e') (fun (s) -> 10);;
 let _endline_ = char '\n';;
 
 let _makeCompat_ nt =
   pack nt (fun (c) -> [c]);;
 
 let unpack nt =
   pack nt (fun ((l,m),r)-> ([l ; m], r));;
 
 (*ToolBox end*)
 
 (*line comments*)
(*
  let const_dots =
  function 
  | '.'::'.'::'.'::s -> (Void, '.'::'.'::'.'::s)
  | _ -> raise X_no_match;;
*)
 let _NotEnd_ =
  const (fun (c)-> c != '\n');;

 let _LineComment_ = 
  make__space_d( disj (pack (caten (caten _semi_ (star _NotEnd_)) _endline_) (fun ((a,b),c)-> Vector[Nil;Nil]))
  (pack  (caten (caten _semi_ (star _NotEnd_))nt_end_of_input) (fun (a,b)-> Vector[Nil;Nil])));;
 
 (*let _LineComment__ = pack ( caten (caten _semi_ (star (diff nt_any _endline_))) _endline_) (fun ((n, s), b) -> n);;*)
 (*line comments end*)

 (*number*)
 
 let _makeInt_ nt =
  pack nt (fun (n) -> Number(Int (n)));;

let _makeFloat_ nt =
  pack nt (fun (n) -> Number(Float (n)));;

let _sign_ =
  pack (maybe (disj _pluschar_ _minuschar_)) (fun (l) -> match l with
                        | Some(e) -> e
                        | _ -> '+');;

let _decimal_ =
  _chartolist_ (char '.');;

let _Natural_ =
  pack (plus _digit_) (fun (ds) -> int_of_string (list_to_string ds));;

let _Integer_ =
  pack (caten _sign_ _Natural_) (fun (l,r) -> match l with
                        | '-' -> -r
                        | _ -> r);;

let _Integer_fl_ = 
 pack (caten_list [ (_chartolist_ _sign_); plus _digit_])
 (fun (a) -> match a with
            | [b ; c]-> (match b with
                         | [] -> raise X_no_match
                         | ['+'] -> String.concat "" ["" ; (list_to_string c)]
                         | ['-'] -> String.concat "" ["-" ; (list_to_string c)]
                         | _ -> raise X_no_match)
 | _ -> raise X_no_match);;

let _Float_ =
  pack (caten_list [_Integer_fl_ ; (pack _decimal_ list_to_string);
   (pack (plus _digit_) (fun (ds) -> list_to_string ds))]) 
   (fun (a)-> float_of_string (String.concat "" a));;

let _HexPrefix_ = 
  _pairtolist_ (caten _hash_ _x_) ;;

let _HexDigit_ = 
  disj _digit_ _xdigit_;;

let _HexNatural_ = 
  plus _HexDigit_;;

let _hex_list_to_int_ c = 
  int_of_string (String.concat "" ["0x" ; (list_to_string c)]);;

let _HexInteger_ =
  pack (caten_list [_HexPrefix_; (_chartolist_ _sign_); _HexNatural_])
          (fun l-> match l with
                          | [a ;['+'];c] -> int_of_string (String.concat "" ["0x" ; (list_to_string c)])
                          | [a ;['-'];c] -> -1 * int_of_string (String.concat "" ["0x" ; (list_to_string c)])
                          | _ -> raise X_no_match);;

let _HexInteger_fl_ = 
 pack (pack (caten_list [_HexPrefix_; (_chartolist_ _sign_); _HexNatural_])
 (fun (m) -> match m with
            | ([a ; b ; c])-> (match b with
                         | [] -> raise X_no_match
                         | ['+'] -> String.concat "" ["0x" ; (list_to_string c)]
                         | ['-'] -> String.concat "" ["-0x" ; (list_to_string c)] 
                         | _ -> raise X_no_match)
            | _ -> raise X_no_match))string_to_list;;

let _HexFloat_ = 
  let catened = caten_list [_HexInteger_fl_ ; _decimal_; _HexNatural_] in
  pack catened (fun d -> float_of_string (list_to_string (List.concat d)));;

let _scientific_ =
   let _scienprefix_ = disj_list [_Float_ ; pack (_Integer_) (fun a -> float a)] in
   let _catened_ = caten_list [ _scienprefix_ ; pack (_scientificE_) (fun a -> float a) ; pack (_Integer_) (fun a -> float a)] in
   pack (_catened_) (fun (m) -> match m with
                          | a -> (match a with
                              | [d ; b; c] -> d *. (b**c)
                              | _ -> raise X_no_match)
                          );;

let _Number_ =
  disj_list  [_makeFloat_ _HexFloat_ ; _makeInt_ _HexInteger_; _makeFloat_ _scientific_ ; _makeFloat_ _Float_ ; _makeInt_ _Integer_; ];;

(*number end*)
 
 (*string*)
 
 let _StringLiteralChar_ =
   pack (const (fun ch -> ch != '\\' && ch != '\"')) (fun (c) -> [c]);;

let _newbackslash_ = 
pack( caten (char '\\') (char '\\') ) (fun (_) -> (['\\']));;
 
 let _metan_ = 
	pack( caten (char '\\') (char 'n') ) (fun _ -> ['\n']);;
let _metar_ = 
	pack( caten (char '\\') (char 'r') ) (fun _ ->['\r']);;


  let _metaq_ =
	pack( caten (char '\\') (char '\"'))  (fun _ -> ['\"']);; 


let _metat_ = 
	pack( caten (char '\\') (char 't') ) (fun _ -> ['\t']);;

let _metaf_ = 
	pack( caten (char '\\') (char 'f') )  (fun _ -> [Char.chr 12]);;


  let _StringMetaChar_ = disj_list [ _newbackslash_ ; _metan_ ; _metar_; _metaq_ ; _metat_ ; _metaf_];;

 let _StringHexChar_ =  
   pack (caten_list [pack (caten _backlash_ _x_) (fun (l, b) -> ['0';'x']); _HexNatural_; pack _semi_ (fun a-> [])]) 
   (fun d -> [char_of_int (int_of_string(list_to_string(List.concat d)))]);;
 
 let _StringChar_ = 
   disj_list [_StringLiteralChar_ ; _StringHexChar_ ; _StringMetaChar_];;
 
 let _String_ = 
     let _specialqoute_ = pack (_quotes_) (fun (c) -> [c]) in
     let packed = pack (caten_list [_specialqoute_ ; pack (star _StringChar_) 
                 (fun d -> List.concat d); _specialqoute_]) (fun d -> List.concat d) in
                 pack packed (fun (l) -> 
                               let arr = Array.of_list l in
                               let len = Array.length arr in
                               let newl = Array.sub arr 1 (len-2) in
                               let string = list_to_string (Array.to_list newl) in
                               String string );;
 
 (*string end*)
 
 (*symbol*)
 
 let _SymbolChar_ =
   disj_list [
               _digit_; _letters_; _exclam_; _dollar_; 
               _exp_; _mul_; _minuschar_; _underscore_; 
               _equal_; _pluschar_; _smaller_; _greater_;
               _question_; _forslash_; _colon_
             ] ;;
  
 let _Symbol_ = 
   let new_symbol = pack (plus _SymbolChar_) (fun (ds) -> String.lowercase_ascii (list_to_string ds)) in
       pack new_symbol (fun (s) -> Symbol s);;
 
 (*symbol end*)
 
 (*boolean*)
 let _true_ = 
   let _t_ = (disj (char 't') (char 'T')) in 
   let _tval_ = caten _hash_ _t_ in
   pack _tval_ (fun (t, l)-> Bool true);;
 
 let _false_ = 
   let _f_ = (disj (char 'f') (char 'F')) in 
   let _fval_ = caten _hash_ _f_ in
   pack _fval_ (fun (f, l)-> Bool false);;
 
 let _Boolean_ = 
   make__space_d (disj _true_ _false_);;
 
 (*boolean end*)
 
 (*char*)
 
 let _charPrefix_ = 
   caten _hash_ (char '\\');;
 
 let _visSimpleChar_ =
   const (fun ch -> ch > ' ');;
   
 let _newl_    =   word_ci "newline";;
 let _nul_     =   word_ci "nul";;
 let _page_    =   word_ci "page";;
 let _return_  =   word_ci "return";;
 let _space_   =   word_ci "space";;
 let _tab_     =   word_ci "tab";;
 
 let _namedChar_ = 
   disj_list [_newl_; _nul_; _page_; _return_; _space_; _tab_];;
 
 let _HexDigit_ = disj _digit_ _xdigit_;;
 
 let _HexChar_ = 
   let catened = caten _x_ (plus _HexDigit_) in
   pack catened (fun(l, p) -> l :: p);;
 
 let test = 
   disj (_makeCompat_ _x_) _tab_;;
 
 let _Char_ = 
   let _visSimpleCharFixed_ = pack _visSimpleChar_(fun (c) -> [c]) in
   let main = disj_list [_namedChar_ ; _HexChar_; _visSimpleCharFixed_ ] in
   let catened = caten_list [(_pairtolist_ _charPrefix_); main]
   in pack catened (fun (m) -> match m with
                            | [p; m] -> (match m with
                                       | 'x' :: a :: b -> Char (char_of_int (_hex_list_to_int_ (a :: b)) )
                                       | 'X' :: a :: b -> Char (char_of_int (_hex_list_to_int_ (a :: b)) )
                                       | [c] -> Char c
                                       | ['n';'e';'w';'l';'i';'n';'e'] -> Char(char_of_int 10)
                                       | ['n';'u';'l'] -> Char(char_of_int 0)
                                       | ['p';'a';'g';'e'] -> Char(char_of_int 12)
                                       | ['r';'e';'t';'u';'r';'n'] -> Char(char_of_int 13)
                                       | ['s';'p';'a';'c';'e'] -> Char(char_of_int 32)
                                       | ['t';'a';'b'] -> Char(char_of_int 9)
                                       | _ -> raise X_no_match)
                              | _ -> raise X_no_match);;
 
 (*char end*)
 (* three dots *)

 let const_dots =
  function 
  | '.'::'.'::'.'::s -> (Vector[Nil;Nil], '.'::'.'::'.'::s)
  | _ -> raise X_no_match;;

 let final_dots =
  word "...";;

 let _dots_ =
  function 
  | '.'::'.'::'.'::s -> (Vector[Nil;Nil],s)
  | _ -> raise X_no_match;;

 (* thre dots rnd *)
 (*list - last CFG*)

 let rec makelist l = match l with
  | [] -> Nil
  | a::b -> Pair (a, makelist b);;

 let rec makedotted l = match l with
  | (([],b),c) -> c
  | ((a::b,c),d) -> Pair (a, makedotted ((b, c), d));; 
  
 let rec list_to_vector p =
  match p with
  | Nil -> []
  | Pair (a,b) -> a :: list_to_vector b
  | _ -> raise X_no_match;;

 let rec _Sexpr_ s =   
  (make_enclosed deleteable ((make__space_d (disj_list [_Number_; _Char_; _String_; _Symbol_; _Boolean_ ;_List_;_DottedList_;_BracketList_;_BracketDottedList_;
                    _Vector_; _Quoted_; _QuasiQuoted_; _UnquoteAndSpliced_;_Unquote_ ; _SexpCom_; _LineComment_]))) deleteable)  s

  and _SexprForEnc_ s =   
  (make_enclosed deleteable (make__space_d (disj_list [ _Number_; _Char_; _String_; _Symbol_; _Boolean_ ;_EncList_;_EncDottedList_;_BracketEncList_;_BracketEncDottedList_;
                    _Vector_; _Quoted_; _QuasiQuoted_; _UnquoteAndSpliced_;_Unquote_ ; _SexpCom_; _LineComment_]))deleteable) s
  and _List_ s =
      (disj(make_enclosed _lparen_ (pack (star (make__space_d _SexprForEnc_)) makelist) _rparen_) 
      (make_enclosed _lparen_ (pack (star (make__space_d _SexprForEnc_)) makelist) final_dots))s

  and _EncList_ s =
      (disj(make_enclosed _lparen_ (pack (star (make__space_d _SexprForEnc_)) makelist) _rparen_) 
      (make_enclosed _lparen_ (pack (star (make__space_d _SexprForEnc_)) makelist) const_dots))s
      
  and _dotted_ s =
    (caten (caten (plus (make__space_d _SexprForEnc_)) (char '.')) _SexprForEnc_)  s
   
  and _DottedList_ s = 
     (disj(make_enclosed _lparen_ (pack _dotted_ makedotted) _rparen_) 
      (make_enclosed _lparen_ (pack _dotted_ makedotted) final_dots))s

   and _EncDottedList_ s = 
     (disj(make_enclosed _lparen_ (pack _dotted_ makedotted) _rparen_) 
      (make_enclosed _lparen_ (pack _dotted_ makedotted) const_dots))s
   
   and _BracketList_ s =
      (disj(make_enclosed _lbracket_ (pack (star (make__space_d _SexprForEnc_)) makelist) _rbracket_) 
      (make_enclosed _lbracket_ (pack (star (make__space_d _SexprForEnc_)) makelist) final_dots))s

   and _BracketEncList_ s =
      (disj(make_enclosed _lbracket_ (pack (star (make__space_d _Sexpr_)) makelist) _rbracket_) 
      (make_enclosed _lbracket_ (pack (star (make__space_d _SexprForEnc_)) makelist) const_dots))s

   and _BracketDottedList_ s = 
     (disj(make_enclosed _lbracket_ (pack _dotted_ makedotted) _rbracket_) 
      (make_enclosed _lbracket_ (pack _dotted_ makedotted) final_dots))s

   and _BracketEncDottedList_ s = 
     (disj(make_enclosed _lbracket_ (pack _dotted_ makedotted) _rbracket_) 
      (make_enclosed _lbracket_ (pack _dotted_ makedotted) const_dots))s

   and _Vector_ s =
     (pack(pack (caten _hash_ _List_ ) (fun (h,p)-> list_to_vector p))
          (fun (a) -> Vector a))s

  and _Quoted_ s =
     (pack (caten _quote_ _Sexpr_ ) (fun (l,r) -> Pair(Symbol("quote"), Pair(r, Nil)))) s
   
   and _QuasiQuoted_ s =
     (pack (caten _quasi_ _Sexpr_ ) (fun (l,r) -> Pair(Symbol("quasiquote"), Pair(r, Nil)))) s
   
   and _UnquoteAndSpliced_ s =
     (pack (caten (caten _comma_ _at_) _Sexpr_) (fun ((a,b),c)-> Pair(Symbol("unquote-splicing"), Pair(c, Nil)))) s
   
   and _Unquote_ s =
     (pack (caten _comma_ _Sexpr_ ) (fun (l,r) -> Pair(Symbol("unquote"), Pair(r, Nil)))) s

   and deleteable s= 
    (star (disj_list [_LineComment_; pack (const (fun a-> a <= char_of_int ( 32 ))) (fun _ -> Vector[Nil ; Nil]); _SexpCom_])) s
      
   and _SexpCom_ s=
      (pack (caten (caten _hash_ _semi_) _Sexpr_) (fun ((h,s),x)-> Vector[Nil;Nil]))s;;

 (*list end*)

 
 
let read_sexpr string = 
  let (e, s) = (_Sexpr_ (string_to_list string)) in
  e;;
 
let read_sexprs string = 
   let (e, s) = ((star _Sexpr_) (string_to_list string)) in
  e;;
   
 end;; (* struct Reader *)
 