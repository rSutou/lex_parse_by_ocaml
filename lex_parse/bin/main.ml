
(* open Ll_parser *)
module LLLang =
  struct
    type name = string
    (* 構文が持つ値の型 *)
    type literal =
    | LInt of int 
    | LBool of bool 
    type binOp =
    | OpAdd | OpSub | OpMul | OpDiv 
    | OpEq | OpLt 
    type expr =
    | ELiteral of literal
    | EBin of binOp * expr * expr 
    | EIf of expr * expr * expr
    | EVar of string
    | ELet of string * expr * expr
    type command =
    | CExp of expr
    | CLet of string * expr

    type value =
    | VInt of int
    | VBool of bool

    type env = (string * value) list

    exception Eval_error of string

    let rec eval : env -> expr -> value = fun en -> function
      | ELiteral (LInt n) -> VInt n
      | ELiteral (LBool b) -> VBool b
      | EBin (OpAdd,e1,e2)
        -> (match (eval en e1,eval en e2) with
            | (VInt n1, VInt n2) -> VInt (n1+n2)
            | _ -> raise (Eval_error "OpAdd defined type int*int->int"))
      | EBin (OpSub,e1,e2)
        -> (match (eval en e1,eval en e2) with
            | (VInt n1, VInt n2) -> VInt (n1-n2)
            | _ -> raise (Eval_error "OpSub defined type int*int->int"))
      | EBin (OpMul,e1,e2)
        -> (match (eval en e1,eval en e2) with
            | (VInt n1, VInt n2) -> VInt (n1*n2)
            | _ -> raise (Eval_error "OpMul defined type int*int->int"))
      | EBin (OpDiv,e1,e2)
        -> (match (eval en e1,eval en e2) with
            | (VInt n1, VInt n2) -> VInt (n1/n2)
            | _ -> raise (Eval_error "OpDiv defined type int*int->int"))
      | EBin (OpEq,e1,e2)
        -> (match (eval en e1,eval en e2) with
            | (VInt n1, VInt n2) -> VBool (n1=n2)
            | (VBool b1, VBool b2) -> VBool (b1=b2)
            | _ -> raise (Eval_error "OpEq arguments must be same type"))
      | EBin (OpLt,e1,e2) 
        -> (match (eval en e1,eval en e2) with
            | (VInt n1, VInt n2) -> VBool (n1<n2)
            | _ -> raise (Eval_error "OpLt defined type int*int->bool"))
      | EIf (e1,e2,e3) 
        -> (match eval en e1 with
            | VBool true -> eval en e2
            | VBool false -> eval en e3
            | _ -> raise (Eval_error "type error on if formula"))
      | EVar n -> (try List.assoc n en with Not_found -> raise (Eval_error "unbound value"))
      | ELet (n,e1,e2) -> eval ((n,eval en e1)::en) e2    
    let print_value :value -> unit = function
      | VBool b -> b |> string_of_bool |> print_string
      | VInt n -> n |> print_int
    
    let eval_command (en:env) (c:command) :value * env =
      match c with
      | CExp e -> (eval en e, en)
      | CLet (n,e) -> (let v = eval en e in (v,(n,v)::en))
    
    let rec eval_commands (en:env) (cl:command list) :(value list * env) =
      match cl with 
      | [] -> ([], en)
      | c::t -> 
          let (v,en') = eval_command en c in
          let (tvl,en'') = eval_commands en' t in
          (v::tvl,en'')

    (* ここからlexer/parser用 *)
    open Str
    type token = 
    | INT of int
    | TRUE
    | FALSE
    | PLUS
    | MINUS
    | TIMES
    | DIV
    | EQUAL
    | LESS
    | IF
    | THEN
    | ELSE
    | LET
    | IN
    | SEMISEMI
    | LPAREN | RPAREN
    | IDENT of string
    | EOF

    let eof = EOF

    let lexing_rule: (regexp * (string -> token option)) list =
      [
        (regexp "\\( \\|\t\\|\r\\|\n\\)+", fun _ -> None);
        (regexp {|[0-9]+|}, fun s -> Some (INT (int_of_string s)));
        (regexp {|true|}, fun _ -> Some TRUE);
        (regexp {|false|}, fun _ -> Some FALSE);
        (regexp {|\+|}, fun _ -> Some PLUS);
        (regexp {|-|}, fun _ -> Some MINUS);
        (regexp {|\*|}, fun _ -> Some TIMES);
        (regexp {|/|}, fun _ -> Some DIV);
        (regexp {|=|}, fun _ -> Some EQUAL);
        (regexp {|<|}, fun _ -> Some LESS);
        (regexp {|if|}, fun _ -> Some IF);
        (regexp {|then|}, fun _ -> Some THEN);
        (regexp {|else|}, fun _ -> Some ELSE);
        (regexp {|let|}, fun _ -> Some LET);
        (regexp {|in|}, fun _ -> Some IN);
        (regexp {|;;|}, fun _ -> Some SEMISEMI);
        (regexp {|(|}, fun _ -> Some LPAREN);
        (regexp {|)|}, fun _ -> Some RPAREN);
        (regexp {|\([a-z]\|_\)\([a-z]\|[A-Z]\|_\)*|}, fun s -> Some (IDENT s))]

    
    type parse_mark = 
    | Start of command list option
    | Commands of command list option
    | Csh of command option
    | Cst of command list option
    | Command of command option
    | Clh of (name*expr) option
    | Clt of expr option option
    | Expr of expr option
    | Enl of expr option
    | Logic of expr option
    | Lt of (binOp*expr) list option
    | Arith of expr option
    | At of (binOp*expr) list option
    | Term of expr option
    | Tt of (binOp*expr) list option
    | Atom of expr option

    type mark = 
    | Mark of parse_mark
    | Token of token

    let start_mark = Mark (Start None)

    let token_match: token -> token -> bool = fun t1 t2 ->
      match t1,t2 with
      | INT _, INT _ | IDENT _, IDENT _ -> true
      | _ -> t1 = t2

    let parse_mark_match = fun pm1 pm2 -> match (pm1,pm2) with
    | (Start _, Start _)
    | (Commands _, Commands _ )
    | (Csh _, Csh _) | (Cst _, Cst _)
    | (Command _ , Command _)
    | (Clh _, Clh _) |( Clt _, Clt _)
    | (Expr _ , Expr _)
    | (Enl _, Enl _)
    | (Logic _, Logic _)
    | (Lt _, Lt _ )| (At _, At _) | (Tt _, Tt _)
    | (Arith _,Arith _ )
    | (Term _,Term _ )
    | (Atom _ ,Atom _) -> true 
    | _ -> false

    let mark_match = fun m1 m2 -> match m1,m2 with
    | Token t1,Token t2 -> token_match t1 t2
    | Mark pm1,Mark pm2 -> parse_mark_match pm1 pm2
    | _ -> false

    let string_of_token t = match t with
    | INT n -> "num:" ^ string_of_int n
    | TRUE -> "true"
    | FALSE -> "false"
    | PLUS -> "plus"
    | MINUS-> "minus"
    | TIMES-> "times"
    | DIV-> "div"
    | EQUAL-> "equal"
    | LESS-> "less"
    | IF-> "if"
    | THEN-> "then"
    | ELSE-> "else"
    | LET-> "let"
    | IN-> "in"
    | SEMISEMI-> "semisemi"
    | LPAREN -> "Lparen"
    | RPAREN -> "Rparen"
    | IDENT s-> "IDENT:" ^ s
    | EOF-> "eof"

    let string_of_parse_mark pm = match pm with
    | Start _ -> "start"
    | Commands _ -> "commands"
    | Csh _ -> "commandshead"
    | Cst _ -> "comandstail"
    | Command _ -> "command"
    | Clh _ -> "commandlethead"
    | Clt _ -> "commandlettail"
    | Expr _ -> "expr"
    | Enl _ -> "exprnotlet"
    | Logic _ -> "logical"
    | Lt _ -> "logicaltail"
    | Arith _ -> "arith"
    | At _ -> "arithtail"
    | Term _ -> "term"
    | Tt _ -> "termtail"
    | Atom _ -> "atom"

    let string_of_mark = function
    | Mark pm -> string_of_parse_mark pm
    | Token t -> string_of_token t


    exception Not_match

    type parse_rule = parse_mark * mark list * (mark list -> mark)
    type parse_list = parse_rule list

    
    let parse:parse_list =
    [
      (Start None, 
      [Mark (Commands None); Token EOF], 
      (function 
      | [Mark Commands cs ;Token EOF] -> Mark (Start cs) 
      |_-> raise Not_match));
      (Commands None, 
      [Mark (Csh None); Mark (Cst None)], 
      (function 
      | [Mark Csh Some c ;Mark Cst Some cs] -> Mark (Commands (Some (c::cs))) 
      |_-> raise Not_match));
      (Csh None, 
      [Mark (Command None); Token SEMISEMI], 
      (function 
      | [Mark Command c ;Token SEMISEMI] -> Mark (Csh c) 
      |_-> raise Not_match));
      (Cst None, 
      [Mark (Commands None)], 
      (function 
      | [Mark Commands cs] -> Mark (Cst cs) 
      |_-> raise Not_match));
      (Cst None, 
      [], 
      (function 
      | [] -> Mark (Cst (Some [])) 
      |_-> raise Not_match));
      (Command None, 
      [Mark (Enl None)], 
      (function 
      | [Mark Enl Some e] -> Mark (Command (Some (CExp e))) 
      |_-> raise Not_match));
      (Command None, 
      [Mark (Clh None); Mark (Clt None)], 
      (function 
      | [Mark Clh Some (n,e); Mark Clt Some ebodyop] 
        -> (match ebodyop with 
          | Some ebody -> Mark (Command (Some (CExp (ELet (n,e,ebody)))))
          | None -> Mark (Command (Some (CLet (n,e)))) )
      |_-> raise Not_match));
      (Clh None, 
      [Token LET; Token (IDENT ""); Token EQUAL; Mark (Expr None)], 
      (function 
      | [Token LET; Token IDENT n; Token EQUAL; Mark Expr Some e] -> Mark (Clh (Some (n,e))) 
      |_-> raise Not_match));
      (Clt None,
      [Token IN; Mark (Expr None)], 
      (function 
      | [Token IN; Mark Expr Some e] -> Mark (Clt (Some (Some e))) 
      |_-> raise Not_match));
      (Clt None, 
      [], 
      (function 
      | [] -> Mark (Clt (Some None)) 
      |_-> raise Not_match));
      (Expr None, 
      [Mark (Enl None)], 
      (function 
      | [Mark Enl Some e] -> Mark (Expr (Some e)) 
      |_-> raise Not_match));
      (Expr None,
      [Token LET; Token (IDENT ""); Token EQUAL; Mark (Expr None); Token IN; Mark (Expr None)], 
      (function 
      | [Token LET; Token (IDENT n); Token EQUAL; Mark Expr Some e1; Token IN; Mark Expr Some ebody] 
        -> Mark (Expr (Some (ELet (n,e1,ebody)))) 
      |_-> raise Not_match));
      (Enl None,
      [Mark (Logic None)],
      (function 
      | [Mark Logic e] -> Mark (Enl e) 
      |_-> raise Not_match));
      (Enl None, 
      [Token IF; Mark (Expr None); Token THEN; Mark (Expr None); Token ELSE; Mark (Expr None)], 
      (function 
      | [Token IF; Mark Expr Some e1; Token THEN; Mark Expr Some e2; Token ELSE; Mark Expr Some e3] 
        -> Mark (Enl (Some (EIf (e1,e2,e3)))) 
      |_-> raise Not_match));
      (Logic None,
      [Mark (Arith None); Mark (Lt None)],
      (function 
      | [Mark Arith Some e1; Mark Lt Some bel] 
        -> Mark (Logic (Some (List.fold_left (fun e1' (bin,e2') -> EBin (bin,e1',e2')) e1 bel)) ) 
      |_-> raise Not_match));
      (Lt None, 
      [Token EQUAL; Mark (Arith None); Mark (Lt None)], 
      (function 
      | [Token EQUAL; Mark Arith Some e1; Mark Lt Some bel] -> Mark (Lt (Some((OpEq,e1)::bel))) 
      |_-> raise Not_match));
      (Lt None, 
      [Token LESS; Mark (Arith None); Mark (Lt None)], 
      (function 
      | [Token LESS; Mark Arith Some e1; Mark Lt Some bel] -> Mark (Lt (Some ((OpLt,e1)::bel))) 
      |_-> raise Not_match));
      (Lt None, 
      [], 
      (function 
      | [] -> Mark (Lt (Some [])) 
      |_-> raise Not_match));
      (Arith None, 
      [Mark (Term None); Mark (At None)], 
      (function 
      | [Mark Term Some e1; Mark At Some bel] 
        -> Mark (Arith (Some (List.fold_left (fun e1' (bin,e2') -> EBin (bin,e1',e2')) e1 bel)) ) 
      |_-> raise Not_match));
      (At None, 
      [Token PLUS; Mark (Term None); Mark (At None)], 
      (function 
      | [Token PLUS; Mark Term Some e1; Mark At Some bel] -> Mark (At (Some ((OpAdd,e1)::bel))) 
      |_-> raise Not_match));
      (At None, 
      [Token MINUS; Mark (Term None); Mark (At None)], 
      (function 
      | [Token MINUS; Mark Term Some e1; Mark At Some bel] -> Mark (At (Some ((OpSub,e1)::bel))) 
      |_-> raise Not_match));
      (At None, 
      [], 
      (function 
      | [] -> Mark (At (Some [])) 
      |_-> raise Not_match));
      (Term None, 
      [Mark (Atom None); Mark (Tt None)], 
      (function 
      | [Mark Atom Some e1; Mark Tt Some bel] 
        -> Mark (Term (Some (List.fold_left (fun e1' (bin,e2') -> EBin (bin,e1',e2')) e1 bel)) ) 
      |_-> raise Not_match));
      (Tt None, 
      [Token TIMES; Mark (Atom None); Mark (Tt None)], 
      (function 
      | [Token TIMES; Mark Atom Some e1; Mark Tt Some bel] -> Mark (Tt (Some ((OpMul,e1)::bel))) 
      |_-> raise Not_match));
      (Tt None, 
      [Token DIV; Mark (Atom None); Mark (Tt None)], 
      (function 
      | [Token DIV; Mark Atom Some e1; Mark Tt Some bel] -> Mark (Tt (Some ((OpDiv,e1)::bel))) 
      |_-> raise Not_match));
      (Tt None, 
      [], 
      (function 
      | [] -> Mark (Tt (Some [])) 
      |_-> raise Not_match));
      (Atom None, 
      [Token (INT 0)], 
      (function 
      | [Token INT n] -> Mark (Atom (Some (ELiteral (LInt n)))) 
      |_-> raise Not_match));
      (Atom None, 
      [Token TRUE], 
      (function 
      | [Token TRUE] -> Mark (Atom (Some (ELiteral (LBool true)))) 
      |_-> raise Not_match));
      (Atom None, 
      [Token FALSE], 
      (function 
      | [Token FALSE] -> Mark (Atom (Some (ELiteral (LBool false)))) 
      |_-> raise Not_match));
      (Atom None, 
      [Token (IDENT "")], 
      (function 
      | [Token IDENT s] -> Mark (Atom (Some (EVar s))) 
      |_-> raise Not_match));
      (Atom None,
      [Token LPAREN; Mark (Expr None); Token RPAREN],
      (function 
      | [Token LPAREN; Mark Expr Some e; Token RPAREN] -> Mark (Atom (Some e)) 
      |_-> raise Not_match)) 
    ]
  

  end

open LLLang
module LL0Parser' = Ll_parser.LLParser(LLLang);;

let _ = 
  LL0Parser'.parse_from_string {q|
1 - 1 - 1;;
3 * 2 / 3;;
1 + 2 * 2;;
1 + 1 < 1 + 1;;
if true then 1 else 2 + 1;;
if if true then false else false then
    if true then true else true
  else
    if true then false else false;;
let x = true in x;;
let x = let x = true in false in x;;
let x = true in
let x = false in
x;;
let x = true;;
let x = false;;
x;;
let x = true;;
let x = false in x;;
x;;
|q}
  |> (fun x -> match x with
      | Mark Start Some cs -> eval_commands [] cs |> fst |> List.iter (fun v -> print_value v;print_newline ())
      | _ -> raise Not_match)

module LL1Parser' = Ll_parser.LL1Parser(LLLang);;

print_endline (LL1Parser'.string_of_nullable ());
print_endline (LL1Parser'.string_of_first ());
print_endline (LL1Parser'.string_of_follow ());
print_endline (LL1Parser'.string_of_director ());
print_endline (LL1Parser'.string_of_parse_table ());;

let _ = 
  LL1Parser'.parse_from_string {q|
1 - 1 - 1;;
3 * 2 / 3;;
1 + 2 * 2;;
1 + 1 < 1 + 1;;
if true then 1 else 2 + 1;;
if if true then false else false then
    if true then true else true
  else
    if true then false else false;;
let x = true in x;;
let x = let x = true in false in x;;
let x = true in
let x = false in
x;;
let x = true;;
let x = false;;
x;;
let x = true;;
let x = false in x;;
x;;
|q}
  |> (fun x -> match x with
      | Mark Start Some cs -> eval_commands [] cs |> fst |> List.iter (fun v -> print_value v;print_newline ())
      | _ -> raise Not_match)




module Lang4 =
  struct
    type name = string
    type literal =
    | LInt of int
    | LBool of bool
    and binOp =
    | OpAdd | OpSub | OpMul | OpDiv
    | OpEq | OpLt
    | OpAnd | OpOr
    and expr =
    | ELiteral of literal
    | EBin of binOp * expr * expr
    | EIf of expr * expr * expr
    | ELet of name * expr * expr
    | EVar of name
    and command =
    | CExp of expr
    | CLet of name * expr

    type value =
    | VInt of int
    | VBool of bool
      
    type env = (string * value) list

    exception Eval_error of string

    let rec eval : env -> expr -> value = fun en -> function
      | ELiteral (LInt n) -> VInt n
      | ELiteral (LBool b) -> VBool b
      | EBin (OpAdd,e1,e2)
        -> (match (eval en e1,eval en e2) with
            | (VInt n1, VInt n2) -> VInt (n1+n2)
            | _ -> raise (Eval_error "OpAdd defined type int*int->int"))
      | EBin (OpSub,e1,e2)
        -> (match (eval en e1,eval en e2) with
            | (VInt n1, VInt n2) -> VInt (n1-n2)
            | _ -> raise (Eval_error "OpSub defined type int*int->int"))
      | EBin (OpMul,e1,e2)
        -> (match (eval en e1,eval en e2) with
            | (VInt n1, VInt n2) -> VInt (n1*n2)
            | _ -> raise (Eval_error "OpMul defined type int*int->int"))
      | EBin (OpDiv,e1,e2)
        -> (match (eval en e1,eval en e2) with
            | (VInt n1, VInt n2) -> VInt (n1/n2)
            | _ -> raise (Eval_error "OpDiv defined type int*int->int"))
      | EBin (OpEq,e1,e2)
        -> (match (eval en e1,eval en e2) with
            | (VInt n1, VInt n2) -> VBool (n1=n2)
            | (VBool b1, VBool b2) -> VBool (b1=b2)
            | _ -> raise (Eval_error "OpEq arguments must be same type"))
      | EBin (OpLt,e1,e2) 
        -> (match (eval en e1,eval en e2) with
            | (VInt n1, VInt n2) -> VBool (n1<n2)
            | _ -> raise (Eval_error "OpLt defined type int*int->bool"))
      | EBin (OpAnd,e1,e2) 
        -> (match (eval en e1,eval en e2) with
            | (VBool b1, VBool b2) -> VBool (b1 && b2)
            | _ -> raise (Eval_error "OpAnd defined type bool*bool->bool"))
      | EBin (OpOr,e1,e2) 
        -> (match (eval en e1,eval en e2) with
            | (VBool b1, VBool b2) -> VBool (b1 || b2)
            | _ -> raise (Eval_error "OpOr defined type bool*bool->bool"))
      | EIf (e1,e2,e3) 
        -> (match eval en e1 with
            | VBool true -> eval en e2
            | VBool false -> eval en e3
            | _ -> raise (Eval_error "type error on if formula"))
      | EVar n -> (try List.assoc n en with Not_found -> raise (Eval_error "unbound value"))
      | ELet (n,e1,e2) -> eval ((n,eval en e1)::en) e2    
    let print_value :value -> unit = function
      | VBool b -> b |> string_of_bool |> print_string
      | VInt n -> n |> print_int
    
    let eval_command (en:env) (c:command) :value * env =
      match c with
      | CExp e -> (eval en e, en)
      | CLet (n,e) -> (let v = eval en e in (v,(n,v)::en))
    
    let rec eval_commands (en:env) (cl:command list) :(value list * env) =
      match cl with 
      | [] -> ([], en)
      | c::t -> 
          let (v,en') = eval_command en c in
          let (tvl,en'') = eval_commands en' t in
          (v::tvl,en'')
    
    open Str
    type token = 
    | INT of int
    | TRUE
    | FALSE
    | PLUS
    | MINUS
    | TIMES
    | DIV
    | AND
    | OR
    | EQUAL
    | LESS
    | IF
    | THEN
    | ELSE
    | LET
    | IN
    | SEMISEMI
    | LPAREN | RPAREN
    | IDENT of string
    | EOF

    let string_of_token t = match t with
    | INT n -> "num:" ^ string_of_int n
    | TRUE -> "true"
    | FALSE -> "false"
    | PLUS -> "plus"
    | MINUS-> "minus"
    | TIMES-> "times"
    | DIV-> "div"
    | AND-> "and"
    | OR-> "or"
    | EQUAL-> "equal"
    | LESS-> "less"
    | IF-> "if"
    | THEN-> "then"
    | ELSE-> "else"
    | LET-> "let"
    | IN-> "in"
    | SEMISEMI-> "semisemi"
    | LPAREN -> "LParen"
    | RPAREN -> "RParen"
    | IDENT s-> "IDENT:" ^ s
    | EOF-> "eof"

    let eof = EOF

    let lexing_rule: (regexp * (string -> token option)) list =
      [
        (regexp "\\( \\|\t\\|\r\\|\n\\)+", fun _ -> None);
        (regexp {|[0-9]+|}, fun s -> Some (INT (int_of_string s)));
        (regexp {|true|}, fun _ -> Some TRUE);
        (regexp {|false|}, fun _ -> Some FALSE);
        (regexp {|\+|}, fun _ -> Some PLUS);
        (regexp {|-|}, fun _ -> Some MINUS);
        (regexp {|\*|}, fun _ -> Some TIMES);
        (regexp {|/|}, fun _ -> Some DIV);
        (regexp {|&|}, fun _ -> Some AND);
        (regexp {|||}, fun _ -> Some OR);
        (regexp {|=|}, fun _ -> Some EQUAL);
        (regexp {|<|}, fun _ -> Some LESS);
        (regexp {|if|}, fun _ -> Some IF);
        (regexp {|then|}, fun _ -> Some THEN);
        (regexp {|else|}, fun _ -> Some ELSE);
        (regexp {|let|}, fun _ -> Some LET);
        (regexp {|in|}, fun _ -> Some IN);
        (regexp {|;;|}, fun _ -> Some SEMISEMI);
        (regexp {|(|}, fun _ -> Some LPAREN);
        (regexp {|)|}, fun _ -> Some RPAREN);
        (regexp {|\([a-z]\|_\)\([a-z]\|[A-Z]\|_\)*|}, fun s -> Some (IDENT s))]

    type parse_mark = 
    | Start of command list option
    | Commands of command list option
    | Command of command option
    | Expr of expr option
    | Logic of expr option
    | Compare of expr option
    | Arith of expr option
    | Term of expr option
    | Atom of expr option

    let string_of_parse_mark pm = match pm with
    | Start _ -> "start"
    | Commands _ -> "commands"
    | Command _ -> "command"
    | Expr _ -> "expr"
    | Logic _ -> "logical"
    | Compare _ -> "comp"
    | Arith _ -> "arith"
    | Term _ -> "term"
    | Atom _ -> "atom"


    (* 解析後の値の格納に使う *)
    type mark = 
    | Mark of parse_mark
    | Token of token

    let string_of_mark = function
    | Mark pm -> string_of_parse_mark pm
    | Token t -> string_of_token t

    exception Not_match

    let token_match: token -> token -> bool = fun t1 t2 ->
      match t1,t2 with
      | INT _, INT _ | IDENT _, IDENT _ -> true
      | _ -> t1 = t2

    let parse_mark_match = fun pm1 pm2 ->match (pm1,pm2) with
      | Start _, Start _
      | Commands _, Commands _ 
      | Command _ , Command _
      | Expr _ , Expr _
      | Logic _, Logic _
      | Compare _, Compare _
      | Arith _,Arith _ 
      | Term _,Term _ 
      | Atom _ ,Atom _-> true 
      | _ -> false

    
    let mark_match = fun rm1 rm2 ->
      match (rm1,rm2) with
      | Token t1,Token t2 -> token_match t1 t2
      | Mark pm1,Mark pm2 -> parse_mark_match pm1 pm2
      | _ -> false
    

    let start_mark = Mark (Start None)

    type parse_rule = parse_mark * mark list * (mark list -> mark)
    type parse_list = parse_rule list

    
    let parse:parse_list =
    [
      (Start None, 
      [Mark (Commands None); Token EOF], 
      (function 
      | [Mark Commands cs ;Token EOF] -> Mark (Start cs) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Start None)); raise Not_match));
      
      (Commands None, 
      [Mark (Command None); Token SEMISEMI; Mark (Commands None)], 
      (function 
      | [Mark Command Some c ;Token SEMISEMI; Mark Commands Some cs] -> Mark (Commands (Some (c::cs))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Commands None)); raise Not_match));
      (Commands None, 
      [Mark (Command None); Token SEMISEMI], 
      (function 
      | [Mark Command Some c ;Token SEMISEMI] -> Mark (Commands (Some [c])) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Commands None)); raise Not_match));

      (Command None, 
      [Mark (Expr None)], 
      (function 
      | [Mark Expr Some e] -> Mark (Command (Some (CExp e))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Command None)); raise Not_match));
      (Command None, 
      [Token LET; Token (IDENT ""); Token EQUAL; Mark (Expr None)], 
      (function 
      | [Token LET; Token IDENT n; Token EQUAL; Mark Expr Some e] -> Mark (Command (Some (CLet (n,e)))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Command None)); raise Not_match));
      
      (Expr None, 
      [Mark (Logic None)], 
      (function 
      | [Mark Logic Some e] -> Mark (Expr (Some e)) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Expr None)); raise Not_match));
      (Expr None, 
      [Token IF; Mark (Expr None); Token THEN; Mark (Expr None); Token ELSE; Mark (Expr None)], 
      (function 
      | [Token IF; Mark Expr Some e1; Token THEN; Mark Expr Some e2; Token ELSE; Mark Expr Some e3] 
        -> Mark (Expr (Some (EIf (e1,e2,e3)))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Expr None)); raise Not_match));
      (Expr None, 
      [Token LET; Token (IDENT ""); Token EQUAL; Mark (Expr None); Token IN; Mark (Expr None)], 
      (function 
      | [Token LET; Token IDENT n; Token EQUAL; Mark Expr Some e; Token IN; Mark Expr Some ebody] 
        -> Mark (Expr (Some (ELet (n,e,ebody)))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Expr None)); raise Not_match));

      (Logic None, 
      [Mark (Compare None)], 
      (function 
      | [Mark Compare Some e] -> Mark (Logic (Some e)) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Logic None)); raise Not_match));
      (Logic None, 
      [Mark (Logic None) ; Token AND; Mark (Compare None)], 
      (function 
      | [Mark Logic Some e1 ; Token AND; Mark Compare Some e2] -> Mark (Logic (Some (EBin (OpAnd,e1,e2)))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Logic None)); raise Not_match));
      (Logic None, 
      [Mark (Logic None) ; Token OR; Mark (Compare None)], 
      (function 
      | [Mark Logic Some e1 ; Token OR; Mark Compare Some e2] -> Mark (Logic (Some (EBin (OpOr,e1,e2)))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Logic None)); raise Not_match));

      (Compare None, 
      [Mark (Arith None)], 
      (function 
      | [Mark Arith Some e] -> Mark (Compare (Some e)) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Compare None)); raise Not_match));
      (Compare None, 
      [Mark (Arith None); Token EQUAL; Mark (Arith None)], 
      (function 
      | [Mark Arith Some e1; Token EQUAL; Mark Arith Some e2] -> Mark (Compare (Some (EBin (OpEq,e1,e2)))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Compare None)); raise Not_match));
      (Compare None, 
      [Mark (Arith None); Token LESS; Mark (Arith None)], 
      (function 
      | [Mark Arith Some e1; Token LESS; Mark Arith Some e2] -> Mark (Compare (Some (EBin (OpLt,e1,e2)))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Compare None)); raise Not_match));
      
      (Arith None, 
      [Mark (Term None)], 
      (function 
      | [Mark Term Some e] -> Mark (Arith (Some e)) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Arith None)); raise Not_match));
      (Arith None, 
      [Mark (Arith None); Token PLUS; Mark (Term None)], 
      (function 
      | [Mark Arith Some e1; Token PLUS; Mark Term Some e2] -> Mark (Arith (Some (EBin (OpAdd,e1,e2)))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Arith None)); raise Not_match));
      (Arith None, 
      [Mark (Arith None); Token MINUS; Mark (Term None)], 
      (function 
      | [Mark Arith Some e1; Token MINUS; Mark Term Some e2] -> Mark (Arith (Some (EBin (OpSub,e1,e2)))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Arith None)); raise Not_match));

      (Term None, 
      [Mark (Atom None)], 
      (function 
      | [Mark Atom Some e] -> Mark (Term (Some e)) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Term None)); raise Not_match));
      (Term None, 
      [Mark (Term None); Token TIMES; Mark (Atom None)], 
      (function 
      | [Mark Term Some e1; Token TIMES; Mark Atom Some e2] -> Mark (Term (Some (EBin (OpMul,e1,e2)))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Term None)); raise Not_match));
      (Term None, 
      [Mark (Term None); Token DIV; Mark (Atom None)], 
      (function 
      | [Mark Term Some e1; Token DIV; Mark Atom Some e2] -> Mark (Term (Some (EBin (OpDiv,e1,e2)))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Term None)); raise Not_match));

      (Atom None, 
      [Token (INT 0)], 
      (function 
      | [Token INT n] -> Mark (Atom (Some (ELiteral (LInt n)))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Atom None)); raise Not_match));
      (Atom None, 
      [Token TRUE], 
      (function 
      | [Token TRUE] -> Mark (Atom (Some (ELiteral (LBool true)))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Atom None)); raise Not_match));
      (Atom None, 
      [Token FALSE], 
      (function 
      | [Token FALSE] -> Mark (Atom (Some (ELiteral (LBool false)))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Atom None)); raise Not_match));
      (Atom None, 
      [Token (IDENT "")], 
      (function 
      | [Token IDENT n] -> Mark (Atom (Some (EVar n))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Atom None)); raise Not_match));
      (Atom None, 
      [Token LPAREN; Mark (Expr None); Token RPAREN], 
      (function 
      | [Token LPAREN; Mark Expr Some e; Token RPAREN] -> Mark (Atom (Some e)) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Atom None)); raise Not_match));
    ]

  end


      
open Lang4
module SLR1Parser4 = Lr_parser.SLRParser(Lang4);;
SLR1Parser4.string_of_nullable () |> prerr_endline ;;
SLR1Parser4.string_of_first () |> prerr_endline ;;
SLR1Parser4.string_of_follow () |> prerr_endline ;;
SLR1Parser4.string_of_rules () |> prerr_endline ;;
SLR1Parser4.string_of_states () |> prerr_endline ;;

let _ = 
  SLR1Parser4.parse_from_string {q|
1 + 1 - 1;;
3 * 2 / 3;;
1 + 2 * 2;;
1 + 1 < 1 + 1;;
if true then 1 else 2 + 1;;
if if true then false else false then
    if true then true else true
  else
    if true then false else false;;
let x = true in x;;
let x = let x = true in false in x;;
let x = true in
let x = false in
x;;
let x = true;;
let x = false;;
x;;
let x = true;;
let x = false in x;;
x;;
|q}
  |> (fun x -> match x with
      | Mark Start (Some cs) -> eval_commands [] cs |> fst |> List.iter (fun v -> print_value v;print_newline ())
      | _ -> raise Not_match)



module Lang5 =
  struct
    type name = string
    and binOp =
    | OpAdd 
    | OpEq 
    and expr =
    | EBin of binOp * expr * expr
    | EVar of name

    
    let rec string_of_expr = function
    | EBin (OpAdd,e1,e2) -> "(" ^ string_of_expr e1 ^ " + " ^ string_of_expr e2 ^ ")"
    | EBin (OpEq,e1,e2) -> "(" ^ string_of_expr e1 ^ " == " ^ string_of_expr e2 ^ ")"
    | EVar n -> n
    
    
    
    open Str
    type token = 
    | PLUS
    | EQUAL
    | LPAREN | RPAREN
    | IDENT of string
    | EOF

    let string_of_token t = match t with
    | PLUS -> "plus"
    | EQUAL-> "equal"
    | LPAREN -> "LParen"
    | RPAREN -> "RParen"
    | IDENT s-> "IDENT:" ^ s
    | EOF-> "eof"

    let eof = EOF

    let lexing_rule: (regexp * (string -> token option)) list =
      [
        (regexp "\\( \\|\t\\|\r\\|\n\\)+", fun _ -> None);
        (regexp {|\+|}, fun _ -> Some PLUS);
        (regexp {|==|}, fun _ -> Some EQUAL);
        (regexp {|(|}, fun _ -> Some LPAREN);
        (regexp {|)|}, fun _ -> Some RPAREN);
        (regexp {|\([a-z]\|_\)\([a-z]\|[A-Z]\|_\)*|}, fun s -> Some (IDENT s))]

    type parse_mark = 
    | Start of expr option
    | Command of expr option
    | Expr of expr option
    | Term of expr option

    let string_of_parse_mark pm = match pm with
    | Start _ -> "start"
    | Command _ -> "command"
    | Expr _ -> "expr"
    | Term _ -> "term"


    (* 解析後の値の格納に使う *)
    type mark = 
    | Mark of parse_mark
    | Token of token

    let string_of_mark = function
    | Mark pm -> string_of_parse_mark pm
    | Token t -> string_of_token t

    exception Not_match

    let token_match: token -> token -> bool = fun t1 t2 ->
      match t1,t2 with
      | IDENT _, IDENT _ -> true
      | _ -> t1 = t2

    let parse_mark_match = fun pm1 pm2 ->match (pm1,pm2) with
      | Start _, Start _
      | Command _ , Command _
      | Expr _ , Expr _
      | Term _,Term _ -> true
      | _ -> false

    
    let mark_match = fun rm1 rm2 ->
      match (rm1,rm2) with
      | Token t1,Token t2 -> token_match t1 t2
      | Mark pm1,Mark pm2 -> parse_mark_match pm1 pm2
      | _ -> false
    

    let start_mark = Mark (Start None)

    type parse_rule = parse_mark * mark list * (mark list -> mark)
    type parse_list = parse_rule list

    
    let parse:parse_list =
    [
      (Start None, 
      [Mark (Command None); Token EOF], 
      (function 
      | [Mark Command e ;Token EOF] -> Mark (Start e) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Start None)); raise Not_match));

      (Command None, 
      [Mark (Expr None); Token EQUAL; Mark (Expr None)], 
      (function 
      | [Mark Expr Some e1; Token EQUAL; Mark Expr Some e2] -> Mark (Command (Some (EBin (OpEq,e1,e2)))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Command None)); raise Not_match));
      (Command None, 
      [Token (IDENT "")], 
      (function 
      | [Token IDENT n] -> Mark (Command (Some (EVar n))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Command None)); raise Not_match));
      
      (Expr None, 
      [Mark (Expr None); Token PLUS; Mark (Term None)], 
      (function 
      | [Mark Expr Some e1; Token PLUS; Mark Term Some e2] -> Mark (Expr (Some (EBin(OpAdd,e1,e2)))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Expr None)); raise Not_match));
      (Expr None, 
      [Mark (Term None)], 
      (function 
      | [Mark Term e2] -> Mark (Expr e2) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Expr None)); raise Not_match));


      (Term None, 
      [Token (IDENT "")], 
      (function 
      | [Token IDENT n] -> Mark (Term (Some (EVar n))) 
      |_-> print_endline ("error on " ^ string_of_parse_mark (Term None)); raise Not_match));
    ]

  end

      
open Lang5

(* module SLR1Parser5 = Lr_parser.SLRParser(Lang5);;
SLR1Parser5.string_of_nullable () |> prerr_endline ;;
SLR1Parser5.string_of_first () |> prerr_endline ;;
SLR1Parser5.string_of_follow () |> prerr_endline ;;
SLR1Parser5.string_of_rules () |> prerr_endline ;;
SLR1Parser5.string_of_states () |> prerr_endline ;; *)


module LR1Parser5 = Lr_parser.LR1Parser(Lang5);;
LR1Parser5.string_of_nullable () |> prerr_endline ;;
LR1Parser5.string_of_first () |> prerr_endline ;;
(* LR1Parser5.string_of_follow () |> prerr_endline ;; *)
LR1Parser5.string_of_rules () |> prerr_endline ;;
LR1Parser5.string_of_states () |> prerr_endline ;;

let _ = 
  LR1Parser5.parse_from_string {q|x == y + z |q}
  |> (fun x -> match x with
      | Mark Start (Some cs) ->  cs |> string_of_expr |> print_endline
      | _ -> raise Not_match)

      
      
module Lr1Parser6 = Lr_parser.LR1Parser(Lang);;
Lr1Parser6.string_of_nullable () |> prerr_endline ;;
Lr1Parser6.string_of_first () |> prerr_endline ;;
(* Lr1Parser6.string_of_follow () |> prerr_endline ;; *)
Lr1Parser6.string_of_rules () |> prerr_endline ;;
Lr1Parser6.string_of_states () |> prerr_endline ;;

let _ = 
  Lr1Parser6.parse_from_string {q|1 + 2 * 3 - 4 / 2 + 2 * (1 - 2)|q}
  |> (fun x -> match x with
      | Mark Start (Some cs) ->  cs |> Lang.eval |> string_of_int |> print_endline
      | _ -> raise Not_match)

