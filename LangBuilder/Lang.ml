
type exp =
| BinOp of op * exp * exp
| Atom of int
and op =
| Add
| Mul
| Sub
| Div


let rec eval : exp -> int = function
| Atom n -> n
| BinOp (Add, e1,e2) -> eval e1 + eval e2
| BinOp (Mul, e1,e2) -> eval e1 * eval e2
| BinOp (Sub, e1,e2) -> eval e1 - eval e2
| BinOp (Div, e1,e2) -> eval e1 / eval e2

type token = 
| EOF
| RPAREN
| LPAREN
| DIV
| MINUS
| MUL
| PLUS
| NUM of int
let string_of_token t = match t with 
| EOF -> "EOF"
| RPAREN -> "RPAREN"
| LPAREN -> "LPAREN"
| DIV -> "DIV"
| MINUS -> "MINUS"
| MUL -> "MUL"
| PLUS -> "PLUS"
| NUM _ -> "NUM"
let eof = EOF
let lexing_rule = 
 [(Str.regexp "\\( \\|\t\\|\r\\|\n\\)+", fun _ -> None);
(Str.regexp "[0-9]+", fun s -> Some (NUM (int_of_string s)));
(Str.regexp ")", fun _ -> Some RPAREN);
(Str.regexp "(", fun _ -> Some LPAREN);
(Str.regexp "/", fun _ -> Some DIV);
(Str.regexp "-", fun _ -> Some MINUS);
(Str.regexp "\\*", fun _ -> Some MUL);
(Str.regexp "\\+", fun _ -> Some PLUS);
]
type parse_mark = 
 | Atomic of (exp) option 
| Term of (exp) option 
| Arith of (exp) option 
| Start of (exp) option 

let string_of_parse_mark m = match m with
| Atomic _ -> "Atomic"
| Term _ -> "Term"
| Arith _ -> "Arith"
| Start _ -> "Start"

type mark = Mark of parse_mark | Token of token 
let string_of_mark m = match m with | Mark m -> string_of_parse_mark m | Token t -> string_of_token t
exception Not_match
let token_match t1 t2 = match (t1, t2) with
| (NUM _,NUM _) -> true
| (_,_) -> t1 = t2 
let parse_mark_match m1 m2 = match (m1,m2) with 
| (Atomic _,Atomic _) -> true
| (Term _,Term _) -> true
| (Arith _,Arith _) -> true
| (Start _,Start _) -> true
| (_,_) -> m1 = m2 
let mark_match m1 m2 = match (m1, m2) with | (Mark m1, Mark m2) -> parse_mark_match m1 m2 | (Token t1, Token t2) -> token_match t1 t2 | (_,_) -> false
let start_mark = Mark (Start None)

    type parse_rule = parse_mark * mark list * (mark list -> mark)
    type parse_list = parse_rule list
    let parse = [
(Start None, [Mark (Arith None);Token EOF;],fun l -> match l with [Mark (Arith (Some _0));Token (EOF);] -> (Mark(Start(Some( _0)))) | _ -> raise Not_match);
(Arith None, [Mark (Arith None);Token MINUS;Mark (Term None);],fun l -> match l with [Mark (Arith (Some _0));Token (MINUS);Mark (Term (Some _2));] -> (Mark(Arith(Some( (BinOp (Sub, _0, _2)))))) | _ -> raise Not_match);
(Arith None, [Mark (Arith None);Token PLUS;Mark (Term None);],fun l -> match l with [Mark (Arith (Some _0));Token (PLUS);Mark (Term (Some _2));] -> (Mark(Arith(Some( (BinOp (Add, _0, _2)))))) | _ -> raise Not_match);
(Arith None, [Mark (Term None);],fun l -> match l with [Mark (Term (Some _0));] -> (Mark(Arith(Some( _0)))) | _ -> raise Not_match);
(Term  None, [Mark (Term None);Token DIV;Mark (Atomic None);],fun l -> match l with [Mark (Term (Some _0));Token (DIV);Mark (Atomic (Some _2));] -> (Mark(Term (Some( BinOp (Div, _0, _2))))) | _ -> raise Not_match);
(Term  None, [Mark (Term None);Token MUL;Mark (Atomic None);],fun l -> match l with [Mark (Term (Some _0));Token (MUL);Mark (Atomic (Some _2));] -> (Mark(Term (Some( BinOp (Mul, _0, _2))))) | _ -> raise Not_match);
(Term  None, [Mark (Atomic None);],fun l -> match l with [Mark (Atomic (Some _0));] -> (Mark(Term (Some( _0)))) | _ -> raise Not_match);
(Atomic  None, [Token LPAREN;Mark (Arith None);Token RPAREN;],fun l -> match l with [Token (LPAREN);Mark (Arith (Some _1));Token (RPAREN);] -> (Mark(Atomic (Some( _1)))) | _ -> raise Not_match);
(Atomic  None, [Token (NUM 0);],fun l -> match l with [Token (NUM _0);] -> (Mark(Atomic (Some( Atom (_0))))) | _ -> raise Not_match);
]
