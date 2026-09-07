

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