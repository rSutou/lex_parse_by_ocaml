(* open Str *)
open Langs

module StringLexer(Lang:LANG_LEX) =
  struct
    exception Lexing_error
    
    let pop_option (s: string) : int * Lang.token option =
      List.fold_left 
      (fun ((n,_) as pre) (re, f) -> 
        if Str.string_partial_match re s 0
        then 
          let ms = Str.matched_string s in 
          let msl = String.length ms in
          (if msl > n then (msl, f ms) else pre)
        else pre)
      (0,None)
      Lang.lexing_rule
      |> 
      (fun ((n,_) as res) -> 
        if n <= 0 then raise Lexing_error
        else res)

    let rec pop (s: string) : int * Lang.token =
      if String.length s = 0 then (0,Lang.eof)
      else
        match pop_option s with
        | (n,Some t) -> (n,t)
        | (n,None) -> let (n',t) = pop (String.sub s n (String.length s - n)) in (n + n', t)

    let rec lex_from_string: string -> Lang.token list = fun s ->
      let (n,t) = pop s in
      if t = Lang.eof then [t] 
      else t:: (lex_from_string (String.sub s n (String.length s - n)))
  end

