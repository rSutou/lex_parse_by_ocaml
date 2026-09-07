open Str

module type LANG_LEX = 
  sig
    type token
    val eof: token
    val lexing_rule: (regexp * (string -> token option)) list
  end

module type LANG_PARSE = 
  sig
    include LANG_LEX

    type parse_mark
    type mark = 
    | Mark of parse_mark
    | Token of token
    val start_mark: mark
    
    val token_match: token -> token -> bool
    val parse_mark_match :parse_mark -> parse_mark -> bool
    val mark_match : mark -> mark -> bool 
    
    val string_of_token : token -> string
    val string_of_parse_mark : parse_mark -> string
    val string_of_mark : mark -> string
    
    type parse_rule = parse_mark * mark list * (mark list -> mark)
    type parse_list = parse_rule list
    val parse:parse_list

  end