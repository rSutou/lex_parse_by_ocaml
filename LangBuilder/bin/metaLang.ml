
type metaLangData =
{
  source : string
  
  ; tokens : (string * string option * string option) list
  
  ;eof : string
  
  ;lexing_rules : (string * string) list
  
  ;parse_marks : (string * string option) list
  ; start_mark : string
  
  ;parse_rules : (string * string list * string) list
}