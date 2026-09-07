open MetaLang

exception Result of metaLangData

let read_from_file (inch:in_channel) (filename:string) : metaLangData = 
  let result = { source = ""; tokens = []; lexing_rules = []; parse_marks = []; eof = ""; start_mark = ""; parse_rules = [] } in 
  let rec forward_line (inch: in_channel) (res:metaLangData) (source_mode:bool): metaLangData =
    let instr = try input_line inch with _ -> raise (Result res) in
    if source_mode 
    then
      match String.split_on_char ' ' instr with
      | h::t when h = "\\end" -> forward_line inch res false
      | _ -> forward_line inch {res with source = res.source ^ "\n" ^ instr} true
    else
      match String.split_on_char ' ' instr with
      | h::t when h = "\\source" -> forward_line inch res true
      | h::t when h = "\\token" 
        -> 
          begin 
            match t with
            | [] -> forward_line inch res source_mode
            | tname :: [] -> forward_line inch {res with tokens = (tname, None, None)::res.tokens} source_mode
            | tname :: _ :: tt 
            -> match String.split_on_char ':' (String.concat " " tt) with 
              | h::t -> forward_line inch {res with tokens = (tname, Some h, Some (String.concat ":" t))::res.tokens} source_mode
              | [] -> forward_line inch {res with tokens = (tname, None, None)::res.tokens} source_mode
          end
      | h::t when h = "\\eof"
        -> 
          begin 
            match t with
            | [] -> forward_line inch res source_mode
            | tname :: _ -> forward_line inch {res with eof = tname} source_mode
          end
      | h::t when h = "\\lex" 
        -> 
          begin 
            match String.split_on_char ',' (String.concat " " t) with
            | [] -> forward_line inch res source_mode
            | re :: [] -> forward_line inch {res with lexing_rules = (re, "fun _ -> None")::res.lexing_rules} source_mode
            | re :: tt -> forward_line inch {res with lexing_rules = (re, (String.concat "," tt))::res.lexing_rules} source_mode
          end
      | h::t when h = "\\mark" 
        -> 
          begin 
            match t with
            | [] -> forward_line inch res source_mode
            | mname :: [] -> forward_line inch {res with parse_marks = (mname, None)::res.parse_marks} source_mode
            | mname :: _ :: tt -> forward_line inch {res with parse_marks = (mname, Some (String.concat " " tt))::res.parse_marks} source_mode
          end
      | h::t when h = "\\start" 
        -> 
          begin 
            match t with
            | [] -> forward_line inch res source_mode
            | mname :: [] -> forward_line inch {res with start_mark = mname} source_mode
            | mname :: _ :: tt -> forward_line inch {res with start_mark = mname} source_mode
          end
      | h::t when h = "\\parse" 
        -> 
          begin 
            match String.split_on_char ':' (String.concat " " t) with
            | mname :: tlist :: pfuns -> forward_line inch {res with parse_rules = (mname, (String.split_on_char ' ' tlist), String.concat ":" pfuns)::res.parse_rules} source_mode
            | _ -> forward_line inch res source_mode
          end
      | _ -> forward_line inch res source_mode

  in
    try forward_line inch result false with
    Result mld -> mld
    

let build_from_data (data: metaLangData) : string =
  let result = data.source ^ "\n" in
  let token_area = 
    List.fold_left 
    (fun e p3 ->
      match p3 with
      | (tname, Some defaultval, Some argty) -> e ^ "| " ^ tname ^ " of " ^ argty ^ "\n" 
      | (tname, _, _) -> e ^ "| " ^ tname ^ "\n")
    "type token = \n"
    data.tokens 
    ^
    List.fold_left
    (fun e p3 ->
      match p3 with
      | (tname, Some defaultval, Some argty) -> e ^ "| " ^ tname ^ " _ -> \"" ^ tname ^ "\"\n" 
      | (tname, _, _) -> e ^ "| " ^ tname ^ " -> \"" ^ tname ^ "\"\n" )
    "let string_of_token t = match t with \n"
    data.tokens
  in
  let eof_area = "let eof = " ^ data.eof ^ "\n" in
  let lex_area = 
    List.fold_left 
    (fun e (re, funstr) -> 
      e ^ "(Str.regexp " ^ re ^ "," ^ funstr ^ ");\n"
      )
    "let lexing_rule = \n ["
    data.lexing_rules
    ^ "]\n"
  in
  let parse_mark_area =
    List.fold_left
    (fun e p2 -> match p2 with
    | (mname, Some t) -> e ^ "| " ^ mname ^ " of (" ^ t ^ ") option \n" 
    | (mname, None) -> e ^ "| " ^ mname ^ " of (unit) option \n" )
    "type parse_mark = \n "
    data.parse_marks
    ^ 
    "\n"
    ^
    List.fold_left
    (fun e p2 -> match p2 with
    | (mname, Some t) -> e ^ "| " ^ mname ^ " _ -> \"" ^ mname ^ "\"\n" 
    | (mname, None) -> e ^ "| " ^ mname ^ " -> \"" ^ mname ^ "\"\n" )
    "let string_of_parse_mark m = match m with\n"
    data.parse_marks
    ^ "\n"
  in
  let mark_area = 
    "type mark = Mark of parse_mark | Token of token \n"
    ^
    "let string_of_mark m = match m with | Mark m -> string_of_parse_mark m | Token t -> string_of_token t\n"
  in
  let except = "exception Not_match\n" in
  let match_area =
    List.fold_left 
    (fun e p3 -> match p3 with
    | (tname, _, Some argty) -> e ^ "| (" ^ tname ^" _," ^ tname ^ " _) -> true\n" 
    | (tname, _, _) -> e )
    "let token_match t1 t2 = match (t1, t2) with\n"
    data.tokens
    ^ "| (_,_) -> t1 = t2 \n"
    ^
    List.fold_left
    (fun e p2 -> match p2 with
    | (mname, Some t) -> e ^ "| (" ^ mname ^" _," ^ mname ^ " _) -> true\n"
    | (mname, None) -> e ^ "| (" ^ mname ^" _," ^ mname ^ " _) -> true\n" )
    "let parse_mark_match m1 m2 = match (m1,m2) with \n"
    data.parse_marks
    ^ "| (_,_) -> m1 = m2 \n"
    ^
    "let mark_match m1 m2 = match (m1, m2) with | (Mark m1, Mark m2) -> parse_mark_match m1 m2 | (Token t1, Token t2) -> token_match t1 t2 | (_,_) -> false\n"
  in
  let parse_area =
    "let start_mark = Mark (" ^ data.start_mark ^ " None)\n"
    ^
    {|
    type parse_rule = parse_mark * mark list * (mark list -> mark)
    type parse_list = parse_rule list
    |}
    ^
    "let parse = [\n"
    ^
    List.fold_left 
    (fun e p3 -> match p3 with 
      | (mname, mlist, tfun) ->
        let _ = List.length mlist in
        e ^ "(" ^ mname ^ " None, [" ^ 
        List.fold_left 
        (fun e mname -> 
          e ^ 
          (List.find_opt (fun (t, _, _) -> t = mname) data.tokens |> 
          fun pop -> match pop with 
            | Some v -> 
              begin 
                match v with 
                | (_,Some v,_) -> "Token (" ^ mname ^ " " ^ v ^")"
                | _ -> "Token " ^ mname
              end
            | None ->
              List.find_opt (fun (m,_) -> m = mname) data.parse_marks |>
              fun pop -> match pop with
                | Some (_,Some _) -> "Mark (" ^ mname ^ " None)"
                | _ -> "None") 
          ^ ";") 
        ""
        mlist
        ^ "],"
        ^
        (List.mapi (fun i mname' -> (i,mname')) mlist |> fun mlist -> 
          List.fold_left
          (fun e (i, mname') ->
            (List.find_opt (fun (t, _, _) -> t = mname') data.tokens |> 
            fun pop -> match pop with 
              | Some v -> 
                begin 
                  match v with 
                  | (_,Some v,_) -> e ^ "Token (" ^ mname' ^ " _" ^ string_of_int i ^");"
                  | _ -> e ^ "Token (" ^ mname' ^ ");"
                end
              | None ->
                List.find_opt (fun (m,_) -> m = mname') data.parse_marks |>
                fun pop -> match pop with
                  | Some (_,Some _) -> e ^ "Mark (" ^ mname' ^ " (Some _" ^ string_of_int i ^"));"
                  | _ -> e))
          "fun l -> match l with ["
          mlist
          ^ "] -> (Mark(" ^ mname ^ "(Some("
          ^ 
          String.map (fun c -> if c == '$' then '_' else c) tfun
          ^ ")))) | _ -> raise Not_match"
          
          )
        ^ ");\n"
        )
    ""
    data.parse_rules
    ^ 
    "]\n"
  in
  result ^ token_area ^ eof_area ^ lex_area ^ parse_mark_area ^ mark_area ^ except ^ match_area ^ parse_area 


let filenames:string list ref = ref []
let spec = []

let _ = 
  Arg.parse spec 
  (fun s -> filenames:= s::!filenames)
  "Usage: main [filename]";
  match !filenames with
  | [] -> print_endline "need an input file's name"
  | n::_ -> let inch = open_in n in 
        let outch = open_out "Lang.ml" in
      (try 
        let readData = read_from_file inch n in 
        output_string outch (build_from_data readData)
      with 
      |_-> "Error in reading the file" |> print_endline);
      close_in inch; close_out outch 

