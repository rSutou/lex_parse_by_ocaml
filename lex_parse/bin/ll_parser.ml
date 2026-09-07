open Data_struct
open Langs


(* 先読みに失敗したらバックトラックする。解析能力としてはPEGと同等 *)
module LLParser(Lang:LANG_PARSE) :
  sig
    exception Parser_error of string
    val parse_from_string :string -> Lang.mark
  end
= 
  struct
    module StrLexer = Lexer.StringLexer(Lang)
    exception Parser_error of string

    let parse_from_string: string -> Lang.mark =
      let rec parse_partial: Lang.token list -> Lang.mark -> (Lang.mark * Lang.token list) =
        fun ts m ->
          match m with
          | Lang.Mark pm -> try_parse ts pm Lang.parse
          | Lang.Token t 
            -> (match ts with 
              | t'::ts' when Lang.token_match t' t -> (Lang.Token t', ts')
              | t'::_ -> raise (Parser_error ("unmatch at " ^ Lang.string_of_token t' ))
              | [] -> raise (Parser_error "less tokens"))
      and try_parse: Lang.token list -> Lang.parse_mark -> Lang.parse_list -> (Lang.mark * Lang.token list) =
        fun tokens pm rules ->
          match rules with
          | (pm', ms',f')::rules' when Lang.parse_mark_match pm' pm
            -> (try
                let (rms'',ts'') = 
                  (List.fold_left 
                  (fun (rms,ts) m -> let (rm',ts') = parse_partial ts m in (rm'::rms,ts')) 
                  ([],tokens) ms') 
                in 
                (f' (List.rev rms''),ts'')
              with 
              | Parser_error _ -> try_parse tokens pm rules')
          | _::rules' -> try_parse tokens pm rules'
          | [] -> raise (Parser_error "no match rules")
      in 
      fun s ->
      let tokens = StrLexer.lex_from_string s in
      match parse_partial tokens Lang.start_mark with
      | (rm,[]) -> rm
      | (rm,t::_) when Lang.token_match t Lang.eof -> rm
      | _ -> raise (Parser_error "Program has extra useless token")
  end


module LL1Parser(Lang:LANG_PARSE) :
  sig
    exception Parser_error of string
    val nullable :(Lang.parse_mark, bool) Dictionary.t
    val nullable_of_list :Lang.mark list -> bool
    val first :(Lang.parse_mark, Lang.token Set.t) Dictionary.t
    val first_of_list :Lang.mark list -> Lang.token Set.t
    val follow :(Lang.parse_mark, Lang.token Set.t) Dictionary.t
    val follow_of_parse_mark :Lang.parse_mark -> Lang.token Set.t 
    val director_of_rule :Lang.parse_mark -> Lang.mark list -> Lang.token Set.t
    val director_table :(Lang.parse_mark*Lang.token,Lang.parse_rule) Dictionary.t
    val parse_from_string :string -> Lang.mark

    val string_of_nullable :unit -> string
    val string_of_first :unit -> string
    val string_of_follow :unit -> string
    val string_of_director :unit -> string
    val string_of_parse_table :unit -> string
  end
=
  struct
    exception Parser_error of string
    module StrLexer = Lexer.StringLexer(Lang)

    type 'a depend_bool = 
    | B of bool
    | Dep of 'a list

    (* 論理式の積和形として、依存関係のある非終端記号間の関係を示すデータ構造 *)
    type depend_dict = (Lang.parse_mark,Lang.parse_mark depend_bool depend_bool) Dictionary.t

    let rec delete_depend (dep_d:depend_dict) :depend_dict =
      let updated = ref false in
      let delete_depend_line (depb:Lang.parse_mark depend_bool) :Lang.parse_mark depend_bool = 
        match depb with
        | B _ -> depb
        | Dep deps
          -> let depb' =
              List.fold_left
              (fun e p -> match e with
                | B _ -> e (* false しか来ないべき *)
                | Dep e'
                  -> (match Dictionary.get_opt_with_eq Lang.parse_mark_match dep_d p with
                    | Some B true -> updated := true; e
                    | Some B false | None -> updated := true; B false
                    | Some Dep _ -> Dep (p::e')))
              (Dep []) deps
            in
            (match depb' with 
            | Dep [] -> updated := true; B true
            | _ -> depb')
      in
      let delete_depend_matrix (depss: Lang.parse_mark depend_bool list) :Lang.parse_mark depend_bool depend_bool =
        let depbb' =
          List.fold_left
          (fun e depb ->
            match e with
            | B _ -> e (* B true しか来ないべき *)
            | Dep e' ->
              (match delete_depend_line depb with
              | B true -> B true
              | B false -> updated := true; e
              | depb' -> Dep (depb'::e')))
          (Dep []) depss
        in
        (match depbb' with
        | Dep [] -> updated := true; B false
        | _ -> depbb')
      in
      let dep_d' =
        Dictionary.map_kv_to_v
        (fun _ dep_bool ->
          match dep_bool with
          | B _ -> dep_bool
          | Dep depss -> delete_depend_matrix depss)
        dep_d
      in
      if !updated then delete_depend dep_d'
      else dep_d'

    let rec get_nullable_depend (dep_d:depend_dict) (rules: Lang.parse_list) :depend_dict =
      let dict_add = Dictionary.add_with_eq Lang.parse_mark_match in
      let dict_get_opt = Dictionary.get_opt_with_eq Lang.parse_mark_match in
      match rules with
        | (p,[],_)::t -> get_nullable_depend (dict_add dep_d p (B true)) t
        | (p,ps,_)::t when List.exists (function | Lang.Token _ -> true | Lang.Mark m -> Lang.parse_mark_match m p ) ps
          -> get_nullable_depend dep_d t
        | (p,ps,_)::t 
          -> (match dict_get_opt dep_d p with
            | Some B _ -> get_nullable_depend dep_d t (* true しか来ないべき *)
            | Some Dep deps
              -> get_nullable_depend
                (dict_add dep_d p
                (Dep (Dep(List.filter_map (function Lang.Mark m -> Some m | Token _ -> None) ps) ::deps)))
                t
            | None 
              -> get_nullable_depend 
                (dict_add dep_d p 
                (Dep (Dep(List.filter_map (function Lang.Mark m -> Some m | Token _ -> None) ps) ::[])))
                t)
        | [] -> dep_d

    let nullable: (Lang.parse_mark, bool) Dictionary.t =
      let dep_d = get_nullable_depend Dictionary.empty Lang.parse in
      delete_depend dep_d |>
      Dictionary.map_kv_to_v
      (fun _ depb -> match depb with
      | B true -> true
      | _ -> false)
    
    let nullable_of_list :Lang.mark list -> bool = 
      fun marks ->
      List.for_all
      (function
      | Lang.Mark m -> Dictionary.get_opt_with_eq Lang.parse_mark_match nullable m = Some true
      | Lang.Token _ -> false)
      marks

    let rec delete_depend_set (dep_d:(Lang.parse_mark,Lang.mark Set.t) Dictionary.t) =
      let updated = ref false in
      let d =
        Dictionary.fold_left
        (fun e p dep_set -> 
          let new_dep_set =
            Set.to_list_with_eq Lang.mark_match dep_set |>
            List.fold_left 
            (fun es m -> match m with
              | Lang.Token _ -> Set.add_with_eq Lang.mark_match es m
              | Lang.Mark pm when Lang.parse_mark_match pm p |> not
                -> (match Dictionary.get_opt_with_eq Lang.parse_mark_match e pm with
                  | Some dlis
                    -> updated := true;
                      Set.remove_with_eq Lang.mark_match dlis m |> Set.union_with_eq Lang.mark_match es
                  | None -> Set.add_with_eq Lang.mark_match es m)
              | _ -> es)
            Set.empty
          in 
          Dictionary.add_with_eq Lang.parse_mark_match e p new_dep_set)
        Dictionary.empty dep_d 
      in
      if !updated then delete_depend_set d
      else d


    type dep_mark_dict = (Lang.parse_mark, Lang.mark Set.t) Dictionary.t

    let rec get_first_depend (dep_d:dep_mark_dict) (rules: Lang.parse_list) :dep_mark_dict =
      let rec gather_of_marks ps res_set =
        match ps with
        | h::t when nullable_of_list [h] -> gather_of_marks t (Set.add_with_eq Lang.mark_match res_set h)
        | h::_ -> Set.add_with_eq Lang.mark_match res_set h
        | [] -> res_set
      in
      match rules with
        | (p,ps,_)::t 
          -> let d = 
              (match Dictionary.get_opt_with_eq Lang.parse_mark_match dep_d p with
              | Some d -> d 
              | None -> Set.empty)
            in
            get_first_depend 
            (Dictionary.add_with_eq Lang.parse_mark_match dep_d p (gather_of_marks ps d))
            t
        | [] -> dep_d

    let first:(Lang.parse_mark, Lang.token Set.t) Dictionary.t =
      let f_dict = get_first_depend Dictionary.empty Lang.parse in
      delete_depend_set f_dict |>
      Dictionary.map_kv_to_v
      (fun _ ms -> 
      Set.map_with_eq Lang.token_match
      (function 
      | Lang.Token t -> t
      |_ -> raise (Parser_error "Failure in first_set."))
      ms)

    let rec first_of_list :Lang.mark list -> Lang.token Set.t =
      fun marks ->
      match marks with
      | Lang.Token ht::_ -> Set.add_with_eq Lang.token_match Set.empty ht
      | (Lang.Mark hpm as hm)::t
        -> let set1 = 
            (match Dictionary.get_opt_with_eq Lang.parse_mark_match first hpm with
            | Some s -> s
            | None -> Set.empty)
          in 
          if nullable_of_list [hm] then Set.union set1 (first_of_list t)
          else set1
      | [] -> Set.empty
    
    let rec get_follow_depend (dep_d:dep_mark_dict) (rules: Lang.parse_list) :dep_mark_dict =
      let follow2 (tail:Lang.mark list) (left_mark: Lang.parse_mark)
        = if nullable_of_list tail 
          then Set.add_with_eq Lang.mark_match 
              (first_of_list tail |> Set.map_with_eq Lang.mark_match (fun x -> Lang.Token x)) (Lang.Mark left_mark)
          else first_of_list tail |> Set.map_with_eq Lang.mark_match (fun x -> Lang.Token x)
      in
      let rec sub_iter p ps res_d =
        match ps with
        | [] -> res_d
        | Lang.Token _::t -> sub_iter p t res_d
        | Lang.Mark x::t 
          -> (match Dictionary.get_opt_with_eq Lang.parse_mark_match res_d x with
            | Some d -> Dictionary.add_with_eq Lang.parse_mark_match res_d x (Set.union_with_eq Lang.mark_match d (follow2 t p))
            | None -> Dictionary.add_with_eq Lang.parse_mark_match res_d x (follow2 t p)
            ) |> sub_iter p t
      in
      match rules with
        | (p,ps,_)::t 
          -> get_follow_depend (sub_iter p ps dep_d) t
        | [] -> dep_d

    let follow:(Lang.parse_mark, Lang.token Set.t) Dictionary.t = 
      let f_dict = get_follow_depend Dictionary.empty Lang.parse
      in 
      delete_depend_set f_dict |> 
      Dictionary.map_kv_to_v
      (fun _ ms -> 
      Set.map_with_eq Lang.token_match 
      (function 
      | Lang.Token t -> t
      | _ -> raise (Parser_error "Failure in follow_set."))
      ms)
    
    let follow_of_parse_mark pm =
      (match Dictionary.get_opt follow pm with
      | Some res -> res 
      | None -> Set.empty)
    
    let director_of_rule p ps =
      if nullable_of_list ps
      then Set.union_with_eq Lang.token_match (first_of_list ps) (follow_of_parse_mark p)
      else first_of_list ps

    let dict_key_eq (p1,t1) (p2,t2) = Lang.parse_mark_match p1 p2 && Lang.token_match t1 t2

    let director_table :(Lang.parse_mark*Lang.token,Lang.parse_rule) Dictionary.t =
      let dict_add = Dictionary.add_with_eq dict_key_eq in
      let rec add_table dic rules =
        match rules with
        | (p,ps,_)as h::t 
          -> let dir_ts = director_of_rule p ps in
            Set.to_list dir_ts |>
            List.fold_left
            (fun edic t ->
            (match Dictionary.get_opt_with_eq dict_key_eq edic (p,t) with
            | Some rs -> dict_add edic (p,t) (h::rs)
            | None -> dict_add edic (p,t) [h])
            ) dic 
            |> (fun x -> add_table x t)
        | [] -> dic
      in
      let temp_table = add_table Dictionary.empty Lang.parse in
      Dictionary.filter_map_kv_to_v 
      (fun (p,t) rulelist -> match rulelist with
      | [] -> None
      | [h] -> Some h
      | _ -> raise (Parser_error ("conflict on state " ^ Lang.string_of_parse_mark p ^ ", token "^Lang.string_of_token t)))
      temp_table

    let parse_from_string :string -> Lang.mark =
      let rec parse_partial: Lang.token list -> Lang.mark -> (Lang.mark * Lang.token list) =
        fun ts m ->
          match m,ts with
          | Lang.Token mt, ht::tt when Lang.token_match mt ht -> (Lang.Token ht,tt)
          | Lang.Mark pm, ht::_
            -> (match Dictionary.get_opt_with_eq dict_key_eq director_table (pm,ht) with
              | Some (_,ps,rf)
                -> let (res,tail) =
                  List.fold_left 
                  (fun (rlist,ts) pm -> let (r',ts') = parse_partial ts pm in (r'::rlist,ts'))
                  ([],ts)
                  ps
                  in
                  (rf (List.rev res), tail)
              | None -> raise (Parser_error ("no shift rule on state " ^ Lang.string_of_parse_mark pm ^ ", token " ^ Lang.string_of_token ht)))
          | Lang.Token mt, [] when Lang.token_match mt Lang.eof -> (Lang.Token Lang.eof,[])
          | Lang.Token mt, ht::_ -> raise (Parser_error ("not match token " ^ Lang.string_of_token ht ^ ", but expected " ^ Lang.string_of_token mt))
          | _, [] -> raise (Parser_error ("less token to parse " ^ Lang.string_of_mark m) )
      in 
      fun s ->
      let tokens = StrLexer.lex_from_string s in
      match parse_partial tokens Lang.start_mark with
      | (rm,[]) -> rm
      | (rm,t::_) when Lang.token_match t Lang.eof -> rm
      | _ -> raise (Parser_error "Program has extra useless token")



    let string_of_nullable :unit -> string = fun () ->
      Dictionary.fold_left
      (fun e pm b -> e ^ Lang.string_of_parse_mark pm ^ " : " ^ string_of_bool b ^ "\n")
      "nullablity of no-terminal mark\n"
      nullable

    let string_of_first :unit -> string = fun () ->
      Dictionary.fold_left
      (fun e pm tset -> 
        (Set.to_list tset |> 
        List.fold_left (fun e' t -> e' ^ Lang.string_of_token t ^ ", ")
        (e ^ Lang.string_of_parse_mark pm ^ " : "))
        ^ "\n")
      "first set of no-terminal mark\n"
      first

    let string_of_follow :unit -> string = fun () ->
      Dictionary.fold_left
      (fun e pm tset -> 
        (Set.to_list tset |> 
        List.fold_left (fun e' t -> e' ^ Lang.string_of_token t ^ ", ")
        (e ^ Lang.string_of_parse_mark pm ^ " : "))
        ^ "\n")
      "follow set of no-terminal mark\n"
      follow

    let string_of_director :unit -> string = fun () ->
      List.fold_left
      (fun e (p,ps,_) ->
        let rule_s = 
          (List.fold_left 
          (fun e' m -> e' ^ " " ^ Lang.string_of_mark m )
          (e ^ Lang.string_of_parse_mark p ^ " : ")
          ps)
          ^ "\n     "
        in
        (Set.to_list (director_of_rule p ps) |>
        List.fold_left 
        (fun e' t -> e' ^ Lang.string_of_token t ^ ", ")
        rule_s)
        ^ "\n")
      "director set of rule\n"
      Lang.parse

    let string_of_parse_table :unit -> string = fun () ->
      Dictionary.fold_left
      (fun e (p,t) (_,ps,_) -> 
        (List.fold_left (fun e' t' -> e' ^ Lang.string_of_mark t' ^ ", ")
        (e ^ "(" ^ Lang.string_of_parse_mark p ^ ", " ^ Lang.string_of_token t ^ ") : ")
        ps)
        ^ "\n")
      "parse table \n"
      director_table

  end

