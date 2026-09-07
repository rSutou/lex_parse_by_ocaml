open Str
open Data_struct

module type LANG = 
  sig
    type token
    val eof: token
    val lexing_rule: (regexp * (string -> token option)) list

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

module SLRParser(Lang:LANG):
  sig
    exception Parser_error of string
    val nullable :(Lang.parse_mark, bool) Dictionary.t
    val nullable_of_list :Lang.mark list -> bool
    val first :(Lang.parse_mark, Lang.token Set.t) Dictionary.t
    val first_of_list :Lang.mark list -> Lang.token Set.t
    val follow :(Lang.parse_mark, Lang.token Set.t) Dictionary.t
    val follow_of_parse_mark :Lang.parse_mark -> Lang.token Set.t 
    val parse_from_string :string -> Lang.mark

    val string_of_nullable :unit -> string
    val string_of_first :unit -> string
    val string_of_follow :unit -> string
    val string_of_rules :unit -> string
    val string_of_states :unit -> string
  end 
=
  struct
    
    exception Parser_error of string
    module StrLexer = Lexer.StringLexer(Lang)

    type 'a depend_bool = 
    | B of bool
    | Dep of 'a list

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


    type rule_id = int
    type lr_term = Lang.parse_mark * Lang.mark list * Lang.mark list * rule_id
    type lr_state = lr_term Set.t

    
    let rules :(rule_id, Lang.parse_rule) Dictionary.t =
      let id = ref 0 in
      List.fold_left
      (fun e r -> let res = Dictionary.add e !id r in id := !id + 1; res )
      Dictionary.empty Lang.parse

    let lr_term_eq (p,ph,pt,n) (p',ph',pt',n') =
      Lang.parse_mark_match p p' &&
      n = n' &&
      List.length ph = List.length ph' &&
      (List.for_all2 Lang.mark_match ph ph') &&
      List.length pt = List.length pt' &&
      (List.for_all2 Lang.mark_match pt pt')

    let table_key_eq (n1,m1) (n2,m2) = n1 = n2 && Lang.mark_match m1 m2

    let rec under_closure :lr_term Set.t -> lr_term Set.t = fun lr_set ->
      let updated = ref false in
      let res =
        Set.fold_left
        (fun e lr -> match lr with
        | (_,_,Lang.Mark pth::_,_) 
          -> Dictionary.fold_left
            (fun e n (p,ps,_) ->
              if Lang.parse_mark_match p pth && (Set.mem_with_eq lr_term_eq e (p,[],ps,n) |> not) 
              then begin updated := true; Set.add_with_eq lr_term_eq e (p,[],ps,n) end
              else e)
            e rules
        | _ -> e) 
        lr_set lr_set
      in
      if !updated then under_closure res
      else res

    let goto :lr_term Set.t -> Lang.mark -> lr_term Set.t = fun lr_set nmark ->
      Set.filter_map_with_eq lr_term_eq
      (function
      | (p,ph,pth::ptt,n) when Lang.mark_match pth nmark -> Some (p,pth::ph,ptt,n)
      | _ -> None)
      lr_set

    type state_id = int

    let first_state : lr_state = 
      match Lang.start_mark with
      | Lang.Mark s 
        -> (match Dictionary.find_opt (fun _ (p,_,_) -> Lang.parse_mark_match p s) rules with
          | Some (n,(_,ps,_)) -> under_closure (Set.add Set.empty (s,[],ps,n))
          | None -> raise (Parser_error "start rule do not exists"))
      | _ -> raise (Parser_error "start_mark is not non-terminate mark")

(* 
    let (lr_states,shift_table,reduce_table)
      :(state_id,lr_state) Dictionary.t * ((state_id*Lang.mark),state_id) Dictionary.t * (state_id,rule_id) Dictionary.t =
      let s_id = ref 0 in
      let rec sub_get_states (res_state,res_stable,res_rtable) =
        let updated = ref false in
        let res =
          Dictionary.fold_left
          (fun (rs,rst,rrt) s_id' state -> 
            Set.fold_left
            (fun (rs',rst',rrt') (_,_,pt',r_id') -> match pt' with
              | pth::_ when Lang.mark_match pth (Lang.Token Lang.eof) |> not
                -> (match Dictionary.get_opt_with_eq table_key_eq rst' (s_id',pth) with
                  | None 
                    -> updated := true; 
                      let new_state = under_closure (goto state pth) in
                      (match Dictionary.find_opt (fun _ state'' -> Set.equal_with_eq lr_term_eq state'' new_state) rs' with
                      | None 
                        -> let new_id = !s_id in s_id := new_id + 1;
                          let rs'' = Dictionary.add rs' new_id new_state in
                          let rst'' =
                            Dictionary.add_with_eq table_key_eq rst' (s_id',pth) new_id
                          in 
                          (rs'',rst'',rrt')
                      | Some (s_id'',_) 
                        -> let rst'' =
                            Dictionary.add_with_eq table_key_eq rst' (s_id',pth) s_id''
                          in 
                          (rs',rst'',rrt')) 
                  | _ -> (rs',rst',rrt')) 
              | []
                -> let rrt'' = match Dictionary.get_opt rrt' s_id' with
                  | None  -> updated := true; Dictionary.add rrt' s_id' [r_id']
                  | Some s when List.exists ((=) r_id') s |> not -> updated := true; Dictionary.add rrt' s_id' (r_id'::s)
                  | _ -> rrt'
                  in
                  (rs',rst',rrt'')
              | _ -> (rs',rst',rrt')
              )
            (rs,rst,rrt) state)
          (res_state,res_stable,res_rtable) res_state
        in
        if !updated then sub_get_states res
        else res
      in
      let first_states = Dictionary.add Dictionary.empty 0 first_state in
      s_id := 1;
      let (res_state,res_stable,res_rtable) = sub_get_states (first_states,Dictionary.empty,Dictionary.empty) in
      (res_state,
      res_stable,
      Dictionary.filter_map_kv_to_v
      (fun s_id r_ids -> match r_ids with
      | [] -> None
      | [r_id] -> Some r_id
      | _ -> raise 
            (Parser_error ("reduce/reduce conflict state_id is " ^ string_of_int s_id ^ ", rules " ^ 
            (List.fold_left (fun e i -> e ^ string_of_int i ^ ",") "" r_ids))))
      res_rtable
      ) *)

(* 
    let parse_from_string: string -> Lang.mark = fun s ->
      let rec div_list lis n = 
        if n <= 0 then ([],lis)
        else
          match lis with
          | [] -> raise (Parser_error "reduce wrong")
          | h::t -> let (hl,tl) = div_list t (n-1) in (h::hl,tl)
      in
      let rec parse_shift_reduce: (state_id list * Lang.mark list * Lang.mark list) -> Lang.mark =
        fun (s_ids,res_h,res_t) ->
          match s_ids with
          | [] -> raise (Parser_error "lost state id")
          | s_id::_ ->
          match res_t with
          | Lang.Token rt::t
            -> (match Dictionary.get_opt reduce_table s_id with
              | Some r_id 
                  -> let (_,ps,f) = List.assoc r_id rules in
                    let rmn = List.length ps in
                    let (rms,res_h_t) = div_list res_h rmn in
                    let (_,state_t) = div_list s_ids rmn in
                    parse_shift_reduce (state_t,res_h_t,f (List.rev rms)::res_t)
              | None 
                -> (match Dictionary.get_opt_with_eq shift_table (s_id,Lang.Token rt) table_key_eq with
                  | Some s -> parse_shift_reduce ((s::s_ids),(Lang.Token rt::res_h),t)
                  | None 
                    -> if Lang.token_match rt Lang.eof 
                      then (match List.assoc s_id lr_states with
                          | [(_,_,_,rid)] ->
                            let (_,ps,f) = List.assoc rid rules in
                            let res_ms = List.rev (Lang.Token rt::res_h) in
                            if List.length ps = List.length res_ms then f res_ms
                            else raise (Parser_error "final state's marks count is not match")
                          | _ -> raise (Parser_error "final state form is not match"))
                      else raise (Parser_error ("no rule for shift or reduce on " ^ Lang.string_of_token rt))))
          | Lang.Mark rm::t 
            -> ((match Dictionary.get_opt_with_eq shift_table (s_id,Lang.Mark rm) table_key_eq with
                | Some s -> parse_shift_reduce ((s::s_ids),(Lang.Mark rm::res_h),t)
                | None -> raise (Parser_error "no rule for shift")))
          | [] -> raise (Parser_error "less tokens")
      in
      let tokens = StrLexer.lex_from_string s |> List.map (fun t -> Lang.Token t) in
      parse_shift_reduce ([0],[],tokens) *)


    type parse_action =
    | Accept
    | Shift of state_id
    | Reduce of rule_id
    let string_of_action = function
    | Accept -> "Accept"
    | Shift s -> "Shift to state " ^ string_of_int s 
    | Reduce r -> "Reduce by rule " ^ string_of_int r

    let (lr_states,action_table)
      :(state_id,lr_state) Dictionary.t * ((state_id*Lang.mark),parse_action) Dictionary.t =
      let s_id = ref 0 in
      let rec sub_get_states (res_state,res_table) =
        let updated = ref false in
        let res =
          Dictionary.fold_left
          (fun (rs,rt) s_id' state -> 
            Set.fold_left
            (fun (rs',rt') (_,_,pt',r_id') -> match pt' with
              | pth::_ when Lang.mark_match pth (Lang.Token Lang.eof) |> not
                -> (match Dictionary.get_opt_with_eq table_key_eq rt' (s_id',pth) with
                  | Some acs when List.exists (function | Shift _ -> true | _ -> false) acs -> (rs',rt')
                  | _
                    -> updated := true; 
                      let new_state = under_closure (goto state pth) in
                      (match Dictionary.find_opt (fun _ state'' -> Set.equal_with_eq lr_term_eq state'' new_state) rs' with
                      | None 
                        -> let new_id = !s_id in s_id := new_id + 1;
                          let rs'' = Dictionary.add rs' new_id new_state in
                          let rt'' =
                            Dictionary.add_with_eq table_key_eq rt' (s_id',pth) [Shift new_id]
                          in 
                          (rs'',rt'')
                      | Some (s_id'',_) 
                        -> let rt'' =
                            Dictionary.add_with_eq table_key_eq rt' (s_id',pth) [Shift s_id'']
                          in 
                          (rs',rt''))) 
              | []
                ->let p = (match Dictionary.get_opt rules r_id' with
                  | Some (p,_,_) -> p
                  | None -> raise (Parser_error "rule id is inable"))
                  in
                  let rt''' = 
                    Set.fold_left
                    (fun rt'' t ->
                    (match Dictionary.get_opt_with_eq table_key_eq rt'' (s_id', Lang.Token t) with
                    | None  -> updated := true; Dictionary.add_with_eq table_key_eq rt'' (s_id', Lang.Token t) [(Reduce r_id')]
                    | Some s when List.exists ((=) (Reduce r_id')) s |> not 
                      -> updated := true;
                        Dictionary.add_with_eq table_key_eq rt'' (s_id',Lang.Token t) (Reduce r_id'::s)
                    | _ -> rt''))
                    rt' (follow_of_parse_mark p)
                  in
                  (rs',rt''')
              | _ -> (rs',Dictionary.add_with_eq table_key_eq rt' (s_id',Lang.Token Lang.eof) [Accept])
              )
            (rs,rt) state)
          (res_state,res_table) res_state
        in
        if !updated then sub_get_states res
        else res
      in
      let first_states = Dictionary.add Dictionary.empty 0 first_state in
      s_id := 1;
      let (res_state,res_table) = sub_get_states (first_states,Dictionary.empty) in
      (res_state,
      Dictionary.filter_map_kv_to_v
      (fun (s_id,m) acs -> match acs with
      | [] -> None
      | [ac] -> Some ac
      | _ -> raise 
            (Parser_error ("conflict on state_id " ^ string_of_int s_id ^ ", forward mark " ^ Lang.string_of_mark m ^ ":" ^
            (List.fold_left (fun e a -> e ^ string_of_action a ^ ",") "" acs))))
      res_table
      )
      
    let parse_from_string: string -> Lang.mark = fun s ->
      let rec div_list lis n = 
        if n <= 0 then ([],lis)
        else
          match lis with
          | [] -> raise (Parser_error "reduce wrong")
          | h::t -> let (hl,tl) = div_list t (n-1) in (h::hl,tl)
      in
      let rec parse_shift_reduce: (state_id list * Lang.mark list * Lang.mark list) -> Lang.mark =
        fun (s_ids,res_h,res_t) ->
          match s_ids with
          | [] -> raise (Parser_error "lost state id")
          | s_id::_ ->
          match res_t with
          | m::t 
            -> (match Dictionary.get_opt_with_eq table_key_eq action_table (s_id,m) with
              | Some Shift s_id' -> parse_shift_reduce ((s_id'::s_ids),(m::res_h),t)
              | Some Reduce r_id 
                -> (match Dictionary.get_opt rules r_id with
                  | Some (_,ps,f) 
                    ->
                    let rmn = List.length ps in
                    let (rms,res_h_t) = div_list res_h rmn in
                    let (_,state_t) = div_list s_ids rmn in
                    parse_shift_reduce (state_t,res_h_t,f (List.rev rms)::res_t)
                  | None -> raise (Parser_error "rule not found"))
              | Some Accept 
                -> (match Dictionary.get_opt lr_states s_id with
                  | Some set
                    -> (match Set.to_list_with_eq lr_term_eq set with
                      | [(_,_,_,rid)] 
                        -> (match Dictionary.get_opt rules rid with
                          | Some (_,ps,f) 
                            -> let res_ms = List.rev (m::res_h) in
                              (if List.length ps = List.length res_ms then f res_ms
                              else raise (Parser_error "final state's marks count is not match"))
                          | None -> raise (Parser_error "rule not found"))
                      | _ -> raise (Parser_error "final state form is not match"))
                  | _ -> raise (Parser_error "final state form is not match"))
              | None -> raise (Parser_error ("no rule for state " ^ string_of_int s_id ^ ", mark " ^ Lang.string_of_mark m)))
          | [] -> raise (Parser_error "less tokens")
      in
      let tokens = StrLexer.lex_from_string s |> List.map (fun t -> Lang.Token t) in
      parse_shift_reduce ([0],[],tokens)


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

    let string_of_rules :unit -> string = fun () ->
      Dictionary.fold_left
      (fun e r_id (p,ps,_) ->
        (List.fold_left 
        (fun e m -> e ^ Lang.string_of_mark m ^ ", ")
        (e ^ string_of_int r_id ^ " " ^ Lang.string_of_parse_mark p ^ " : ") ps)
      ^ "\n")
      "syntax rules\n"
      rules

    let string_of_states :unit -> string = fun () ->
      Dictionary.fold_left
      (fun e s_id state ->
        (Set.fold_left
        (fun e (p,ph,pt,_) ->
          List.fold_right
          (fun m e -> e ^ Lang.string_of_mark m ^ " ")
          ph (e ^ Lang.string_of_parse_mark p ^ "[ ")
          ^ "." ^
          List.fold_right
          (fun m e -> " " ^  Lang.string_of_mark m ^ e)
          pt "]\n")
      (e ^ "state " ^ string_of_int s_id ^ ": \n { \n")
      state) ^ "}\n")
      "states \n"
      lr_states
      


  end


module LR1Parser(Lang:LANG):
  sig
    exception Parser_error of string
    val nullable :(Lang.parse_mark, bool) Dictionary.t
    val nullable_of_list :Lang.mark list -> bool
    val first :(Lang.parse_mark, Lang.token Set.t) Dictionary.t
    val first_of_list :Lang.mark list -> Lang.token Set.t
    (* val follow :(Lang.parse_mark, Lang.token Set.t) Dictionary.t
    val follow_of_parse_mark :Lang.parse_mark -> Lang.token Set.t  *)
    val parse_from_string :string -> Lang.mark

    val string_of_nullable :unit -> string
    val string_of_first :unit -> string
    (* val string_of_follow :unit -> string *)
    val string_of_rules :unit -> string
    val string_of_states :unit -> string
  end 
=
  struct
    
    exception Parser_error of string
    module StrLexer = Lexer.StringLexer(Lang)

    type 'a depend_bool = 
    | B of bool
    | Dep of 'a list

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
                      (Set.remove_with_eq Lang.mark_match (Set.remove_with_eq Lang.mark_match dlis (Lang.Mark p)) m) |> Set.union_with_eq Lang.mark_match es
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
      (fun k ms -> 
      (* Set.filter_map_with_eq Lang.token_match
      (function 
      | Lang.Token t -> Some t
      |_ -> None) *)
      Set.map_with_eq Lang.token_match
      (function 
      | Lang.Token t -> t
      | Lang.Mark m -> raise (Parser_error ("Failure in first_set. Fail simplify " ^ Lang.string_of_parse_mark m ^ " in first(" ^ Lang.string_of_parse_mark k ^ ")")))
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
(*     
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
      | None -> Set.empty) *)


    type rule_id = int
    type lr_term = Lang.parse_mark * Lang.mark list * Lang.mark list * Lang.token * rule_id
    type lr_state = lr_term Set.t

    
    let rules :(rule_id, Lang.parse_rule) Dictionary.t =
      let id = ref 0 in
      List.fold_left
      (fun e r -> let res = Dictionary.add e !id r in id := !id + 1; res )
      Dictionary.empty Lang.parse

    let lr_term_eq (p,ph,pt,t,n) (p',ph',pt',t',n') =
      Lang.parse_mark_match p p' &&
      Lang.token_match t t' &&
      n = n' &&
      List.length ph = List.length ph' &&
      (List.for_all2 Lang.mark_match ph ph') &&
      List.length pt = List.length pt' &&
      (List.for_all2 Lang.mark_match pt pt')

    let table_key_eq (n1,m1) (n2,m2) = n1 = n2 && Lang.mark_match m1 m2

    let rec under_closure :lr_term Set.t -> lr_term Set.t = fun lr_set ->
      let updated = ref false in
      let res =
        Set.fold_left
        (fun e lr -> match lr with
        | (_,_,Lang.Mark pth::ptt,t,_) 
          -> let ts' = if nullable_of_list ptt then Set.add_with_eq Lang.token_match (first_of_list ptt) t else first_of_list ptt 
            in
            Set.fold_left
            (fun e t' -> 
              (Dictionary.fold_left
              (fun e n (p,ps,_) ->
                if Lang.parse_mark_match p pth && (Set.mem_with_eq lr_term_eq e (p,[],ps,t',n) |> not) 
                then begin updated := true; Set.add_with_eq lr_term_eq e (p,[],ps,t',n) end
                else e)
              e rules))
            e ts'
        | _ -> e) 
        lr_set lr_set
      in
      if !updated then under_closure res
      else res

    let goto :lr_term Set.t -> Lang.mark -> lr_term Set.t = fun lr_set nmark ->
      Set.filter_map_with_eq lr_term_eq
      (function
      | (p,ph,pth::ptt,t,n) when Lang.mark_match pth nmark -> Some (p,pth::ph,ptt,t,n)
      | _ -> None)
      lr_set

    type state_id = int

    let first_state : lr_state = 
      match Lang.start_mark with
      | Lang.Mark s 
        -> (match Dictionary.find_opt (fun _ (p,_,_) -> Lang.parse_mark_match p s) rules with
          | Some (n,(_,ps,_)) -> under_closure (Set.add Set.empty (s,[],ps,Lang.eof,n))
          | None -> raise (Parser_error "start rule do not exists"))
      | _ -> raise (Parser_error "start_mark is not non-terminate mark")

(* 
    let (lr_states,shift_table,reduce_table)
      :(state_id,lr_state) Dictionary.t * ((state_id*Lang.mark),state_id) Dictionary.t * (state_id,rule_id) Dictionary.t =
      let s_id = ref 0 in
      let rec sub_get_states (res_state,res_stable,res_rtable) =
        let updated = ref false in
        let res =
          Dictionary.fold_left
          (fun (rs,rst,rrt) s_id' state -> 
            Set.fold_left
            (fun (rs',rst',rrt') (_,_,pt',r_id') -> match pt' with
              | pth::_ when Lang.mark_match pth (Lang.Token Lang.eof) |> not
                -> (match Dictionary.get_opt_with_eq table_key_eq rst' (s_id',pth) with
                  | None 
                    -> updated := true; 
                      let new_state = under_closure (goto state pth) in
                      (match Dictionary.find_opt (fun _ state'' -> Set.equal_with_eq lr_term_eq state'' new_state) rs' with
                      | None 
                        -> let new_id = !s_id in s_id := new_id + 1;
                          let rs'' = Dictionary.add rs' new_id new_state in
                          let rst'' =
                            Dictionary.add_with_eq table_key_eq rst' (s_id',pth) new_id
                          in 
                          (rs'',rst'',rrt')
                      | Some (s_id'',_) 
                        -> let rst'' =
                            Dictionary.add_with_eq table_key_eq rst' (s_id',pth) s_id''
                          in 
                          (rs',rst'',rrt')) 
                  | _ -> (rs',rst',rrt')) 
              | []
                -> let rrt'' = match Dictionary.get_opt rrt' s_id' with
                  | None  -> updated := true; Dictionary.add rrt' s_id' [r_id']
                  | Some s when List.exists ((=) r_id') s |> not -> updated := true; Dictionary.add rrt' s_id' (r_id'::s)
                  | _ -> rrt'
                  in
                  (rs',rst',rrt'')
              | _ -> (rs',rst',rrt')
              )
            (rs,rst,rrt) state)
          (res_state,res_stable,res_rtable) res_state
        in
        if !updated then sub_get_states res
        else res
      in
      let first_states = Dictionary.add Dictionary.empty 0 first_state in
      s_id := 1;
      let (res_state,res_stable,res_rtable) = sub_get_states (first_states,Dictionary.empty,Dictionary.empty) in
      (res_state,
      res_stable,
      Dictionary.filter_map_kv_to_v
      (fun s_id r_ids -> match r_ids with
      | [] -> None
      | [r_id] -> Some r_id
      | _ -> raise 
            (Parser_error ("reduce/reduce conflict state_id is " ^ string_of_int s_id ^ ", rules " ^ 
            (List.fold_left (fun e i -> e ^ string_of_int i ^ ",") "" r_ids))))
      res_rtable
      ) *)

(* 
    let parse_from_string: string -> Lang.mark = fun s ->
      let rec div_list lis n = 
        if n <= 0 then ([],lis)
        else
          match lis with
          | [] -> raise (Parser_error "reduce wrong")
          | h::t -> let (hl,tl) = div_list t (n-1) in (h::hl,tl)
      in
      let rec parse_shift_reduce: (state_id list * Lang.mark list * Lang.mark list) -> Lang.mark =
        fun (s_ids,res_h,res_t) ->
          match s_ids with
          | [] -> raise (Parser_error "lost state id")
          | s_id::_ ->
          match res_t with
          | Lang.Token rt::t
            -> (match Dictionary.get_opt reduce_table s_id with
              | Some r_id 
                  -> let (_,ps,f) = List.assoc r_id rules in
                    let rmn = List.length ps in
                    let (rms,res_h_t) = div_list res_h rmn in
                    let (_,state_t) = div_list s_ids rmn in
                    parse_shift_reduce (state_t,res_h_t,f (List.rev rms)::res_t)
              | None 
                -> (match Dictionary.get_opt_with_eq shift_table (s_id,Lang.Token rt) table_key_eq with
                  | Some s -> parse_shift_reduce ((s::s_ids),(Lang.Token rt::res_h),t)
                  | None 
                    -> if Lang.token_match rt Lang.eof 
                      then (match List.assoc s_id lr_states with
                          | [(_,_,_,rid)] ->
                            let (_,ps,f) = List.assoc rid rules in
                            let res_ms = List.rev (Lang.Token rt::res_h) in
                            if List.length ps = List.length res_ms then f res_ms
                            else raise (Parser_error "final state's marks count is not match")
                          | _ -> raise (Parser_error "final state form is not match"))
                      else raise (Parser_error ("no rule for shift or reduce on " ^ Lang.string_of_token rt))))
          | Lang.Mark rm::t 
            -> ((match Dictionary.get_opt_with_eq shift_table (s_id,Lang.Mark rm) table_key_eq with
                | Some s -> parse_shift_reduce ((s::s_ids),(Lang.Mark rm::res_h),t)
                | None -> raise (Parser_error "no rule for shift")))
          | [] -> raise (Parser_error "less tokens")
      in
      let tokens = StrLexer.lex_from_string s |> List.map (fun t -> Lang.Token t) in
      parse_shift_reduce ([0],[],tokens) *)


    type parse_action =
    | Accept
    | Shift of state_id
    | Reduce of rule_id
    let string_of_action = function
    | Accept -> "Accept"
    | Shift s -> "Shift to state " ^ string_of_int s 
    | Reduce r -> "Reduce by rule " ^ string_of_int r

    let (lr_states,action_table)
      :(state_id,lr_state) Dictionary.t * ((state_id*Lang.mark),parse_action) Dictionary.t =
      let s_id = ref 0 in
      let rec sub_get_states (res_state,res_table) =
        let updated = ref false in
        let res =
          Dictionary.fold_left
          (fun (rs,rt) s_id' state -> 
            Set.fold_left
            (fun (rs',rt') (_,_,pt',t',r_id') -> match pt' with
              | pth::_ when Lang.mark_match pth (Lang.Token Lang.eof) |> not
                -> (match Dictionary.get_opt_with_eq table_key_eq rt' (s_id',pth) with
                  | Some acs when List.exists (function | Shift _ -> true | _ -> false) acs -> (rs',rt')
                  | _
                    -> updated := true; 
                      let new_state = under_closure (goto state pth) in
                      (match Dictionary.find_opt (fun _ state'' -> Set.equal_with_eq lr_term_eq state'' new_state) rs' with
                      | None 
                        -> let new_id = !s_id in s_id := new_id + 1;
                          let rs'' = Dictionary.add rs' new_id new_state in
                          let rt'' =
                            Dictionary.add_with_eq table_key_eq rt' (s_id',pth) [Shift new_id]
                          in 
                          (rs'',rt'')
                      | Some (s_id'',_) 
                        -> let rt'' =
                            Dictionary.add_with_eq table_key_eq rt' (s_id',pth) [Shift s_id'']
                          in 
                          (rs',rt''))) 
              | []
                -> let rt''' = 
                    (match Dictionary.get_opt_with_eq table_key_eq rt' (s_id', Lang.Token t') with
                    | None  -> updated := true; Dictionary.add_with_eq table_key_eq rt' (s_id', Lang.Token t') [(Reduce r_id')]
                    | Some s when List.exists ((=) (Reduce r_id')) s |> not 
                      -> updated := true;
                        Dictionary.add_with_eq table_key_eq rt' (s_id',Lang.Token t') (Reduce r_id'::s)
                    | _ -> rt')
                  in
                  (rs',rt''')
              | _ -> (rs',Dictionary.add_with_eq table_key_eq rt' (s_id',Lang.Token Lang.eof) [Accept])
              )
            (rs,rt) state)
          (res_state,res_table) res_state
        in
        if !updated then sub_get_states res
        else res
      in
      let first_states = Dictionary.add Dictionary.empty 0 first_state in
      s_id := 1;
      let (res_state,res_table) = sub_get_states (first_states,Dictionary.empty) in
      (res_state,
      Dictionary.filter_map_kv_to_v
      (fun (s_id,m) acs -> match acs with
      | [] -> None
      | [ac] -> Some ac
      | _ -> raise 
            (Parser_error ("conflict on state_id " ^ string_of_int s_id ^ ", forward mark " ^ Lang.string_of_mark m ^ ":" ^
            (List.fold_left (fun e a -> e ^ string_of_action a ^ ",") "" acs))))
      res_table
      )
      
    (* let string_of_states :unit -> string = fun () ->
      Dictionary.fold_left
      (fun e s_id state ->
        (Set.fold_left
        (fun e (p,ph,pt,t,_) ->
          List.fold_right
          (fun m e -> e ^ Lang.string_of_mark m ^ " ")
          ph (e ^ Lang.string_of_parse_mark p ^ "[ ")
          ^ "." ^
          List.fold_right
          (fun m e -> " " ^  Lang.string_of_mark m ^ e)
          pt (", " ^ Lang.string_of_token t ^ "]\n"))
      (e ^ "state " ^ string_of_int s_id ^ ": \n { \n")
      state) ^ "}\n")
      "states \n"
      lr_states *)
      
      
    let parse_from_string: string -> Lang.mark = fun s ->
      let rec div_list lis n = 
        if n <= 0 then ([],lis)
        else
          match lis with
          | [] -> raise (Parser_error "reduce wrong")
          | h::t -> let (hl,tl) = div_list t (n-1) in (h::hl,tl)
      in
      let rec parse_shift_reduce: (state_id list * Lang.mark list * Lang.mark list) -> Lang.mark =
        fun (s_ids,res_h,res_t) ->
          match s_ids with
          | [] -> raise (Parser_error "lost state id")
          | s_id::_ ->
          match res_t with
          | m::t 
            -> (match Dictionary.get_opt_with_eq table_key_eq action_table (s_id,m) with
              | Some Shift s_id' -> parse_shift_reduce ((s_id'::s_ids),(m::res_h),t)
              | Some Reduce r_id 
                -> (match Dictionary.get_opt rules r_id with
                  | Some (_,ps,f) 
                    ->
                    let rmn = List.length ps in
                    let (rms,res_h_t) = div_list res_h rmn in
                    let (_,state_t) = div_list s_ids rmn in
                    parse_shift_reduce (state_t,res_h_t,f (List.rev rms)::res_t)
                  | None -> raise (Parser_error "rule not found"))
              | Some Accept 
                -> (match Dictionary.get_opt lr_states s_id with
                  | Some set
                    -> 
                      (* print_endline (Set.to_list_with_eq lr_term_eq set |> List.length |> string_of_int); *)
                    (match Set.to_list_with_eq lr_term_eq set with
                      | (((_,_,_,_,_)::_ )as lis)
                        -> (List.find_map
                          (fun (_,_,_,_,rid) ->
                            (* print_endline "branch1"; *)
                          match Dictionary.get_opt rules rid with
                          | Some (_,ps,f) 
                            -> let res_ms = List.rev (m::res_h) in
                              (if List.length ps = List.length res_ms then Some (f res_ms)
                              else None)
                          | None -> raise (Parser_error "rule not found"))
                          lis |> fun op -> match op with Some op -> op | _ -> raise (Parser_error "final state's marks count is not match1"))
                      | _ -> 
                            print_endline "branch2";
                            raise (Parser_error ("final state form is not match2. state_id:" ^ string_of_int s_id ^ " , mark:"^ Lang.string_of_mark m )))
                  | _ -> raise (Parser_error "final state form is not match3"))
              | None -> raise (Parser_error ("no rule for state " ^ string_of_int s_id ^ ", mark " ^ Lang.string_of_mark m)))
          | [] -> raise (Parser_error "less tokens")
      in
      let tokens = StrLexer.lex_from_string s |> List.map (fun t -> Lang.Token t) in
      parse_shift_reduce ([0],[],tokens)


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
(* 
    let string_of_follow :unit -> string = fun () ->
      Dictionary.fold_left
      (fun e pm tset -> 
        (Set.to_list tset |> 
        List.fold_left (fun e' t -> e' ^ Lang.string_of_token t ^ ", ")
        (e ^ Lang.string_of_parse_mark pm ^ " : "))
        ^ "\n")
      "follow set of no-terminal mark\n"
      follow *)

    let string_of_rules :unit -> string = fun () ->
      Dictionary.fold_left
      (fun e r_id (p,ps,_) ->
        (List.fold_left 
        (fun e m -> e ^ Lang.string_of_mark m ^ ", ")
        (e ^ string_of_int r_id ^ " " ^ Lang.string_of_parse_mark p ^ " : ") ps)
      ^ "\n")
      "syntax rules\n"
      rules

    let string_of_states :unit -> string = fun () ->
      Dictionary.fold_left
      (fun e s_id state ->
        (Set.fold_left
        (fun e (p,ph,pt,t,_) ->
          List.fold_right
          (fun m e -> e ^ Lang.string_of_mark m ^ " ")
          ph (e ^ Lang.string_of_parse_mark p ^ "[ ")
          ^ "." ^
          List.fold_right
          (fun m e -> " " ^  Lang.string_of_mark m ^ e)
          pt (", " ^ Lang.string_of_token t ^ "]\n"))
      (e ^ "state " ^ string_of_int s_id ^ ": \n { \n")
      state) ^ "}\n")
      "states \n"
      lr_states
      


  end

  