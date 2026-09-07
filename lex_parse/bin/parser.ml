open Str

module type LANG = 
  sig
    type token
    val string_of_token : token -> string
    val eof: token
    val lexing_rule: (regexp * (string -> token option)) list
    type parse_mark
    val string_of_parse_mark : parse_mark -> string
    type parse_result
    type mark = 
    | Mark of parse_mark
    | Token of token
    (* val string_of_mark : mark -> string *)
    type mark_result = 
    | RMark of parse_result 
    | RToken of token
    val start_mark: mark
    exception Not_match
    val token_match: token -> token -> bool
    (* val mark_and_result_match : mark -> mark_result -> bool
    val mark_result_match : mark_result -> mark_result -> bool *)
    type ty_rule = parse_mark * mark list * (mark_result list -> mark_result)
    type parse_list = ty_rule list
    val parse:parse_list
  end

module Dictionary = 
  struct
    type ('k,'v) t = ('k*'v) list
    let empty:('k,'v) t = []
    let rec remove d k = match d with
    | [] -> []
    | (k',_)::t' when k' = k -> remove t' k
    | h::t' -> h :: remove t' k
    let add d k v = (k,v)::(remove d k)
    let rec get_opt d k = match d with
    | [] -> None 
    | (k',v')::_ when k' = k -> Some v'
    | _::t' -> get_opt t' k
    let map_kv_v f (d:('a,'b)t) = List.map (fun (k,v) -> (k,f k v)) d
    let filter_map_kv_v f (d:('a,'b)t) = 
      List.filter_map 
      (fun (k,v) -> match f k v with 
      | Some nv -> Some (k,nv)
      | None -> None) 
      d
    let fold_left f e d = 
      List.fold_left (fun e (k,v) -> (f e k v)) e d

    let to_list s = s
    let rec remove_with_eq d k eq = match d with
    | [] -> []
    | (k',_)::t' when eq k' k -> remove_with_eq t' k eq
    | h::t' -> h :: remove_with_eq t' k eq
    let add_with_eq d k v eq= (k,v)::(remove_with_eq d k eq)
    let rec get_opt_with_eq d k eq = match d with
    | [] -> None 
    | (k',v')::_ when eq k' k -> Some v'
    | _::t' -> get_opt_with_eq t' k eq
  end

module Set =
  struct
    type 'a t = 'a list
    let empty: 'a t = []
    let rec remove s v = match s with
    | [] -> []
    | h::t when h = v -> remove t v
    | h::t -> h::remove t v
    let rec mem s v = match s with
    | [] -> false
    | h::t -> h = v || mem t v
    let add s v = if mem s v then s else v::s
    let to_list s = s
    let union s1 s2 =
      List.fold_left (fun e x -> add e x) s1 s2
    let equals s1 s2 = 
      List.for_all (fun e1 -> List.exists (fun e2 -> e1 = e2) s2) s1
      && 
      List.for_all (fun e1 -> List.exists (fun e2 -> e1 = e2) s1) s2

    let rec remove_with_eq s v f = match s with
    | [] -> []
    | h::t when f h v -> remove_with_eq t v f
    | h::t -> h::remove_with_eq t v f
    let rec mem_with_eq s v f = match s with
    | [] -> false
    | h::t -> f h v || mem_with_eq t v f
    let add_with_eq s v f = v::remove_with_eq s v f
    let equals_with_eq s1 s2 f = 
      List.for_all (fun e1 -> List.exists (fun e2 -> f e1 e2) s2) s1
      && 
      List.for_all (fun e1 -> List.exists (fun e2 -> f e1 e2) s1) s2
    let union_with_eq s1 s2 f =
      List.fold_left (fun e x -> add_with_eq e x f) s1 s2
  end



module type LRLANG = 
  sig
    type token
    val string_of_token : token -> string
    val eof: token
    val lexing_rule: (regexp * (string -> token option)) list
    type parse_mark
    val string_of_parse_mark : parse_mark -> string
    type mark = 
    | Mark of parse_mark
    | Token of token
    val string_of_mark : mark -> string
    val start_mark: mark
    exception Not_match
    val token_match: token -> token -> bool
    val parse_mark_match :parse_mark -> parse_mark -> bool
    val mark_match : mark -> mark -> bool
    type ty_rule = parse_mark * mark list * (mark list -> mark)
    type parse_list = ty_rule list
    val parse:parse_list
  end

module LRParser(Lang:LRLANG) = 
  struct
    exception Parser_error of string
    module StrLexer = Lexer.StringLexer(Lang)

    

    type 'a depend_bool = 
    | B of bool
    | Dep of 'a list

    type depend_dict = (Lang.parse_mark,Lang.parse_mark depend_bool depend_bool) Dictionary.t

    let rec delete_depend (dep_d:depend_dict) :depend_dict =
      let updated = ref false in
      let delete_depend_line 
      (depb:Lang.parse_mark depend_bool)
      :Lang.parse_mark depend_bool = 
        match depb with 
        | B _ -> depb
        | Dep deps ->
          match
          List.fold_left
          (fun e p ->
            match e with
            | B _ -> e (* B false しか来ないはず *)
            | Dep e' ->
              (match Dictionary.get_opt_with_eq dep_d p Lang.parse_mark_match with
              | Some B true -> updated := true; e
              | Some B false -> updated := true; B false
              | _ -> Dep (p::e')))
          (Dep []) deps
          with 
          | Dep [] -> updated := true; B true
          | x -> x
      in
      let delete_depend_matrix 
        (depbb: Lang.parse_mark depend_bool depend_bool)
        : Lang.parse_mark depend_bool depend_bool =
        match depbb with 
        | B _ -> depbb 
        | Dep depss ->
          match
          List.fold_left
          (fun e ps -> 
            match e with
            | B _ -> e (* B true しか来ないはず *)
            | Dep e' ->
              (match delete_depend_line ps with
              | B true -> B true
              | B false -> updated := true; e
              | Dep _ as ps' -> Dep (ps'::e')))
          (Dep []) depss
          with 
          | Dep [] -> updated := true; B false
          | x -> x
      in
      match 
      Dictionary.map_kv_v
      (fun _ dep_bool -> 
        match dep_bool with
        | B _ -> dep_bool
        | Dep _ -> delete_depend_matrix dep_bool)
      dep_d with
      | nd when !updated -> delete_depend nd 
      | nd -> nd
(*     
    let rec get_terminatable_depend
      (dep_d:depend_dict) 
      (rules: Lang.parse_list)
      :depend_dict =
      match rules with
      | (p,ps,_)::t when List.exists (fun m -> Lang.mark_match m (Lang.Mark p)) ps 
        -> (match Dictionary.get_opt dep_d p with
          | None -> get_terminatable_depend (Dictionary.add dep_d p (Dep [])) t (* or false に相当するものを入れておく *)
          | _ -> get_terminatable_depend dep_d t)
      | (p,ps,_)::t 
        -> (match Dictionary.get_opt_with_eq dep_d p Lang.parse_mark_match with
          | Some B _ -> get_terminatable_depend dep_d t
          | _ when List.for_all (function Lang.Token _ -> true |_ -> false) ps 
            -> get_terminatable_depend (Dictionary.add dep_d p (B true)) t
          | Some Dep deps
            -> get_terminatable_depend 
              (Dictionary.add dep_d p 
              (Dep (Dep (List.filter_map (function Lang.Mark m -> Some m | Token _ -> None) ps) :: deps)))
              t 
          | None 
            -> get_terminatable_depend 
              (Dictionary.add dep_d p 
              (Dep (Dep (List.filter_map (function Lang.Mark m -> Some m | Token _ -> None) ps)::[])))
              t ) 
      | [] -> dep_d *)

    let rec get_nullable_depend
      (dep_d:depend_dict) 
      (rules: Lang.parse_list)
      :depend_dict =
      match rules with
        | (p,[],_)::t -> get_nullable_depend (Dictionary.add_with_eq dep_d p (B true) Lang.parse_mark_match) t
        | (p,ps,_)::t when List.exists (function Lang.Token _ -> true | Lang.Mark m -> m = p) ps 
          -> (match Dictionary.get_opt_with_eq dep_d p Lang.parse_mark_match with
            | None -> get_nullable_depend (Dictionary.add_with_eq dep_d p (Dep []) Lang.parse_mark_match) t (* or false に相当するものを入れておく *)
            | _ -> get_nullable_depend dep_d t)
        (* 全部自身と異なる非終端記号 *)
        | (p,ps,_)::t 
          -> (match Dictionary.get_opt_with_eq dep_d p Lang.parse_mark_match with
            | Some B _ -> get_nullable_depend dep_d t (* B true しか来ないはず *)
            | Some Dep deps
              -> get_nullable_depend 
                (Dictionary.add_with_eq dep_d p 
                (Dep (Dep(List.filter_map (function Lang.Mark m -> Some m | Token _ -> None) ps) ::deps))
                Lang.parse_mark_match)
                t 
            | None 
              -> get_nullable_depend 
                (Dictionary.add_with_eq dep_d p 
                (Dep (Dep(List.filter_map (function Lang.Mark m -> Some m | Token _ -> None) ps) ::[]))
                Lang.parse_mark_match)
                t ) 
        | [] -> dep_d


    (* let terminatable: (Lang.parse_mark, bool) Dictionary.t =
      let dep_d = get_terminatable_depend Dictionary.empty Lang.parse in
      delete_depend dep_d 
      |> (fun x -> List.map 
      (fun (p,depb) -> match depb with
      | B b -> (p,b)
      | Dep _ -> (p,false)
      ) x)  *)
    
    (* let terminatable_of_list marks =
      List.for_all
      (function
      | Lang.Mark m -> Dictionary.get_opt terminatable m = Some true
      | Lang.Token _ -> true)
      marks *)

    let nullable: (Lang.parse_mark, bool) Dictionary.t =
      let dep_d = get_nullable_depend [] Lang.parse in
      delete_depend dep_d |>
      Dictionary.map_kv_v 
      (fun _ depb -> match depb with
      | B b -> b
      | Dep _ -> false
      )
    
    let nullable_of_list marks =
      List.for_all
      (function
      | Lang.Mark m -> Dictionary.get_opt_with_eq nullable m Lang.parse_mark_match = Some true
      | Lang.Token _ -> false)
      marks


    let rec delete_depend_set (dep_d:(Lang.parse_mark,Lang.mark Set.t) Dictionary.t) =
      let updated = ref false in
      let d =
      Dictionary.fold_left
      (fun e p dep_set -> 
        let new_dep_set =
          Set.to_list dep_set 
          |> List.fold_left 
          (fun es m -> match m with
          | Lang.Token _ -> Set.add_with_eq es m Lang.mark_match
          | Lang.Mark pm when Lang.parse_mark_match pm p |> not 
            -> let es' = Set.remove_with_eq es m Lang.mark_match in
              (match Dictionary.get_opt_with_eq e pm Lang.parse_mark_match with
              | Some dlis 
                -> updated := true; 
                  Set.remove_with_eq dlis m Lang.mark_match |>
                  (fun x -> Set.union_with_eq es' x Lang.mark_match)
              | None -> es')
          | _ -> es
          ) 
          Set.empty
        in Dictionary.add_with_eq e p new_dep_set Lang.parse_mark_match) 
      Dictionary.empty dep_d in
      if !updated then delete_depend_set d
      else d
    
    let rec get_first_depend
      (dep_d:(Lang.parse_mark, Lang.mark Set.t) Dictionary.t)
      (rules: Lang.parse_list)
      :(Lang.parse_mark, Lang.mark Set.t) Dictionary.t =
      let rec gather_of_parse_list ps res_set = 
        match ps with
        | h::t when nullable_of_list [h] -> gather_of_parse_list t (Set.add_with_eq res_set h Lang.mark_match)
        | h::_ -> Set.add_with_eq res_set h Lang.mark_match
        | [] -> res_set
      in
      match rules with
        | (p,ps,_)::t 
          -> let d = (match Dictionary.get_opt_with_eq dep_d p Lang.parse_mark_match with
            | Some d -> d 
            | None -> Set.empty) in
            get_first_depend 
            (Dictionary.add_with_eq dep_d p (Set.union d (gather_of_parse_list ps Set.empty)) Lang.parse_mark_match)
            t
        | [] -> dep_d

    let first:(Lang.parse_mark, Lang.token Set.t) Dictionary.t =
      let f_dict = get_first_depend Dictionary.empty Lang.parse
      in 
      delete_depend_set f_dict |> 
      Dictionary.map_kv_v
      (fun _ ms -> 
      ms |> Set.to_list |> List.map (function Lang.Token t -> t |_ -> raise (Parser_error "Failure in first_set.")))

    let rec first_of_list marks =
      match marks with
      | Lang.Token ht::_ -> Set.add Set.empty ht
      | Lang.Mark hm::t 
        -> (match Dictionary.get_opt_with_eq first hm Lang.parse_mark_match, Dictionary.get_opt_with_eq nullable hm Lang.parse_mark_match with
          | Some res, Some true -> Set.union res (first_of_list t)
          | Some res, _ -> res 
          | None, Some true -> first_of_list t
          | None, _ -> Set.empty)
      | [] -> Set.empty
    
    let rec get_follow_depend
      (dep_d:(Lang.parse_mark, Lang.mark Set.t) Dictionary.t)
      (rules: Lang.parse_list)
      :(Lang.parse_mark, Lang.mark Set.t) Dictionary.t =
      let follow2 (tail:Lang.mark list) (left_mark: Lang.parse_mark)
        = if nullable_of_list tail 
          then Set.add_with_eq (first_of_list tail |> List.map (fun x -> Lang.Token x)) (Lang.Mark left_mark) Lang.mark_match
          else first_of_list tail |> List.map (fun x -> Lang.Token x)
      in
      let rec sub_iter p ps res_d =
        match ps with
        | [] -> res_d
        | Lang.Token _::t -> sub_iter p t res_d
        | Lang.Mark x::t 
          -> (match Dictionary.get_opt_with_eq res_d x Lang.parse_mark_match with
            | Some d -> Dictionary.add_with_eq res_d x (Set.union d (follow2 t p)) Lang.parse_mark_match
            | None -> Dictionary.add_with_eq res_d x (follow2 t p) Lang.parse_mark_match
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
      Dictionary.map_kv_v
      (fun _ ms -> 
      ms |> Set.to_list |> List.map (function Lang.Token t -> t |_ -> raise (Parser_error "Failure in follow_set.")))
    
    let follow_of_mark pm =
      (match Dictionary.get_opt_with_eq follow pm Lang.parse_mark_match with
      | Some res -> res  
      | None -> Set.empty)
    

    type rule_id = int
    type lr_term = Lang.parse_mark * Lang.mark list * Lang.mark list * rule_id
    type lr_state = lr_term Set.t

    let rules :(rule_id, Lang.ty_rule) Dictionary.t =
      let id = ref 0 in
      List.fold_left
      (fun e r -> let res = Dictionary.add e !id r in id := !id + 1; res )
      Dictionary.empty Lang.parse

    let lr_term_eq (p,ph,pt,n) (p',ph',pt',n') =
      p = p' && n = n' &&
      List.length ph = List.length ph' &&
      List.length pt = List.length pt' &&
      (List.for_all2 Lang.mark_match ph ph') && 
      (List.for_all2 Lang.mark_match pt pt')

    let table_key_eq (n1,m1) (n2,m2) = n1 = n2 && Lang.mark_match m1 m2

    let rec under_closure:lr_term Set.t -> lr_term Set.t = fun lr_set ->
      let updated = ref false in
      let res =
        List.fold_left 
        (fun e lr -> match lr with
        | (_,_,Lang.Mark pth::_,_) 
          -> List.fold_left
            (fun e (n,(p,ps,_)) ->
              if Lang.parse_mark_match p pth && (Set.mem_with_eq e (p,[],ps,n) lr_term_eq |> not) 
              then begin updated := true; Set.add_with_eq e (p,[],ps,n) lr_term_eq end
              else e)
            e rules
        | _ -> e) 
        lr_set (Set.to_list lr_set)
      in
      if !updated then under_closure res
      else res

    let goto :lr_term Set.t -> Lang.mark -> lr_term Set.t = fun lr_set nmark ->
      List.filter_map 
      (function 
      | (p,ph,pth::ptt,n) when Lang.mark_match pth nmark -> Some (p,pth::ph,ptt,n)
      | _ -> None)
      (Set.to_list lr_set)
      |> (fun x -> Set.union_with_eq Set.empty x lr_term_eq)

    type state_id = int

    let first_state : lr_state = 
      match Lang.start_mark with
      | Lang.Mark s 
        -> (match List.find (fun (_,(p,_,_)) -> Lang.parse_mark_match p s) rules with
          | (n,(_,ps,_)) -> under_closure (Set.add Set.empty (s,[],ps,n)))
      | _ -> raise (Parser_error "start_mark is not non-terminate mark")
    
    let (lr_states,shift_table,reduce_table) 
    : (state_id * lr_state) list * ((state_id*Lang.mark),state_id) Dictionary.t * (state_id,rule_id) Dictionary.t =
      let s_id = ref 0 in
      let rec sub_get_states (res_state,res_stable,res_rtable) =
        let updated = ref false in
        let res =
          List.fold_left
          (fun (rs,rst,rrt) (s_id',state) -> 
            List.fold_left 
            (fun (rs',rst',rrt') (_,_,pt',r_id') -> match pt' with
              | pth::_ when Lang.mark_match pth (Lang.Token Lang.eof) |> not
                -> (match Dictionary.get_opt_with_eq rst' (s_id',pth) table_key_eq with
                  | None 
                    -> updated := true; 
                      let new_state = under_closure (goto state pth) in
                      (match List.find_opt (fun (_,state'') -> Set.equals_with_eq state'' new_state lr_term_eq) rs' with
                      | None 
                        -> let new_id = !s_id in s_id := new_id + 1;
                          let rs'' = (new_id,new_state)::rs' in
                          let rst'' =
                            Dictionary.add_with_eq rst' (s_id',pth) new_id table_key_eq
                          in 
                          (rs'',rst'',rrt')
                      | Some (s_id'',_) 
                        -> let rst'' =
                            Dictionary.add_with_eq rst' (s_id',pth) s_id'' table_key_eq
                          in 
                          (rs',rst'',rrt')) 
                  | _ -> (rs',rst',rrt')) 
              | []
                -> let rrt'' = match Dictionary.get_opt rrt' s_id' with 
                  | None  -> updated := true; Dictionary.add rrt' s_id' [r_id']
                  | Some s when Set.mem s r_id' |> not -> updated := true; Dictionary.add rrt' s_id' (r_id'::s)
                  | _ -> rrt'
                  in
                  (rs',rst',rrt'')
              | _ -> (rs',rst',rrt')
              )
            (rs,rst,rrt) (Set.to_list state))
          (res_state,res_stable,res_rtable) res_state
        in
        if !updated then sub_get_states res
        else res
      in
      let first_states = [(0,first_state)] in
      s_id := 1;
      let (res_state,res_stable,res_rtable) = sub_get_states (first_states,Dictionary.empty,Dictionary.empty) in
      (res_state,
      res_stable,
      Dictionary.filter_map_kv_v
      (fun s_id r_ids -> match r_ids with
      | [] -> None
      | [r_id] -> Some r_id
      | _ -> raise (Parser_error ("reduce/reduce conflict state_id is "^ string_of_int s_id)))
      res_rtable
      )

    (* let final_state_id = 
      match Lang.start_mark with
      | Lang.Mark s 
        -> (match List.find (fun (_,(p,_,_)) -> p = s) rules with
          | (n,(_,ps,_)) -> 
            List.find 
            (fun (_,state) -> 
              match Set.to_list state with
              | [(p,ph,[],rid)] when p = s && rid = n -> (List.rev ph = ps)
              | _ -> false)
            lr_states) |> fst
      | _ -> raise (Parser_error "start_mark is not non-terminate mark") *)

    let parse_from_string: string -> Lang.mark = fun s ->
      let rec div_list lis n = 
        if n <= 0 then ([],lis)
        else
          match lis with
          | [] -> raise (Parser_error "reduce wrong")
          | h::t -> let (hl,tl) = div_list t (n-1) in (h::hl,tl)
      in
      let tokens = StrLexer.lex_from_string s |> List.map (fun t -> Lang.Token t) in
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
      parse_shift_reduce ([0],[],tokens)
      


  end
