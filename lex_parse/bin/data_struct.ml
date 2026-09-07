module Set :
  sig
    type 'a t
    val empty :'a t

    val remove_with_eq :('a -> 'a -> bool ) -> 'a t -> 'a -> 'a t
    val mem_with_eq :('a -> 'a -> bool ) -> 'a t -> 'a -> bool
    val add_with_eq :('a -> 'a -> bool ) -> 'a t -> 'a -> 'a t
    val union_with_eq :('a -> 'a -> bool ) -> 'a t -> 'a t -> 'a t
    val is_subset_with_eq :('a -> 'a -> bool ) -> 'a t -> 'a t -> bool
    val equal_with_eq :('a -> 'a -> bool ) -> 'a t -> 'a t -> bool
    val map_with_eq :('b -> 'b -> bool ) -> ('a -> 'b) -> 'a t -> 'b t
    val filter_map_with_eq :('b -> 'b -> bool ) -> ('a -> 'b option) -> 'a t -> 'b t

    val remove :'a t -> 'a -> 'a t
    val mem :'a t -> 'a -> bool
    val add :'a t -> 'a -> 'a t
    val union :'a t -> 'a t -> 'a t
    val is_subset :'a t -> 'a t -> bool
    val equal :'a t -> 'a t -> bool

    val map :('a -> 'b) -> 'a t -> 'b t
    val filter_map :('a -> 'b option) -> 'a t -> 'b t
    val fold_left :('a -> 'b -> 'a) -> 'a -> 'b t -> 'a

    val normalize_with_eq : ('a -> 'a -> bool) -> 'a t -> 'a t
    val normalize :'a t -> 'a t

    val of_list_with_eq : ('a -> 'a -> bool) -> 'a list -> 'a t
    val to_list_with_eq : ('a -> 'a -> bool) -> 'a t -> 'a list

    val of_list :'a list -> 'a t
    val to_list :'a t -> 'a list
  end
=
  struct
    type 'a t = 'a list
    let empty: 'a t = []

    let remove_with_eq = fun f s v -> List.filter ((fun x -> f v x |> not)) s
    let mem_with_eq = fun f s v -> List.exists (f v) s
    let add_with_eq = fun f s v -> if mem_with_eq f s v then s else v::s
    let union_with_eq = fun f s1 s2 -> List.fold_left (fun e v -> add_with_eq f e v) s1 s2
    let is_subset_with_eq = fun f s1 s2 -> List.for_all (fun v -> List.exists (f v) s2) s1
    let equal_with_eq = fun f s1 s2 -> is_subset_with_eq f s1 s2 && is_subset_with_eq f s2 s1
    let map_with_eq = fun eq mf s -> List.fold_left (fun e x -> add_with_eq eq e (mf x)) empty s
    let filter_map_with_eq = fun eq mf s 
      -> List.fold_left
        (fun e x -> match mf x with 
          | Some v -> add_with_eq eq e v
          | None -> e)
        empty s

    let remove = fun s v -> remove_with_eq (=) s v
    let mem = fun s v -> mem_with_eq (=) s v
    let add = fun s v -> add_with_eq (=) s v
    let union = fun s1 s2 -> union_with_eq (=) s1 s2
    let is_subset = fun s1 s2 -> is_subset_with_eq (=) s1 s2
    let equal = fun s1 s2 -> equal_with_eq (=) s1 s2

    let map = fun f s -> map_with_eq (=) f s
    let filter_map = fun f s -> filter_map_with_eq (=) f s
    let fold_left = List.fold_left 

    let normalize_with_eq = fun f s -> union_with_eq f empty s
    let normalize = fun s -> normalize_with_eq (=) s

    let to_list_with_eq = fun f s -> normalize_with_eq f s
    let of_list_with_eq = fun f s -> to_list_with_eq f s
    let to_list = fun s -> to_list_with_eq (=) s
    let of_list = fun s -> of_list_with_eq (=) s
  end



module Dictionary:
  sig
    type ('k,'v) t
    val empty :('k,'v) t

    val remove_with_eq :('k -> 'k -> bool) -> ('k,'v) t -> 'k -> ('k,'v) t
    val mem_with_eq :('k -> 'k -> bool) -> ('k,'v) t -> 'k -> bool
    val add_with_eq :('k -> 'k -> bool) -> ('k,'v) t -> 'k -> 'v -> ('k,'v) t
    val get_opt_with_eq :('k -> 'k -> bool) -> ('k,'v) t -> 'k -> 'v option

    val remove :('k,'v) t -> 'k -> ('k,'v) t
    val mem :('k,'v) t -> 'k -> bool
    val add :('k,'v) t -> 'k -> 'v -> ('k,'v) t
    val get_opt :('k,'v) t -> 'k -> 'v option
    val find_opt :('k -> 'v -> bool) -> ('k,'v) t -> ('k*'v) option

    val map_kv_to_v :('k -> 'v -> 'c) -> ('k,'v) t -> ('k,'c) t
    val filter_map_kv_to_v :('k -> 'v -> 'c option) -> ('k,'v) t -> ('k,'c) t
    val fold_left :('a -> 'k -> 'v -> 'a) -> 'a -> ('k,'v) t -> 'a
    
    val of_list_with_eq :('k -> 'k -> bool) -> ('k*'v) list -> ('k,'v) t
    val to_list_with_eq :('k -> 'k -> bool) -> ('k,'v) t -> ('k*'v) list

    val of_list :('k*'v) list -> ('k,'v) t
    val to_list :('k,'v) t -> ('k*'v) list
  end
= 
  struct
    type ('k,'v) t = ('k*'v) list
    let empty:('k,'v) t = []

    let remove_with_eq = fun f d k -> List.filter (fun (k',_) -> f k k' |> not) d
    let mem_with_eq = fun f d k -> List.exists (fun (k',_) -> f k k') d
    let add_with_eq = fun f d k v -> (k,v)::remove_with_eq f d k
    let get_opt_with_eq = fun f d k -> 
      match List.find_opt (fun (k',_) -> f k k') d with
      | Some (_,v) -> Some v
      | None -> None

    let remove d k = remove_with_eq (=) d k
    let mem d k = mem_with_eq (=) d k
    let add d k v = add_with_eq (=) d k v
    let get_opt d k = get_opt_with_eq (=) d k

    let find_opt = fun f d ->
      List.find_opt (fun (k,v) -> f k v) d

    let map_kv_to_v = fun f d -> List.map (fun (k,v) -> (k,f k v)) d
    let filter_map_kv_to_v f d = 
      List.filter_map 
      (fun (k,v) -> match f k v with 
      | Some nv -> Some (k,nv)
      | None -> None) 
      d
    let fold_left f e d = List.fold_left (fun e (k,v) -> (f e k v)) e d

    let of_list_with_eq = fun f d -> fold_left (fun e k v -> add_with_eq f e k v ) empty d
    let to_list_with_eq = fun f d -> List.fold_right (fun (k,v) e -> add_with_eq f e k v ) d empty
    let of_list = fun d -> of_list_with_eq (=) d
    let to_list = fun d -> to_list_with_eq (=) d
  end
