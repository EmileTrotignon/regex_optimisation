open Printf

module Letter = struct
  type t = A | B | C | D

  let to_char l = match l with A -> 'a' | B -> 'b' | C -> 'c' | D -> 'd'

  let to_string l = match l with A -> "a" | B -> "b" | C -> "c" | D -> "d"
end

module rec Regex : sig
  type t =
    | Empty
    | Epsilon
    | Letter of Letter.t
    | Star of t
    | Concat of t list
    | Sum of RegexSet.t

  val compare : t -> t -> int

  val to_string : t -> string

  val star : t -> t

  val concat : t list -> t

  val sum : RegexSet.t -> t

  val sum_from_list : t list -> t

  val letter : Letter.t -> t
end = struct
  type t =
    | Empty
    | Epsilon
    | Letter of Letter.t
    | Star of t
    | Concat of t list
    | Sum of RegexSet.t

  let empty = Empty

  let epsilon = Epsilon

  let compare (r1 : t) (r2 : t) = compare r1 r2

  let rec to_string r : string =
    let rec aux_sum set =
      if RegexSet.cardinal set >= 2 then
        let ele = RegexSet.choose set in
        "(" ^ to_string ele ^ ")+" ^ aux_sum (RegexSet.remove ele set)
      else if RegexSet.cardinal set = 1 then
        "(" ^ to_string (RegexSet.choose set) ^ ")"
      else ""
    in
    let aux_concat lr = List.fold_left ( ^ ) "" (List.map to_string lr) in
    match r with
    | Empty -> ""
    | Epsilon -> "ε"
    | Letter l -> Letter.to_string l
    | Star r -> "(" ^ to_string r ^ ")*"
    | Sum set -> aux_sum set
    | Concat lr -> aux_concat lr

  let letter l = Letter l

  let rec star r =
    match r with
    | Star r' -> r'
    | Sum set when RegexSet.mem Epsilon set ->
        Star (sum (RegexSet.remove Epsilon set))
    | _ -> Star r

  and concat rl =
    let rec opti rl =
      match rl with
      | [] -> []
      | Concat rl' :: rs -> opti rl' @ rs
      | [r] -> [r]
      | Epsilon :: rs -> opti rs
      | r1 :: r2 :: rs -> (
        match (r1, r2) with
        | Sum set1, Star (Sum set2)
          when RegexSet.mem Epsilon set1
               && RegexSet.subset (RegexSet.remove Epsilon set1) set2 ->
            opti (r2 :: rs)
        | Star (Sum set2), Sum set1
          when RegexSet.mem Epsilon set1
               && RegexSet.subset (RegexSet.remove Epsilon set1) set2 ->
            opti (r1 :: rs)
        | Sum set, Star r
          when RegexSet.mem Epsilon set
               && RegexSet.cardinal set = 2
               && RegexSet.mem r set ->
            opti (r2 :: rs)
        | Star r, Sum set
          when RegexSet.mem Epsilon set
               && RegexSet.cardinal set = 2
               && RegexSet.mem r set ->
            opti (r1 :: rs)
        | _, _ -> r1 :: opti (r2 :: rs) )
    in
    let opti_rl = opti rl in
    match (rl, opti_rl) with
    | r :: rs, [] -> Epsilon
    | [], _ -> Empty
    | _, [r] -> r
    | _, _ -> Concat opti_rl

  and sum_from_list (rl : t list) : t = sum (RegexSet.of_list rl)

  and sum set =
    let run_all_opti set =
      let opti_1 set =
        let is_ele_opti ele =
          match ele with
          | Concat [Star s; s'; r] when s = s' && RegexSet.mem r set -> true
          | Concat [s; Star s'; r] when s = s' && RegexSet.mem r set -> true
          | _ -> false
        in
        match RegexSet.find_first_opt is_ele_opti set with
        | Some (Concat [Star s; s'; r]) ->
            Some
              (RegexSet.add
                 (concat [star s; r])
                 (RegexSet.remove r
                    (RegexSet.remove (Concat [Star s; s'; r]) set)))
        | None -> None
        | _ -> assert false
      in
      let opti_2 set =
        let is_ele_opti ele = match ele with Star r -> true | _ -> false in
        match RegexSet.find_first_opt is_ele_opti set with
        | Some (Star r) ->
            Some (RegexSet.remove Epsilon (RegexSet.remove r set))
        | Some r -> assert false
        | None -> None
      in
      let set' = ref set in
      let b = ref true in
      while !b do
        b := false ;
        match opti_1 !set' with
        | Some set'' ->
            (set' := set'' ;
            b := true)
        | None -> (
            () ;
            match opti_2 !set' with
            | Some set'' ->
                (set' := set'' ;
                b := true)
            | None -> () )
      done ;
      !set'
    in
    let set =
      List.fold_left RegexSet.union RegexSet.empty
        (List.map
           (fun ele ->
             match ele with Sum set -> set | _ -> RegexSet.singleton ele )
           (RegexSet.elements set))
    in
    let set = RegexSet.remove Empty set in
    if RegexSet.is_empty set then Empty
    else
      let set = run_all_opti set in
      if RegexSet.cardinal set = 1 then RegexSet.choose set else Sum set
end

and RegexSet : (Set.S with type elt = Regex.t) = Set.Make (Regex)

module Int = struct
  type t = int

  let compare = compare
end

module SetInt = Set.Make (Int)

type automata = int * int * SetInt.t * (int -> Letter.t -> int option)

let exemple =
  Letter.
    ( 2
    , 0
    , SetInt.singleton 1
    , fun n l ->
        match n with
        | 0 -> ( match l with A -> Some 0 | B -> Some 1 | C | D -> None )
        | 1 -> ( match l with A | B -> None | C -> Some 0 | D -> Some 1 )
        | _ -> failwith "not a state" )

let ( +% ) r1 r2 =
  if String.compare r1 "" = 0 then r2
  else if String.compare r2 "" = 0 then r1
  else if String.compare r1 r2 != 0 then "(" ^ r1 ^ "+" ^ r2 ^ ")"
  else r1

let star r =
  match String.length r with 0 -> "" | 1 -> r ^ "*" | _ -> "(" ^ r ^ ")*"

let rec sum ll =
  match ll with
  | [] -> ""
  | x :: xs -> ( match xs with [] -> x | _ -> x +% sum xs )

let yamada a =
  Regex.(
    match a with n_state, q0, final_states, transition_fun ->
      let good_letters p q =
        sum
          (RegexSet.of_list
             Letter.(
               (if transition_fun p A = Some q then [letter A] else [])
               @ (if transition_fun p B = Some q then [letter B] else [])
               @ (if transition_fun p C = Some q then [letter C] else [])
               @ (if transition_fun p D = Some q then [letter D] else [])
               @ if p = q then [Epsilon] else []))
      in
      let l = Array.make_matrix n_state n_state Empty in
      for p = 0 to n_state - 1 do
        for q = 0 to n_state - 1 do
          l.(p).(q) <- good_letters p q ;
          printf "k = -1, p = %d, q = %d\nr = %s\n\n" p q (to_string l.(p).(q))
        done
      done ;
      for k = 0 to n_state - 1 do
        for p = 0 to n_state - 1 do
          for q = 0 to n_state - 1 do
            let nlpq =
              sum_from_list
                [l.(p).(q); concat [l.(p).(k); star l.(k).(k); l.(k).(q)]]
              (*concat
                [ sum_from_list [l.(p).(q); l.(p).(k)]
                ; star l.(k).(k)
                ; l.(k).(q) ]*)
            in
            printf "k = %d, p = %d, q = %d\nold : %s\nnew : %s\n\n" k p q
              (to_string l.(p).(q))
              (to_string nlpq) ;
            l.(p).(q) <- nlpq
          done
        done
      done ;
      let r = ref Empty in
      let add q =
        printf "q = %d\nold : %s\n\n" q (to_string !r) ;
        r :=
          if q = q0 then sum_from_list [!r; Epsilon; l.(q0).(q0)]
          else sum_from_list [!r; l.(q0).(q)]
      in
      SetInt.iter add final_states ;
      to_string !r)

;;
print_endline (yamada exemple)
