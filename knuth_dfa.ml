open! Core

type production = (char * char list) [@@deriving sexp, compare, equal]
type productions = production list [@@deriving sexp, compare, equal]

module Nfa_state = struct
  module T = struct
    type t = [`q_0 | `Prod of production] [@@deriving sexp, compare, equal]
  end
  include T
  include Comparable.Make(T)
end

module Dfa_state = struct
  module T = struct
    type t = Nfa_state.Set.t [@@deriving sexp, compare, equal]
  end
  include T
  include Comparable.Make(T)

  let to_string (state:Nfa_state.Set.t) =
    let s = Nfa_state.Set.fold state ~init:"" ~f:(fun accum state -> match state with
        | `q_0 -> accum ^ "q_0, "
        | `Prod (left,right) -> accum ^ Char.to_string left ^ " -> "  ^ (String.of_char_list right) ^ ", "
      ) in
    if Nfa_state.Set.is_empty state then s
    else String.prefix s (String.length s - 2)
  ;;
end

type grammar = Char.Set.t * Char.Set.t * productions * char [@@deriving sexp]

type nfa = Nfa_state.Set.t * Char.Set.t * (Nfa_state.t -> char -> Nfa_state.Set.t) * Nfa_state.t * Nfa_state.Set.t

type dfa = Dfa_state.Set.t * Char.Set.t * (Dfa_state.t -> char -> Dfa_state.t) * Dfa_state.t * Dfa_state.Set.t

let dot = '.';;

let q1_grammar =
  let variables = ['S'; 'T'; 'A'] |> Char.Set.of_list in
  let alphabet = ['a'; 'b'; 'c'] |> Char.Set.of_list in
  let productions = [
    ('S', ['T';'c'])
  ; ('T', ['A';'T'])
  ; ('T', ['A'])
  ; ('A', ['a';'T';'b'])
  ; ('A', ['a';'b'])
  ] in
  (variables, alphabet, productions, 'S')
;;

let q2_grammar =
  let variables = ['S'; 'E'; 'T'] |> Char.Set.of_list in
  let alphabet = ['+'; 'a'; '('; ')'; '#'] |> Char.Set.of_list in
  let productions = [
    ('S', ['E';'#'])
  ; ('E', ['E';'+';'T'])
  ; ('E', ['T'])
  ; ('T', ['a'])
  ; ('T', ['(';'E';')'])
  ] in
  (variables, alphabet, productions, 'S')
;;

let get_items (productions : productions) : production list =
  let get_item (left,right : production) : production list =
    List.range 0 (List.length right + 1)
    |> List.map ~f:(fun i ->
        (left,
         (List.sub right ~pos:0 ~len:i)
         @ [dot]
         @ (List.sub right ~pos:i ~len:(List.length right - i))
        )
      )
  in
  List.map productions ~f:get_item |> List.join
;;
let%expect_test "get_items" =
  print_s [%message (get_items [('A', ['a']); ('B', ['A';'B';'C'])] : production list)];
  [%expect {|
    ("get_items [('A', ['a']); ('B', ['A'; 'B'; 'C'])]"
     ((A (. a)) (A (a .)) (B (. A B C)) (B (A . B C)) (B (A B . C))
      (B (A B C .)))) |}]
;;



let productions_with_left productions left =
  List.filter productions ~f:(fun (l,_) -> Char.(=) l left )
;;

let symbol_after_dot prod_rhs : char option =
  match List.findi prod_rhs ~f:(fun _ c -> Char.(=) dot c) with
  | None -> None
  | Some (i,_) -> List.nth prod_rhs (i+1)
;;
let%expect_test "symbol_after_dot" =
  print_s [%message (symbol_after_dot ['.';'a';'b'] : char option)];
  print_s [%message (symbol_after_dot ['a';'.';'b'] : char option)];
  print_s [%message (symbol_after_dot ['a';'b';'.'] : char option)];
  [%expect {|
    ("symbol_after_dot ['.'; 'a'; 'b']" (a))
    ("symbol_after_dot ['a'; '.'; 'b']" (b))
    ("symbol_after_dot ['a'; 'b'; '.']" ()) |}]
;;

let move_dot_exn prod_rhs  =
  let idx,_ = List.findi prod_rhs ~f:(fun _ c -> Char.(=) dot c) |> Option.value_exn in
  (List.sub prod_rhs ~pos:0 ~len:idx) @ [List.nth_exn prod_rhs (idx + 1)] @ [dot] @ (List.sub prod_rhs ~pos:(idx+2) ~len:(List.length prod_rhs - idx - 2))
;;
let%expect_test "move_dot_exn" =
  print_s [%message (move_dot_exn ['.';'a';'b'] : char list)];
  print_s [%message (move_dot_exn ['a';'.';'b'] : char list)];
  [%expect {|
    ("move_dot_exn ['.'; 'a'; 'b']" (a . b))
    ("move_dot_exn ['a'; '.'; 'b']" (a b .)) |}]
;;

let to_knuth_nfa (variables, sigma, productions, start : grammar) : nfa =
  let states = `q_0 :: (get_items productions |> List.map ~f:(fun p -> `Prod p)) |> Nfa_state.Set.of_list in
  let alphabet = Char.Set.union sigma variables in
  let final_states = states in
  let delta (state : Nfa_state.t) (letter: char) : Dfa_state.t =
    match state, letter with
    | `q_0, '?' -> (* using ? as epsilon *)
      productions_with_left productions start
      |> List.map ~f:(fun (l,r) -> `Prod (l, dot :: r))
      |> Nfa_state.Set.of_list
    | `Prod prod, '?' ->
      let _, right = prod in
      (match symbol_after_dot right with
       | None -> Nfa_state.Set.empty
       | Some beta -> productions_with_left productions beta |> List.map ~f:(fun (l,r) -> `Prod (l, dot :: r)) |> Nfa_state.Set.of_list
      )
    | `Prod prod, letter ->
      let left, right = prod in
      (match symbol_after_dot right with
       | None -> Nfa_state.Set.empty
       | Some x -> if Char.(=) x letter then
           [`Prod (left, move_dot_exn right)] |> Nfa_state.Set.of_list
         else Nfa_state.Set.empty
      )
    | _, _ -> Nfa_state.Set.empty
  in
  (states, alphabet, delta, `q_0, final_states)
;;
let%expect_test "q2 nfa" =
  let states, alphabet, _, _, _ = to_knuth_nfa q2_grammar in
  print_s [%message (alphabet: Char.Set.t)];
  Set.iter states ~f:(fun state -> print_s [%message (state : Nfa_state.t)]);
  [%expect {|
    (alphabet (# "(" ")" + E S T a))
    (state q_0)
    (state (Prod (E (. E + T))))
    (state (Prod (E (. T))))
    (state (Prod (E (E + . T))))
    (state (Prod (E (E + T .))))
    (state (Prod (E (E . + T))))
    (state (Prod (E (T .))))
    (state (Prod (S (. E #))))
    (state (Prod (S (E # .))))
    (state (Prod (S (E . #))))
    (state (Prod (T ("(" . E ")"))))
    (state (Prod (T ("(" E ")" .))))
    (state (Prod (T ("(" E . ")"))))
    (state (Prod (T (. "(" E ")"))))
    (state (Prod (T (. a))))
    (state (Prod (T (a .)))) |}]
;;

let epsilon_closure (delta : Nfa_state.t -> char -> Dfa_state.t) state =
  let rec epsilon_closure states_to_be_processed acc =
    match states_to_be_processed with
    | [] -> acc
    | state :: other_states ->
      let acc = Set.add acc state in
      let epsilon_reachable = delta state '?'
                              |> Set.filter ~f:(fun state ->
                                  not (Set.mem acc state)
                                )
                              |> Set.to_list
      in
      epsilon_closure (other_states @ epsilon_reachable) acc
  in
  epsilon_closure [state] Nfa_state.Set.empty
;;

let to_knuth_dfa (grammar : grammar) : dfa =
  let _, nfa_alphabet, nfa_delta, nfa_start, _ = to_knuth_nfa grammar in
  let epsilon_closure = epsilon_closure nfa_delta in
  let initial_state = epsilon_closure nfa_start in
  let dfa_delta (dfa_state : Dfa_state.t) letter =
    Set.to_list dfa_state
    |> List.map ~f:(fun nfa_state -> nfa_delta nfa_state letter)
    |> List.fold ~init:Nfa_state.Set.empty ~f:Set.union
    |> Set.to_list
    |> List.map ~f:(epsilon_closure)
    |> List.fold ~init:Nfa_state.Set.empty ~f:Set.union
  in
  let rec produce_all_states states_to_be_processed acc =
    match states_to_be_processed with
    | [] -> acc
    | dfa_state :: more_states ->
      let acc = Set.add acc dfa_state in
      let neighbors = nfa_alphabet |> Set.to_list
                      |> List.map ~f:(fun letter ->
                          dfa_delta dfa_state letter
                        )
                      |> List.filter ~f:(fun neighbor ->
                          not (Set.mem acc neighbor)
                        )
      in
      produce_all_states (more_states @ neighbors) acc
  in
  let dfa_states = produce_all_states [initial_state] Dfa_state.Set.empty in
  (dfa_states, nfa_alphabet, dfa_delta, initial_state, dfa_states)
;;

let print_dfa (states: Dfa_state.Set.t) (alphabet: Char.Set.t) delta =
  let states = Set.to_list states in
  print_s [%message "STATES:"];
  List.iteri states ~f:(fun i state ->
      printf "%d : {%s}\n" i (Dfa_state.to_string state);
    );
  print_s [%message "TRANSITIONS:"];
  List.iteri states ~f:(fun i in_state ->
      Set.iter alphabet ~f:(fun c ->
          let out_state = delta in_state c in
          let in_state = i in
          let out_state,_ = List.findi states ~f:(fun _ state -> Dfa_state.equal state out_state) |> Option.value_exn in
          if in_state = 0 || out_state = 0 then () else
            printf "%d --%c--> %d\n" in_state c out_state
        )
    )
;;

let print_dfa_gv (states: Dfa_state.Set.t) (alphabet: Char.Set.t) delta =
  print_endline "digraph G {";
  print_endline "rankdir = LR;";
  let states = Set.to_list states in
  List.iteri states ~f:(fun i state ->
      if Set.is_empty state then ()
      else printf "node [shape = doublecircle, label=\"%s\", fontsize=12]%d;\n" (
          Dfa_state.to_string state
          |> String.split ~on:','
          |> List.map ~f:String.strip
          |> String.concat ~sep:"\\n"
        ) i;
    );
  print_endline "node [shape = point]qi;";
  print_endline "qi -> 1;";
  List.iteri states ~f:(fun i in_state ->
      Set.iter alphabet ~f:(fun c ->
          let out_state = delta in_state c in
          let out_state,_ = List.findi states ~f:(fun _ state -> Dfa_state.equal state out_state) |> Option.value_exn in
          if i = 0 || out_state = 0 then ()
          else printf "%d -> %d[ label = \"%c\" ];\n" i out_state c
        )
    );
  print_endline "}"
;;

let%expect_test "q1_dfa" =
  let states, alphabet, delta, _, _ = to_knuth_dfa q1_grammar in
  print_s [%message (alphabet: Char.Set.t)];
  print_dfa states alphabet delta;
  print_s [%message "GV FILE:"];
  print_dfa_gv states alphabet delta;
  [%expect {|
    (alphabet (A S T a b c))
    STATES:
    0 : {}
    1 : {q_0, A -> .aTb, A -> .ab, S -> .Tc, T -> .A, T -> .AT}
    2 : {A -> .aTb, A -> .ab, A -> a.Tb, A -> a.b, T -> .A, T -> .AT}
    3 : {A -> .aTb, A -> .ab, T -> .A, T -> .AT, T -> A., T -> A.T}
    4 : {A -> aT.b}
    5 : {A -> aTb.}
    6 : {A -> ab.}
    7 : {S -> T.c}
    8 : {S -> Tc.}
    9 : {T -> AT.}
    TRANSITIONS:
    1 --A--> 3
    1 --T--> 7
    1 --a--> 2
    2 --A--> 3
    2 --T--> 4
    2 --a--> 2
    2 --b--> 6
    3 --A--> 3
    3 --T--> 9
    3 --a--> 2
    4 --b--> 5
    7 --c--> 8
    "GV FILE:"
    digraph G {
    rankdir = LR;
    node [shape = doublecircle, label="q_0\nA -> .aTb\nA -> .ab\nS -> .Tc\nT -> .A\nT -> .AT", fontsize=12]1;
    node [shape = doublecircle, label="A -> .aTb\nA -> .ab\nA -> a.Tb\nA -> a.b\nT -> .A\nT -> .AT", fontsize=12]2;
    node [shape = doublecircle, label="A -> .aTb\nA -> .ab\nT -> .A\nT -> .AT\nT -> A.\nT -> A.T", fontsize=12]3;
    node [shape = doublecircle, label="A -> aT.b", fontsize=12]4;
    node [shape = doublecircle, label="A -> aTb.", fontsize=12]5;
    node [shape = doublecircle, label="A -> ab.", fontsize=12]6;
    node [shape = doublecircle, label="S -> T.c", fontsize=12]7;
    node [shape = doublecircle, label="S -> Tc.", fontsize=12]8;
    node [shape = doublecircle, label="T -> AT.", fontsize=12]9;
    node [shape = point]qi;
    qi -> 1;
    1 -> 3[ label = "A" ];
    1 -> 7[ label = "T" ];
    1 -> 2[ label = "a" ];
    2 -> 3[ label = "A" ];
    2 -> 4[ label = "T" ];
    2 -> 2[ label = "a" ];
    2 -> 6[ label = "b" ];
    3 -> 3[ label = "A" ];
    3 -> 9[ label = "T" ];
    3 -> 2[ label = "a" ];
    4 -> 5[ label = "b" ];
    7 -> 8[ label = "c" ];
    } |}]
;;

let%expect_test "q2_dfa" =
  let states, alphabet, delta, _, _ = to_knuth_dfa q2_grammar in
  print_s [%message (alphabet: Char.Set.t)];
  print_dfa states alphabet delta;
  print_s [%message "GV FILE:"];
  print_dfa_gv states alphabet delta;
  [%expect {|
    (alphabet (# "(" ")" + E S T a))
    STATES:
    0 : {}
    1 : {q_0, E -> .E+T, E -> .T, S -> .E#, T -> .(E), T -> .a}
    2 : {E -> .E+T, E -> .T, T -> (.E), T -> .(E), T -> .a}
    3 : {E -> E+.T, T -> .(E), T -> .a}
    4 : {E -> E+T.}
    5 : {E -> E.+T, S -> E.#}
    6 : {E -> E.+T, T -> (E.)}
    7 : {E -> T.}
    8 : {S -> E#.}
    9 : {T -> (E).}
    10 : {T -> a.}
    TRANSITIONS:
    1 --(--> 2
    1 --E--> 5
    1 --T--> 7
    1 --a--> 10
    2 --(--> 2
    2 --E--> 6
    2 --T--> 7
    2 --a--> 10
    3 --(--> 2
    3 --T--> 4
    3 --a--> 10
    5 --#--> 8
    5 --+--> 3
    6 --)--> 9
    6 --+--> 3
    "GV FILE:"
    digraph G {
    rankdir = LR;
    node [shape = doublecircle, label="q_0\nE -> .E+T\nE -> .T\nS -> .E#\nT -> .(E)\nT -> .a", fontsize=12]1;
    node [shape = doublecircle, label="E -> .E+T\nE -> .T\nT -> (.E)\nT -> .(E)\nT -> .a", fontsize=12]2;
    node [shape = doublecircle, label="E -> E+.T\nT -> .(E)\nT -> .a", fontsize=12]3;
    node [shape = doublecircle, label="E -> E+T.", fontsize=12]4;
    node [shape = doublecircle, label="E -> E.+T\nS -> E.#", fontsize=12]5;
    node [shape = doublecircle, label="E -> E.+T\nT -> (E.)", fontsize=12]6;
    node [shape = doublecircle, label="E -> T.", fontsize=12]7;
    node [shape = doublecircle, label="S -> E#.", fontsize=12]8;
    node [shape = doublecircle, label="T -> (E).", fontsize=12]9;
    node [shape = doublecircle, label="T -> a.", fontsize=12]10;
    node [shape = point]qi;
    qi -> 1;
    1 -> 2[ label = "(" ];
    1 -> 5[ label = "E" ];
    1 -> 7[ label = "T" ];
    1 -> 10[ label = "a" ];
    2 -> 2[ label = "(" ];
    2 -> 6[ label = "E" ];
    2 -> 7[ label = "T" ];
    2 -> 10[ label = "a" ];
    3 -> 2[ label = "(" ];
    3 -> 4[ label = "T" ];
    3 -> 10[ label = "a" ];
    5 -> 8[ label = "#" ];
    5 -> 3[ label = "+" ];
    6 -> 9[ label = ")" ];
    6 -> 3[ label = "+" ];
    } |}]
;;
