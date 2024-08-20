From Coq Require Import List.
Import ListNotations.

From Cdeque Require Import types models core.

Module D.

Equations empty {A : Type} : { d : deque A | deque_seq d = [] } :=
empty := ? T Empty.

Equations push {A : Type} (x : A) (d : deque A) :
  { d' : deque A | deque_seq d' = [x] ++ deque_seq d } :=
push x (T c) with push_chain (Ground x) c => { | ? c' := ? T c' }.

Equations inject {A : Type} (d : deque A) (x : A) :
  { d' : deque A | deque_seq d' = deque_seq d ++ [x] } :=
inject (T c) x with inject_chain c (Ground x) => { | ? c' := ? T c' }.

Equations concat {A : Type} (d1 d2 : deque A) :
  { d3 : deque A | deque_seq d3 = deque_seq d1 ++ deque_seq d2 } :=
concat (T c1) (T c2) with make_left c1 => {
  | ? Not_enough v with push_vector v (NE_chain c2) => {
    | ? NE_chain c3 := ? T c3 };
  | ? Ok_lrt tl with make_right c2 => {
    | ? Not_enough v with inject_vector (NE_chain c1) v => {
      | ? NE_chain c3 := ? T c3 };
    | ? Ok_lrt tr with chain_of_triple tl, chain_of_triple tr => {
      | ? cl, ? cr := ? T (Pair_chain cl cr) } } }.

Equations pop {A : Type} (d : deque A) :
  { o : option (A * deque A) |
    deque_seq d = match o with
    | None => []
    | Some (x, d') => [x] ++ deque_seq d'
    end } :=
pop (T (e := Is_end) Empty) := ? None;
pop (T (e := Not_end) c) with pop_green c => {
  | ? (Ground x, Semi c1) with ensure_green c1 => {
    | ? c2 := ? Some (x, T c2) } }.

Equations eject {A : Type} (d : deque A) :
  { o : option (deque A * A) |
    deque_seq d = match o with
    | None => []
    | Some (d', x) => deque_seq d' ++ [x]
    end } :=
eject (T (e := Is_end) Empty) := ? None;
eject (T (e := Not_end) c) with eject_green c => {
  | ? (Semi c1, Ground x) with ensure_green c1 => {
    | ? c2 := ? Some (T c2, x) } }.

End D.

Separate Extraction D models.