From Coq Require Import List.
Import ListNotations.

From Deque Require Import types models core.

Module D.

Equations empty {A} : { d : deque A | deque_seq d = [] } :=
empty := ? T Empty.

Equations push {A} (x : A) (d : deque A) :
  { d' : deque A | deque_seq d' = [x] ++ deque_seq d } :=
push x (T cd) with push_cdeque (ST_ground x) cd => { | ? cd' := ? T cd' }.

Equations inject {A} (d : deque A) (x : A) :
  { d' : deque A | deque_seq d' = deque_seq d ++ [x] } :=
inject (T cd) x with inject_cdeque cd (ST_ground x) => { | ? cd' := ? T cd' }.

Equations concat {A} (d1 d2 : deque A) :
  { d : deque A | deque_seq d = deque_seq d1 ++ deque_seq d2 } :=
concat (T cd1) (T cd2) with make_left cd1 => {
  | ? ZeroSix v with push_vector v cd2 => {
    | ? cd := ? T cd };
  | ? Ok pl with make_right cd2 => {
    | ? ZeroSix v with inject_vector cd1 v => {
      | ? cd := ? T cd };
    | ? Ok pr := ? T (NonEmpty (Pair_green pl pr)) } }.

Equations pop {A} (d : deque A) :
  { o : option (A * deque A) |
    match o with
    | None => []
    | Some (x, d') => [x] ++ deque_seq d'
    end = deque_seq d } :=
pop (T Empty) := ? None;
pop (T (NonEmpty cd)) with pop_green cd => {
  | ? (ST_ground x, sd) with regular_of_semi sd => {
    | ? d' := ? Some (x, d') } }.

Equations eject {A} (d : deque A) :
  { o : option (deque A * A) |
    match o with
    | None => []
    | Some (d', x) => deque_seq d' ++ [x]
    end = deque_seq d } :=
eject (T Empty) := ? None;
eject (T (NonEmpty cd)) with eject_green cd => {
  | ? (sd, ST_ground x) with regular_of_semi sd => {
    | ? d' := ? Some (d', x) } }.

End D.

Separate Extraction D models.