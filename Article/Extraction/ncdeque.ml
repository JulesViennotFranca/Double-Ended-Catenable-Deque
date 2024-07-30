open Datatypes
open Nat

type green_hue =
| SomeGreen
| NoGreen

type yellow_hue =
| SomeYellow
| NoYellow

type red_hue =
| SomeRed
| NoRed

type color =
| Mix of green_hue * yellow_hue * red_hue

type 'a prodN =
| Coq_prodZ of 'a
| Coq_prodS of nat * 'a prodN * 'a prodN

type 'a buffer =
| B0
| B1 of 'a prodN
| B2 of green_hue * yellow_hue * 'a prodN * 'a prodN
| B3 of green_hue * yellow_hue * 'a prodN * 'a prodN * 'a prodN
| B4 of 'a prodN * 'a prodN * 'a prodN * 'a prodN
| B5 of 'a prodN * 'a prodN * 'a prodN * 'a prodN * 'a prodN

type 'a yellow_buffer =
| Yellowish of green_hue * yellow_hue * 'a buffer

type 'a any_buffer =
| Any of color * 'a buffer

type packet_color =
| PCGreen
| PCYellow of green_hue * yellow_hue * green_hue * yellow_hue
| PCRed of color * color

type 'a packet =
| Hole
| Triple of nat * nat * nat * nat * yellow_hue * color * color * color
   * 'a buffer * 'a packet * 'a buffer * packet_color

(** val power2 : nat -> nat **)

let rec power2 = function
| O -> S O
| S n0 -> let p = power2 n0 in add p p

type cdeque_color =
| CCGreen of green_hue * red_hue
| CCYellow
| CCRed

type 'a cdeque =
| Small of nat * color * 'a buffer
| Big of nat * nat * nat * nat * nat * color * color * 'a packet * 'a cdeque
   * cdeque_color

(** val size_option : 'a1 option -> nat **)

let size_option = function
| Some _ -> S O
| None -> O

type 'a decompose =
| Underflow of 'a prodN option
| Ok of nat * 'a buffer
| Overflow of nat * 'a buffer * 'a prodN

type 'a sandwich =
| Alone of 'a prodN option
| Sandwich of nat * color * 'a prodN * 'a buffer * 'a prodN

type 'a deque =
| T of green_hue * yellow_hue * 'a cdeque

(** val prodN_seq : nat -> 'a1 prodN -> 'a1 list **)

let rec prodN_seq n p =
  match n with
  | O ->
    (match p with
     | Coq_prodZ y -> Coq_cons (y, Coq_nil)
     | Coq_prodS (_, _, _) -> assert false (* absurd case *))
  | S n0 ->
    (match p with
     | Coq_prodZ _ -> assert false (* absurd case *)
     | Coq_prodS (_, p0, p1) -> app (prodN_seq n0 p0) (prodN_seq n0 p1))

(** val buffer_seq : nat -> nat -> color -> 'a1 buffer -> 'a1 list **)

let buffer_seq lvl _ _ = function
| B0 -> Coq_nil
| B1 p -> prodN_seq lvl p
| B2 (_, _, p, p0) -> app (prodN_seq lvl p) (prodN_seq lvl p0)
| B3 (_, _, p, p0, p1) ->
  app (prodN_seq lvl p) (app (prodN_seq lvl p0) (prodN_seq lvl p1))
| B4 (p, p0, p1, p2) ->
  app (prodN_seq lvl p)
    (app (prodN_seq lvl p0) (app (prodN_seq lvl p1) (prodN_seq lvl p2)))
| B5 (p, p0, p1, p2, p3) ->
  app (prodN_seq lvl p)
    (app (prodN_seq lvl p0)
      (app (prodN_seq lvl p1) (app (prodN_seq lvl p2) (prodN_seq lvl p3))))

(** val packet_front_seq :
    nat -> nat -> nat -> color -> 'a1 packet -> 'a1 list **)

let rec packet_front_seq lvl _ _ _ = function
| Hole -> Coq_nil
| Triple (len, psize, pktsize, _, y, c1, _, _, b, p0, _, _) ->
  app (buffer_seq lvl psize c1 b)
    (packet_front_seq (S lvl) len pktsize (Mix (NoGreen, y, NoRed)) p0)

(** val packet_rear_seq :
    nat -> nat -> nat -> color -> 'a1 packet -> 'a1 list **)

let rec packet_rear_seq lvl _ _ _ = function
| Hole -> Coq_nil
| Triple (len, _, pktsize, ssize, y, _, c2, _, _, p0, b, _) ->
  app (packet_rear_seq (S lvl) len pktsize (Mix (NoGreen, y, NoRed)) p0)
    (buffer_seq lvl ssize c2 b)

(** val cdeque_seq : nat -> nat -> color -> 'a1 cdeque -> 'a1 list **)

let rec cdeque_seq lvl _ _ = function
| Small (size, c0, b) -> buffer_seq lvl size c0 b
| Big (len, pktsize, nlvl, nsize, _, c1, c2, p, c0, _) ->
  app (packet_front_seq lvl len pktsize c1 p)
    (app (cdeque_seq nlvl nsize c2 c0) (packet_rear_seq lvl len pktsize c1 p))

(** val deque_seq : nat -> 'a1 deque -> 'a1 list **)

let deque_seq size = function
| T (g, y, c) -> cdeque_seq O size (Mix (g, y, NoRed)) c

(** val map_deque :
    (nat -> 'a1 -> 'a2 list) -> nat -> nat -> 'a1 deque -> 'a2 list **)

let map_deque f lvl q d =
  let prodN_seq0 =
    let rec prodN_seq0 lvlt _ = function
    | Coq_prodZ z -> f lvlt z
    | Coq_prodS (n, p1, p2) ->
      app (prodN_seq0 lvlt n p1) (prodN_seq0 lvlt n p2)
    in prodN_seq0
  in
  let buffer_seq0 = fun lvlt lvlp _ _ b ->
    match b with
    | B0 -> Coq_nil
    | B1 p1 -> prodN_seq0 lvlt lvlp p1
    | B2 (_, _, p1, p2) ->
      app (prodN_seq0 lvlt lvlp p1) (prodN_seq0 lvlt lvlp p2)
    | B3 (_, _, p1, p2, p3) ->
      app (prodN_seq0 lvlt lvlp p1)
        (app (prodN_seq0 lvlt lvlp p2) (prodN_seq0 lvlt lvlp p3))
    | B4 (p1, p2, p3, p4) ->
      app (prodN_seq0 lvlt lvlp p1)
        (app (prodN_seq0 lvlt lvlp p2)
          (app (prodN_seq0 lvlt lvlp p3) (prodN_seq0 lvlt lvlp p4)))
    | B5 (p1, p2, p3, p4, p5) ->
      app (prodN_seq0 lvlt lvlp p1)
        (app (prodN_seq0 lvlt lvlp p2)
          (app (prodN_seq0 lvlt lvlp p3)
            (app (prodN_seq0 lvlt lvlp p4) (prodN_seq0 lvlt lvlp p5))))
  in
  let packet_front_seq0 =
    let rec packet_front_seq0 lvlt lvlp _ _ _ = function
    | Hole -> Coq_nil
    | Triple (len0, psize, pktsize, _, y, c1, _, _, p, pkt0, _, _) ->
      app (buffer_seq0 lvlt lvlp psize c1 p)
        (packet_front_seq0 lvlt (S lvlp) len0 pktsize (Mix (NoGreen, y,
          NoRed)) pkt0)
    in packet_front_seq0
  in
  let packet_rear_seq0 =
    let rec packet_rear_seq0 lvlt lvlp _ _ _ = function
    | Hole -> Coq_nil
    | Triple (len0, _, pktsize, ssize, y, _, c2, _, _, pkt0, s, _) ->
      app
        (packet_rear_seq0 lvlt (S lvlp) len0 pktsize (Mix (NoGreen, y,
          NoRed)) pkt0) (buffer_seq0 lvlt lvlp ssize c2 s)
    in packet_rear_seq0
  in
  let cdeque_seq0 =
    let rec cdeque_seq0 lvlt lvlp _ _ = function
    | Small (size0, c0, b) -> buffer_seq0 lvlt lvlp size0 c0 b
    | Big (len, pktsize, nlvl, nsize, _, c1, c2, pkt, cd0, _) ->
      app (packet_front_seq0 lvlt lvlp len pktsize c1 pkt)
        (app (cdeque_seq0 lvlt nlvl nsize c2 cd0)
          (packet_rear_seq0 lvlt lvlp len pktsize c1 pkt))
    in cdeque_seq0
  in
  let T (g, y, cd) = d in cdeque_seq0 lvl O q (Mix (g, y, NoRed)) cd

(** val cempty : nat -> 'a1 cdeque **)

let cempty _ =
  Small (O, (Mix (NoGreen, NoYellow, SomeRed)), B0)

(** val empty : 'a1 deque **)

let empty =
  T (SomeGreen, NoYellow, (cempty O))

(** val green_push : nat -> nat -> 'a1 prodN -> 'a1 buffer -> 'a1 buffer **)

let green_push _ _ x = function
| B2 (_, _, p, p0) -> B3 (NoGreen, SomeYellow, x, p, p0)
| B3 (_, _, p, p0, p1) -> B4 (x, p, p0, p1)
| _ -> assert false (* absurd case *)

(** val green_inject : nat -> nat -> 'a1 buffer -> 'a1 prodN -> 'a1 buffer **)

let green_inject _ _ b x =
  match b with
  | B2 (_, _, p, p0) -> B3 (NoGreen, SomeYellow, p, p0, x)
  | B3 (_, _, p, p0, p1) -> B4 (p, p0, p1, x)
  | _ -> assert false (* absurd case *)

(** val green_pop_obligations_obligation_2 : green_hue **)

let green_pop_obligations_obligation_2 =
  SomeGreen

(** val green_pop_obligations_obligation_3 : yellow_hue **)

let green_pop_obligations_obligation_3 =
  SomeYellow

(** val green_pop :
    nat -> nat -> 'a1 buffer -> ('a1 prodN, 'a1 yellow_buffer) prod **)

let green_pop _ _ = function
| B2 (_, _, p, p0) -> Coq_pair (p, (Yellowish (NoGreen, SomeYellow, (B1 p0))))
| B3 (_, _, p, p0, p1) ->
  Coq_pair (p, (Yellowish (green_pop_obligations_obligation_2,
    green_pop_obligations_obligation_3, (B2
    (green_pop_obligations_obligation_2, green_pop_obligations_obligation_3,
    p0, p1)))))
| _ -> assert false (* absurd case *)

(** val green_eject_obligations_obligation_2 : green_hue **)

let green_eject_obligations_obligation_2 =
  SomeGreen

(** val green_eject_obligations_obligation_3 : yellow_hue **)

let green_eject_obligations_obligation_3 =
  SomeYellow

(** val green_eject :
    nat -> nat -> 'a1 buffer -> ('a1 yellow_buffer, 'a1 prodN) prod **)

let green_eject _ _ = function
| B2 (_, _, p, p0) -> Coq_pair ((Yellowish (NoGreen, SomeYellow, (B1 p))), p0)
| B3 (_, _, p, p0, p1) ->
  Coq_pair ((Yellowish (green_eject_obligations_obligation_2,
    green_eject_obligations_obligation_3, (B2
    (green_eject_obligations_obligation_2,
    green_eject_obligations_obligation_3, p, p0)))), p1)
| _ -> assert false (* absurd case *)

(** val yellow_push_obligations_obligation_1 : green_hue **)

let yellow_push_obligations_obligation_1 =
  SomeGreen

(** val yellow_push_obligations_obligation_2 : yellow_hue **)

let yellow_push_obligations_obligation_2 =
  SomeYellow

(** val yellow_push_obligations_obligation_4 : green_hue -> green_hue **)

let yellow_push_obligations_obligation_4 g0 =
  g0

(** val yellow_push_obligations_obligation_5 : yellow_hue -> yellow_hue **)

let yellow_push_obligations_obligation_5 y0 =
  y0

(** val yellow_push :
    nat -> nat -> 'a1 prodN -> 'a1 yellow_buffer -> 'a1 any_buffer **)

let yellow_push _ _ x = function
| Yellowish (_, _, b0) ->
  (match b0 with
   | B1 p ->
     Any ((Mix (yellow_push_obligations_obligation_1,
       yellow_push_obligations_obligation_2, NoRed)), (B2
       (yellow_push_obligations_obligation_1,
       yellow_push_obligations_obligation_2, x, p)))
   | B2 (g, y, p, p0) ->
     Any ((Mix ((yellow_push_obligations_obligation_4 g),
       (yellow_push_obligations_obligation_5 y), NoRed)), (B3
       ((yellow_push_obligations_obligation_4 g),
       (yellow_push_obligations_obligation_5 y), x, p, p0)))
   | B3 (_, _, p, p0, p1) ->
     Any ((Mix (NoGreen, SomeYellow, NoRed)), (B4 (x, p, p0, p1)))
   | B4 (p, p0, p1, p2) ->
     Any ((Mix (NoGreen, NoYellow, SomeRed)), (B5 (x, p, p0, p1, p2)))
   | _ -> assert false (* absurd case *))

(** val yellow_inject_obligations_obligation_1 : green_hue **)

let yellow_inject_obligations_obligation_1 =
  SomeGreen

(** val yellow_inject_obligations_obligation_2 : yellow_hue **)

let yellow_inject_obligations_obligation_2 =
  SomeYellow

(** val yellow_inject_obligations_obligation_4 : green_hue -> green_hue **)

let yellow_inject_obligations_obligation_4 g0 =
  g0

(** val yellow_inject_obligations_obligation_5 : yellow_hue -> yellow_hue **)

let yellow_inject_obligations_obligation_5 y0 =
  y0

(** val yellow_inject :
    nat -> nat -> 'a1 yellow_buffer -> 'a1 prodN -> 'a1 any_buffer **)

let yellow_inject _ _ b x =
  let Yellowish (_, _, b0) = b in
  (match b0 with
   | B1 p ->
     Any ((Mix (yellow_inject_obligations_obligation_1,
       yellow_inject_obligations_obligation_2, NoRed)), (B2
       (yellow_inject_obligations_obligation_1,
       yellow_inject_obligations_obligation_2, p, x)))
   | B2 (g, y, p, p0) ->
     Any ((Mix ((yellow_inject_obligations_obligation_4 g),
       (yellow_inject_obligations_obligation_5 y), NoRed)), (B3
       ((yellow_inject_obligations_obligation_4 g),
       (yellow_inject_obligations_obligation_5 y), p, p0, x)))
   | B3 (_, _, p, p0, p1) ->
     Any ((Mix (NoGreen, SomeYellow, NoRed)), (B4 (p, p0, p1, x)))
   | B4 (p, p0, p1, p2) ->
     Any ((Mix (NoGreen, NoYellow, SomeRed)), (B5 (p, p0, p1, p2, x)))
   | _ -> assert false (* absurd case *))

(** val yellow_pop_obligations_obligation_3 : green_hue -> green_hue **)

let yellow_pop_obligations_obligation_3 g1 =
  g1

(** val yellow_pop_obligations_obligation_4 : yellow_hue -> yellow_hue **)

let yellow_pop_obligations_obligation_4 y1 =
  y1

(** val yellow_pop_obligations_obligation_6 : green_hue **)

let yellow_pop_obligations_obligation_6 =
  SomeGreen

(** val yellow_pop_obligations_obligation_7 : yellow_hue **)

let yellow_pop_obligations_obligation_7 =
  SomeYellow

(** val yellow_pop :
    nat -> nat -> 'a1 yellow_buffer -> ('a1 prodN, 'a1 any_buffer) prod **)

let yellow_pop _ _ = function
| Yellowish (_, _, b0) ->
  (match b0 with
   | B1 p -> Coq_pair (p, (Any ((Mix (NoGreen, NoYellow, SomeRed)), B0)))
   | B2 (_, _, p, p0) ->
     Coq_pair (p, (Any ((Mix (NoGreen, SomeYellow, NoRed)), (B1 p0))))
   | B3 (g, y, p, p0, p1) ->
     Coq_pair (p, (Any ((Mix ((yellow_pop_obligations_obligation_3 g),
       (yellow_pop_obligations_obligation_4 y), NoRed)), (B2
       ((yellow_pop_obligations_obligation_3 g),
       (yellow_pop_obligations_obligation_4 y), p0, p1)))))
   | B4 (p, p0, p1, p2) ->
     Coq_pair (p, (Any ((Mix (yellow_pop_obligations_obligation_6,
       yellow_pop_obligations_obligation_7, NoRed)), (B3
       (yellow_pop_obligations_obligation_6,
       yellow_pop_obligations_obligation_7, p0, p1, p2)))))
   | _ -> assert false (* absurd case *))

(** val yellow_eject_obligations_obligation_3 : green_hue -> green_hue **)

let yellow_eject_obligations_obligation_3 g1 =
  g1

(** val yellow_eject_obligations_obligation_4 : yellow_hue -> yellow_hue **)

let yellow_eject_obligations_obligation_4 y1 =
  y1

(** val yellow_eject_obligations_obligation_6 : green_hue **)

let yellow_eject_obligations_obligation_6 =
  SomeGreen

(** val yellow_eject_obligations_obligation_7 : yellow_hue **)

let yellow_eject_obligations_obligation_7 =
  SomeYellow

(** val yellow_eject :
    nat -> nat -> 'a1 yellow_buffer -> ('a1 any_buffer, 'a1 prodN) prod **)

let yellow_eject _ _ = function
| Yellowish (_, _, b0) ->
  (match b0 with
   | B1 p -> Coq_pair ((Any ((Mix (NoGreen, NoYellow, SomeRed)), B0)), p)
   | B2 (_, _, p, p0) ->
     Coq_pair ((Any ((Mix (NoGreen, SomeYellow, NoRed)), (B1 p))), p0)
   | B3 (g, y, p, p0, p1) ->
     Coq_pair ((Any ((Mix ((yellow_eject_obligations_obligation_3 g),
       (yellow_eject_obligations_obligation_4 y), NoRed)), (B2
       ((yellow_eject_obligations_obligation_3 g),
       (yellow_eject_obligations_obligation_4 y), p, p0)))), p1)
   | B4 (p, p0, p1, p2) ->
     Coq_pair ((Any ((Mix (yellow_eject_obligations_obligation_6,
       yellow_eject_obligations_obligation_7, NoRed)), (B3
       (yellow_eject_obligations_obligation_6,
       yellow_eject_obligations_obligation_7, p, p0, p1)))), p2)
   | _ -> assert false (* absurd case *))

(** val buffer_push_obligations_obligation_2 : green_hue **)

let buffer_push_obligations_obligation_2 =
  SomeGreen

(** val buffer_push_obligations_obligation_3 : yellow_hue **)

let buffer_push_obligations_obligation_3 =
  SomeYellow

(** val buffer_push_obligations_obligation_5 : green_hue -> green_hue **)

let buffer_push_obligations_obligation_5 g =
  g

(** val buffer_push_obligations_obligation_6 : yellow_hue -> yellow_hue **)

let buffer_push_obligations_obligation_6 y =
  y

(** val buffer_push :
    nat -> nat -> color -> 'a1 prodN -> 'a1 buffer -> 'a1 cdeque **)

let buffer_push lvl _ _ x = function
| B0 -> Small ((S O), (Mix (NoGreen, SomeYellow, NoRed)), (B1 x))
| B1 p ->
  Small ((S (S O)), (Mix (buffer_push_obligations_obligation_2,
    buffer_push_obligations_obligation_3, NoRed)), (B2
    (buffer_push_obligations_obligation_2,
    buffer_push_obligations_obligation_3, x, p)))
| B2 (g, y, p, p0) ->
  Small ((S (S (S O))), (Mix ((buffer_push_obligations_obligation_5 g),
    (buffer_push_obligations_obligation_6 y), NoRed)), (B3
    ((buffer_push_obligations_obligation_5 g),
    (buffer_push_obligations_obligation_6 y), x, p, p0)))
| B3 (_, _, p, p0, p1) ->
  Small ((S (S (S (S O)))), (Mix (NoGreen, SomeYellow, NoRed)), (B4 (x, p,
    p0, p1)))
| B4 (p, p0, p1, p2) ->
  Small ((S (S (S (S (S O))))), (Mix (NoGreen, NoYellow, SomeRed)), (B5 (x,
    p, p0, p1, p2)))
| B5 (p, p0, p1, p2, p3) ->
  Big ((S O), (add (add (add (S (S (S O))) O) O) (S (S (S O)))),
    (add (S O) lvl), O, (S (S (S (S (S (S O)))))), (Mix (SomeGreen, NoYellow,
    NoRed)), (Mix (SomeGreen, NoYellow, NoRed)), (Triple (O, (S (S (S O))),
    O, (S (S (S O))), NoYellow, (Mix (SomeGreen, NoYellow, NoRed)), (Mix
    (SomeGreen, NoYellow, NoRed)), (Mix (SomeGreen, NoYellow, NoRed)), (B3
    (SomeGreen, NoYellow, x, p, p0)), Hole, (B3 (SomeGreen, NoYellow, p1, p2,
    p3)), PCGreen)), (Small (O, (Mix (NoGreen, NoYellow, SomeRed)), B0)),
    (CCGreen (SomeGreen, NoRed)))

(** val buffer_inject_obligations_obligation_2 : green_hue **)

let buffer_inject_obligations_obligation_2 =
  SomeGreen

(** val buffer_inject_obligations_obligation_3 : yellow_hue **)

let buffer_inject_obligations_obligation_3 =
  SomeYellow

(** val buffer_inject_obligations_obligation_5 : green_hue -> green_hue **)

let buffer_inject_obligations_obligation_5 g =
  g

(** val buffer_inject_obligations_obligation_6 : yellow_hue -> yellow_hue **)

let buffer_inject_obligations_obligation_6 y =
  y

(** val buffer_inject :
    nat -> nat -> color -> 'a1 buffer -> 'a1 prodN -> 'a1 cdeque **)

let buffer_inject lvl _ _ b x =
  match b with
  | B0 -> Small ((S O), (Mix (NoGreen, SomeYellow, NoRed)), (B1 x))
  | B1 p ->
    Small ((S (S O)), (Mix (buffer_inject_obligations_obligation_2,
      buffer_inject_obligations_obligation_3, NoRed)), (B2
      (buffer_inject_obligations_obligation_2,
      buffer_inject_obligations_obligation_3, p, x)))
  | B2 (g, y, p, p0) ->
    Small ((S (S (S O))), (Mix ((buffer_inject_obligations_obligation_5 g),
      (buffer_inject_obligations_obligation_6 y), NoRed)), (B3
      ((buffer_inject_obligations_obligation_5 g),
      (buffer_inject_obligations_obligation_6 y), p, p0, x)))
  | B3 (_, _, p, p0, p1) ->
    Small ((S (S (S (S O)))), (Mix (NoGreen, SomeYellow, NoRed)), (B4 (p, p0,
      p1, x)))
  | B4 (p, p0, p1, p2) ->
    Small ((S (S (S (S (S O))))), (Mix (NoGreen, NoYellow, SomeRed)), (B5 (p,
      p0, p1, p2, x)))
  | B5 (p, p0, p1, p2, p3) ->
    Big ((S O), (add (add (add (S (S (S O))) O) O) (S (S (S O)))),
      (add (S O) lvl), O, (S (S (S (S (S (S O)))))), (Mix (SomeGreen,
      NoYellow, NoRed)), (Mix (SomeGreen, NoYellow, NoRed)), (Triple (O, (S
      (S (S O))), O, (S (S (S O))), NoYellow, (Mix (SomeGreen, NoYellow,
      NoRed)), (Mix (SomeGreen, NoYellow, NoRed)), (Mix (SomeGreen, NoYellow,
      NoRed)), (B3 (SomeGreen, NoYellow, p, p0, p1)), Hole, (B3 (SomeGreen,
      NoYellow, p2, p3, x)), PCGreen)), (Small (O, (Mix (NoGreen, NoYellow,
      SomeRed)), B0)), (CCGreen (SomeGreen, NoRed)))

(** val buffer_pop :
    nat -> nat -> color -> 'a1 buffer -> ('a1 prodN, 'a1 any_buffer) prod
    option **)

let buffer_pop lvl _ _ = function
| B0 -> None
| B1 p ->
  Some (yellow_pop lvl (S O) (Yellowish (NoGreen, SomeYellow, (B1 p))))
| B2 (g, y, p, p0) ->
  Some (yellow_pop lvl (S (S O)) (Yellowish (g, y, (B2 (g, y, p, p0)))))
| B3 (g, y, p, p0, p1) ->
  Some
    (yellow_pop lvl (S (S (S O))) (Yellowish (g, y, (B3 (g, y, p, p0, p1)))))
| B4 (p, p0, p1, p2) ->
  Some
    (yellow_pop lvl (S (S (S (S O)))) (Yellowish (NoGreen, SomeYellow, (B4
      (p, p0, p1, p2)))))
| B5 (p, p0, p1, p2, p3) ->
  Some (Coq_pair (p, (Any ((Mix (NoGreen, SomeYellow, NoRed)), (B4 (p0, p1,
    p2, p3))))))

(** val buffer_eject :
    nat -> nat -> color -> 'a1 buffer -> ('a1 any_buffer, 'a1 prodN) prod
    option **)

let buffer_eject lvl _ _ = function
| B0 -> None
| B1 p ->
  Some (yellow_eject lvl (S O) (Yellowish (NoGreen, SomeYellow, (B1 p))))
| B2 (g, y, p, p0) ->
  Some (yellow_eject lvl (S (S O)) (Yellowish (g, y, (B2 (g, y, p, p0)))))
| B3 (g, y, p, p0, p1) ->
  Some
    (yellow_eject lvl (S (S (S O))) (Yellowish (g, y, (B3 (g, y, p, p0,
      p1)))))
| B4 (p, p0, p1, p2) ->
  Some
    (yellow_eject lvl (S (S (S (S O)))) (Yellowish (NoGreen, SomeYellow, (B4
      (p, p0, p1, p2)))))
| B5 (p, p0, p1, p2, p3) ->
  Some (Coq_pair ((Any ((Mix (NoGreen, SomeYellow, NoRed)), (B4 (p, p0, p1,
    p2)))), p3))

(** val prefix_rot :
    nat -> nat -> color -> 'a1 prodN -> 'a1 buffer -> ('a1 buffer, 'a1 prodN)
    prod **)

let prefix_rot _ _ _ x = function
| B0 -> Coq_pair (B0, x)
| B1 p -> Coq_pair ((B1 x), p)
| B2 (g, y, p, p0) -> Coq_pair ((B2 (g, y, x, p)), p0)
| B3 (g, y, p, p0, p1) -> Coq_pair ((B3 (g, y, x, p, p0)), p1)
| B4 (p, p0, p1, p2) -> Coq_pair ((B4 (x, p, p0, p1)), p2)
| B5 (p, p0, p1, p2, p3) -> Coq_pair ((B5 (x, p, p0, p1, p2)), p3)

(** val suffix_rot :
    nat -> nat -> color -> 'a1 buffer -> 'a1 prodN -> ('a1 prodN, 'a1 buffer)
    prod **)

let suffix_rot _ _ _ b y =
  match b with
  | B0 -> Coq_pair (y, B0)
  | B1 p -> Coq_pair (p, (B1 y))
  | B2 (g, y0, p, p0) -> Coq_pair (p, (B2 (g, y0, p0, y)))
  | B3 (g, y0, p, p0, p1) -> Coq_pair (p, (B3 (g, y0, p0, p1, y)))
  | B4 (p, p0, p1, p2) -> Coq_pair (p, (B4 (p0, p1, p2, y)))
  | B5 (p, p0, p1, p2, p3) -> Coq_pair (p, (B5 (p0, p1, p2, p3, y)))

(** val prefix23 :
    nat -> green_hue -> yellow_hue -> 'a1 prodN option -> 'a1 prodN -> 'a1
    buffer **)

let prefix23 _ g y o p =
  match o with
  | Some p0 ->
    (match p with
     | Coq_prodZ _ -> assert false (* absurd case *)
     | Coq_prodS (_, p1, p2) -> B3 (g, y, p0, p1, p2))
  | None ->
    (match p with
     | Coq_prodZ _ -> assert false (* absurd case *)
     | Coq_prodS (_, p0, p1) -> B2 (g, y, p0, p1))

(** val suffix23 :
    nat -> green_hue -> yellow_hue -> 'a1 prodN -> 'a1 prodN option -> 'a1
    buffer **)

let suffix23 _ g y p o =
  match p with
  | Coq_prodZ _ -> assert false (* absurd case *)
  | Coq_prodS (_, p0, p1) ->
    (match o with
     | Some p2 -> B3 (g, y, p0, p1, p2)
     | None -> B2 (g, y, p0, p1))

(** val suffix12 : nat -> 'a1 prodN -> 'a1 prodN option -> 'a1 buffer **)

let suffix12 _ x = function
| Some p -> B2 (NoGreen, SomeYellow, x, p)
| None -> B1 x

(** val prefix_decompose :
    nat -> nat -> color -> 'a1 buffer -> 'a1 decompose **)

let prefix_decompose lvl _ _ = function
| B0 -> Underflow None
| B1 p -> Underflow (Some p)
| B2 (_, _, p, p0) -> Ok ((S (S O)), (B2 (SomeGreen, NoYellow, p, p0)))
| B3 (_, _, p, p0, p1) ->
  Ok ((S (S (S O))), (B3 (SomeGreen, NoYellow, p, p0, p1)))
| B4 (p, p0, p1, p2) ->
  Overflow ((S (S O)), (B2 (SomeGreen, NoYellow, p, p0)), (Coq_prodS (lvl,
    p1, p2)))
| B5 (p, p0, p1, p2, p3) ->
  Overflow ((S (S (S O))), (B3 (SomeGreen, NoYellow, p, p0, p1)), (Coq_prodS
    (lvl, p2, p3)))

(** val suffix_decompose :
    nat -> nat -> color -> 'a1 buffer -> 'a1 decompose **)

let suffix_decompose lvl _ _ = function
| B0 -> Underflow None
| B1 p -> Underflow (Some p)
| B2 (_, _, p, p0) -> Ok ((S (S O)), (B2 (SomeGreen, NoYellow, p, p0)))
| B3 (_, _, p, p0, p1) ->
  Ok ((S (S (S O))), (B3 (SomeGreen, NoYellow, p, p0, p1)))
| B4 (p, p0, p1, p2) ->
  Overflow ((S (S O)), (B2 (SomeGreen, NoYellow, p1, p2)), (Coq_prodS (lvl,
    p, p0)))
| B5 (p, p0, p1, p2, p3) ->
  Overflow ((S (S (S O))), (B3 (SomeGreen, NoYellow, p1, p2, p3)), (Coq_prodS
    (lvl, p, p0)))

(** val buffer_unsandwich_obligations_obligation_5 : green_hue **)

let buffer_unsandwich_obligations_obligation_5 =
  SomeGreen

(** val buffer_unsandwich_obligations_obligation_6 : yellow_hue **)

let buffer_unsandwich_obligations_obligation_6 =
  SomeYellow

(** val buffer_unsandwich_obligations_obligation_8 : green_hue **)

let buffer_unsandwich_obligations_obligation_8 =
  SomeGreen

(** val buffer_unsandwich_obligations_obligation_9 : yellow_hue **)

let buffer_unsandwich_obligations_obligation_9 =
  SomeYellow

(** val buffer_unsandwich :
    nat -> nat -> color -> 'a1 buffer -> 'a1 sandwich **)

let buffer_unsandwich _ _ _ = function
| B0 -> Alone None
| B1 p -> Alone (Some p)
| B2 (_, _, p, p0) ->
  Sandwich (O, (Mix (NoGreen, NoYellow, SomeRed)), p, B0, p0)
| B3 (_, _, p, p0, p1) ->
  Sandwich ((S O), (Mix (NoGreen, SomeYellow, NoRed)), p, (B1 p0), p1)
| B4 (p, p0, p1, p2) ->
  Sandwich ((S (S O)), (Mix (buffer_unsandwich_obligations_obligation_5,
    buffer_unsandwich_obligations_obligation_6, NoRed)), p, (B2
    (buffer_unsandwich_obligations_obligation_5,
    buffer_unsandwich_obligations_obligation_6, p0, p1)), p2)
| B5 (p, p0, p1, p2, p3) ->
  Sandwich ((S (S (S O))), (Mix (buffer_unsandwich_obligations_obligation_8,
    buffer_unsandwich_obligations_obligation_9, NoRed)), p, (B3
    (buffer_unsandwich_obligations_obligation_8,
    buffer_unsandwich_obligations_obligation_9, p0, p1, p2)), p3)

(** val buffer_halve_obligations_obligation_5 : green_hue **)

let buffer_halve_obligations_obligation_5 =
  SomeGreen

(** val buffer_halve_obligations_obligation_6 : yellow_hue **)

let buffer_halve_obligations_obligation_6 =
  SomeYellow

(** val buffer_halve_obligations_obligation_8 : green_hue **)

let buffer_halve_obligations_obligation_8 =
  SomeGreen

(** val buffer_halve_obligations_obligation_9 : yellow_hue **)

let buffer_halve_obligations_obligation_9 =
  SomeYellow

(** val buffer_halve :
    nat -> nat -> color -> 'a1 buffer -> ('a1 prodN option, 'a1 any_buffer)
    prod **)

let buffer_halve lvl _ _ = function
| B0 -> Coq_pair (None, (Any ((Mix (NoGreen, NoYellow, SomeRed)), B0)))
| B1 p -> Coq_pair ((Some p), (Any ((Mix (NoGreen, NoYellow, SomeRed)), B0)))
| B2 (_, _, p, p0) ->
  Coq_pair (None, (Any ((Mix (NoGreen, SomeYellow, NoRed)), (B1 (Coq_prodS
    (lvl, p, p0))))))
| B3 (_, _, p, p0, p1) ->
  Coq_pair ((Some p), (Any ((Mix (NoGreen, SomeYellow, NoRed)), (B1
    (Coq_prodS (lvl, p0, p1))))))
| B4 (p, p0, p1, p2) ->
  Coq_pair (None, (Any ((Mix (buffer_halve_obligations_obligation_5,
    buffer_halve_obligations_obligation_6, NoRed)), (B2
    (buffer_halve_obligations_obligation_5,
    buffer_halve_obligations_obligation_6, (Coq_prodS (lvl, p, p0)),
    (Coq_prodS (lvl, p1, p2)))))))
| B5 (p, p0, p1, p2, p3) ->
  Coq_pair ((Some p), (Any ((Mix (buffer_halve_obligations_obligation_8,
    buffer_halve_obligations_obligation_9, NoRed)), (B2
    (buffer_halve_obligations_obligation_8,
    buffer_halve_obligations_obligation_9, (Coq_prodS (lvl, p0, p1)),
    (Coq_prodS (lvl, p2, p3)))))))

(** val buffer_translate :
    nat -> nat -> nat -> color -> 'a1 buffer -> 'a1 buffer **)

let buffer_translate _ _ _ _ b =
  b

(** val green_prefix_concat :
    nat -> nat -> nat -> color -> 'a1 buffer -> 'a1 buffer -> ('a1 buffer,
    'a1 yellow_buffer) prod **)

let green_prefix_concat lvl size1 size2 c buf1 buf2 =
  match prefix_decompose lvl size1 c buf1 with
  | Underflow o ->
    let Coq_pair (p, y) = green_pop (S lvl) size2 buf2 in
    let Yellowish (g, y0, b) = y in
    Coq_pair
    ((buffer_translate lvl (add (S (S O)) (size_option o)) (S (S
       (match snd (PeanoNat.Nat.divmod (size_option o) (S O) O (S O)) with
        | O -> S O
        | S _ -> O))) (Mix (SomeGreen, NoYellow, NoRed))
       (prefix23 lvl SomeGreen NoYellow o p)), (Yellowish (g, y0,
    (buffer_translate (S lvl) (PeanoNat.Nat.pred size2)
      (add (sub size2 (S O))
        (fst (PeanoNat.Nat.divmod (size_option o) (S O) O (S O)))) (Mix (g,
      y0, NoRed)) b))))
  | Ok (size, b) ->
    Coq_pair
      ((buffer_translate lvl size (S (S
         (match snd (PeanoNat.Nat.divmod size (S O) O (S O)) with
          | O -> S O
          | S _ -> O))) (Mix (SomeGreen, NoYellow, NoRed)) b), (Yellowish
      (SomeGreen, NoYellow,
      (buffer_translate (S lvl) size2
        (add (sub size2 (S O)) (fst (PeanoNat.Nat.divmod size (S O) O (S O))))
        (Mix (SomeGreen, NoYellow, NoRed)) buf2))))
  | Overflow (size, b, p) ->
    Coq_pair
      ((buffer_translate lvl size (S (S
         (match snd (PeanoNat.Nat.divmod size (S O) (S O) (S O)) with
          | O -> S O
          | S _ -> O))) (Mix (SomeGreen, NoYellow, NoRed)) b), (Yellowish
      (NoGreen, SomeYellow,
      (buffer_translate (S lvl) (S size2)
        (add (sub size2 (S O))
          (fst (PeanoNat.Nat.divmod size (S O) (S O) (S O)))) (Mix (NoGreen,
        SomeYellow, NoRed)) (green_push (S lvl) size2 p buf2)))))

(** val green_suffix_concat :
    nat -> nat -> nat -> color -> 'a1 buffer -> 'a1 buffer -> ('a1
    yellow_buffer, 'a1 buffer) prod **)

let green_suffix_concat lvl size1 size2 c buf1 buf2 =
  match suffix_decompose lvl size2 c buf2 with
  | Underflow o ->
    let Coq_pair (y, p) = green_eject (S lvl) size1 buf1 in
    let Yellowish (g, y0, b) = y in
    Coq_pair ((Yellowish (g, y0,
    (buffer_translate (S lvl) (PeanoNat.Nat.pred size1)
      (add (sub size1 (S O))
        (fst (PeanoNat.Nat.divmod (size_option o) (S O) O (S O)))) (Mix (g,
      y0, NoRed)) b))),
    (buffer_translate lvl (add (S (S O)) (size_option o)) (S (S
      (match snd (PeanoNat.Nat.divmod (size_option o) (S O) O (S O)) with
       | O -> S O
       | S _ -> O))) (Mix (SomeGreen, NoYellow, NoRed))
      (suffix23 lvl SomeGreen NoYellow p o)))
  | Ok (size, b) ->
    Coq_pair ((Yellowish (SomeGreen, NoYellow,
      (buffer_translate (S lvl) size1
        (add (sub size1 (S O)) (fst (PeanoNat.Nat.divmod size (S O) O (S O))))
        (Mix (SomeGreen, NoYellow, NoRed)) buf1))),
      (buffer_translate lvl size (S (S
        (match snd (PeanoNat.Nat.divmod size (S O) O (S O)) with
         | O -> S O
         | S _ -> O))) (Mix (SomeGreen, NoYellow, NoRed)) b))
  | Overflow (size, b, p) ->
    Coq_pair ((Yellowish (NoGreen, SomeYellow,
      (buffer_translate (S lvl) (S size1)
        (add (sub size1 (S O))
          (fst (PeanoNat.Nat.divmod size (S O) (S O) (S O)))) (Mix (NoGreen,
        SomeYellow, NoRed)) (green_inject (S lvl) size1 buf1 p)))),
      (buffer_translate lvl size (S (S
        (match snd (PeanoNat.Nat.divmod size (S O) (S O) (S O)) with
         | O -> S O
         | S _ -> O))) (Mix (SomeGreen, NoYellow, NoRed)) b))

(** val yellow_prefix_concat :
    nat -> nat -> nat -> color -> 'a1 buffer -> 'a1 yellow_buffer -> ('a1
    buffer, 'a1 any_buffer) prod **)

let yellow_prefix_concat lvl size1 size2 c buf1 = function
| Yellowish (g, y, b) ->
  (match prefix_decompose lvl size1 c buf1 with
   | Underflow o ->
     let Coq_pair (p, a) = yellow_pop (S lvl) size2 (Yellowish (g, y, b)) in
     let Any (c0, b0) = a in
     Coq_pair
     ((buffer_translate lvl (add (S (S O)) (size_option o)) (S (S
        (match snd (PeanoNat.Nat.divmod (size_option o) (S O) O (S O)) with
         | O -> S O
         | S _ -> O))) (Mix (SomeGreen, NoYellow, NoRed))
        (prefix23 lvl SomeGreen NoYellow o p)), (Any (c0,
     (buffer_translate (S lvl) (PeanoNat.Nat.pred size2)
       (add (sub size2 (S O))
         (fst (PeanoNat.Nat.divmod (size_option o) (S O) O (S O)))) c0 b0))))
   | Ok (size, b0) ->
     Coq_pair
       ((buffer_translate lvl size (S (S
          (match snd (PeanoNat.Nat.divmod size (S O) O (S O)) with
           | O -> S O
           | S _ -> O))) (Mix (SomeGreen, NoYellow, NoRed)) b0), (Any ((Mix
       (g, y, NoRed)),
       (buffer_translate (S lvl) size2
         (add (sub size2 (S O))
           (fst (PeanoNat.Nat.divmod size (S O) O (S O)))) (Mix (g, y,
         NoRed)) b))))
   | Overflow (size, b0, p) ->
     let Any (c0, b1) = yellow_push (S lvl) size2 p (Yellowish (g, y, b)) in
     Coq_pair
     ((buffer_translate lvl size (S (S
        (match snd (PeanoNat.Nat.divmod size (S O) (S O) (S O)) with
         | O -> S O
         | S _ -> O))) (Mix (SomeGreen, NoYellow, NoRed)) b0), (Any (c0,
     (buffer_translate (S lvl) (S size2)
       (add (sub size2 (S O))
         (fst (PeanoNat.Nat.divmod size (S O) (S O) (S O)))) c0 b1)))))

(** val yellow_suffix_concat :
    nat -> nat -> nat -> color -> 'a1 yellow_buffer -> 'a1 buffer -> ('a1
    any_buffer, 'a1 buffer) prod **)

let yellow_suffix_concat lvl size1 size2 c buf1 buf2 =
  let Yellowish (g, y, b) = buf1 in
  (match suffix_decompose lvl size2 c buf2 with
   | Underflow o ->
     let Coq_pair (a, p) = yellow_eject (S lvl) size1 (Yellowish (g, y, b)) in
     let Any (c0, b0) = a in
     Coq_pair ((Any (c0,
     (buffer_translate (S lvl) (PeanoNat.Nat.pred size1)
       (add (sub size1 (S O))
         (fst (PeanoNat.Nat.divmod (size_option o) (S O) O (S O)))) c0 b0))),
     (buffer_translate lvl (add (S (S O)) (size_option o)) (S (S
       (match snd (PeanoNat.Nat.divmod (size_option o) (S O) O (S O)) with
        | O -> S O
        | S _ -> O))) (Mix (SomeGreen, NoYellow, NoRed))
       (suffix23 lvl SomeGreen NoYellow p o)))
   | Ok (size, b0) ->
     Coq_pair ((Any ((Mix (g, y, NoRed)),
       (buffer_translate (S lvl) size1
         (add (sub size1 (S O))
           (fst (PeanoNat.Nat.divmod size (S O) O (S O)))) (Mix (g, y,
         NoRed)) b))),
       (buffer_translate lvl size (S (S
         (match snd (PeanoNat.Nat.divmod size (S O) O (S O)) with
          | O -> S O
          | S _ -> O))) (Mix (SomeGreen, NoYellow, NoRed)) b0))
   | Overflow (size, b0, p) ->
     let Any (c0, b1) = yellow_inject (S lvl) size1 (Yellowish (g, y, b)) p in
     Coq_pair ((Any (c0,
     (buffer_translate (S lvl) (S size1)
       (add (sub size1 (S O))
         (fst (PeanoNat.Nat.divmod size (S O) (S O) (S O)))) c0 b1))),
     (buffer_translate lvl size (S (S
       (match snd (PeanoNat.Nat.divmod size (S O) (S O) (S O)) with
        | O -> S O
        | S _ -> O))) (Mix (SomeGreen, NoYellow, NoRed)) b0)))

(** val cdeque_of_opt3_obligations_obligation_2 : green_hue **)

let cdeque_of_opt3_obligations_obligation_2 =
  SomeGreen

(** val cdeque_of_opt3_obligations_obligation_3 : yellow_hue **)

let cdeque_of_opt3_obligations_obligation_3 =
  SomeYellow

(** val cdeque_of_opt3_obligations_obligation_5 : green_hue **)

let cdeque_of_opt3_obligations_obligation_5 =
  SomeGreen

(** val cdeque_of_opt3_obligations_obligation_6 : yellow_hue **)

let cdeque_of_opt3_obligations_obligation_6 =
  SomeYellow

(** val cdeque_of_opt3_obligations_obligation_9 : green_hue **)

let cdeque_of_opt3_obligations_obligation_9 =
  SomeGreen

(** val cdeque_of_opt3_obligations_obligation_10 : yellow_hue **)

let cdeque_of_opt3_obligations_obligation_10 =
  SomeYellow

(** val cdeque_of_opt3_obligations_obligation_12 : green_hue **)

let cdeque_of_opt3_obligations_obligation_12 =
  SomeGreen

(** val cdeque_of_opt3_obligations_obligation_13 : yellow_hue **)

let cdeque_of_opt3_obligations_obligation_13 =
  SomeYellow

(** val cdeque_of_opt3 :
    nat -> 'a1 prodN option -> 'a1 prodN option -> 'a1 prodN option -> 'a1
    cdeque **)

let cdeque_of_opt3 _ o1 o2 o3 =
  match o1 with
  | Some p ->
    (match o2 with
     | Some p0 ->
       (match p0 with
        | Coq_prodZ _ -> assert false (* absurd case *)
        | Coq_prodS (_, p1, p2) ->
          (match o3 with
           | Some p3 ->
             Small ((S (S (S (S O)))), (Mix (NoGreen, SomeYellow, NoRed)),
               (B4 (p, p1, p2, p3)))
           | None ->
             Small ((S (S (S O))), (Mix
               (cdeque_of_opt3_obligations_obligation_2,
               cdeque_of_opt3_obligations_obligation_3, NoRed)), (B3
               (cdeque_of_opt3_obligations_obligation_2,
               cdeque_of_opt3_obligations_obligation_3, p, p1, p2)))))
     | None ->
       (match o3 with
        | Some p0 ->
          Small ((S (S O)), (Mix (cdeque_of_opt3_obligations_obligation_5,
            cdeque_of_opt3_obligations_obligation_6, NoRed)), (B2
            (cdeque_of_opt3_obligations_obligation_5,
            cdeque_of_opt3_obligations_obligation_6, p, p0)))
        | None -> Small ((S O), (Mix (NoGreen, SomeYellow, NoRed)), (B1 p))))
  | None ->
    (match o2 with
     | Some p ->
       (match p with
        | Coq_prodZ _ -> assert false (* absurd case *)
        | Coq_prodS (_, p0, p1) ->
          (match o3 with
           | Some p2 ->
             Small ((S (S (S O))), (Mix
               (cdeque_of_opt3_obligations_obligation_9,
               cdeque_of_opt3_obligations_obligation_10, NoRed)), (B3
               (cdeque_of_opt3_obligations_obligation_9,
               cdeque_of_opt3_obligations_obligation_10, p0, p1, p2)))
           | None ->
             Small ((S (S O)), (Mix
               (cdeque_of_opt3_obligations_obligation_12,
               cdeque_of_opt3_obligations_obligation_13, NoRed)), (B2
               (cdeque_of_opt3_obligations_obligation_12,
               cdeque_of_opt3_obligations_obligation_13, p0, p1)))))
     | None ->
       (match o3 with
        | Some p -> Small ((S O), (Mix (NoGreen, SomeYellow, NoRed)), (B1 p))
        | None -> Small (O, (Mix (NoGreen, NoYellow, SomeRed)), B0)))

(** val cdeque_translate :
    nat -> nat -> nat -> color -> 'a1 cdeque -> 'a1 cdeque **)

let cdeque_translate _ _ _ _ cd =
  cd

(** val make_small :
    nat -> nat -> nat -> nat -> color -> color -> color -> 'a1 buffer -> 'a1
    buffer -> 'a1 buffer -> 'a1 cdeque **)

let make_small lvl size1 size2 size3 c1 c2 c3 prefix1 buf suffix1 =
  match prefix_decompose lvl size1 c1 prefix1 with
  | Underflow o ->
    (match suffix_decompose lvl size3 c3 suffix1 with
     | Underflow o0 ->
       (match buffer_unsandwich (S lvl) size2 c2 buf with
        | Alone o1 -> cdeque_of_opt3 lvl o o1 o0
        | Sandwich (size, c, p, b, p0) ->
          Big ((S O),
            (add (add (add (add (S (S O)) (size_option o)) O) O)
              (add (S (S O)) (size_option o0))), (S lvl), size,
            (add (add (add (size_option o) (S (S size))) (S (S size)))
              (size_option o0)), (Mix (SomeGreen, NoYellow, NoRed)), (Mix
            (SomeGreen, NoYellow, NoRed)), (Triple (O,
            (add (S (S O)) (size_option o)), O,
            (add (S (S O)) (size_option o0)), NoYellow, (Mix (SomeGreen,
            NoYellow, NoRed)), (Mix (SomeGreen, NoYellow, NoRed)), (Mix
            (SomeGreen, NoYellow, NoRed)),
            (prefix23 lvl SomeGreen NoYellow o p), Hole,
            (suffix23 lvl SomeGreen NoYellow p0 o0), PCGreen)), (Small (size,
            c, b)), (CCGreen (SomeGreen, NoRed))))
     | Ok (size, b) ->
       (match o with
        | Some p ->
          (match buffer_pop (S lvl) size2 c2 buf with
           | Some p0 ->
             let Coq_pair (p1, a) = p0 in
             (match p1 with
              | Coq_prodZ _ -> assert false (* absurd case *)
              | Coq_prodS (_, p2, p3) ->
                let Any (c, b0) = a in
                Big ((S O), (add (add (add (S (S (S O))) O) O) size), (S
                lvl), (PeanoNat.Nat.pred size2), (S
                (add (add size2 size2) size)), (Mix (SomeGreen, NoYellow,
                NoRed)), (Mix (SomeGreen, NoYellow, NoRed)), (Triple (O, (S
                (S (S O))), O, size, NoYellow, (Mix (SomeGreen, NoYellow,
                NoRed)), (Mix (SomeGreen, NoYellow, NoRed)), (Mix (SomeGreen,
                NoYellow, NoRed)), (B3 (SomeGreen, NoYellow, p, p2, p3)),
                Hole, b, PCGreen)), (Small ((PeanoNat.Nat.pred size2), c,
                b0)), (CCGreen (SomeGreen, NoRed))))
           | None ->
             cdeque_translate lvl (S size) (S (add (add size2 size2) size))
               (Mix (SomeGreen, NoYellow, NoRed))
               (buffer_push lvl size (Mix (SomeGreen, NoYellow, NoRed)) p b))
        | None ->
          (match buffer_pop (S lvl) size2 c2 buf with
           | Some p ->
             let Coq_pair (p0, a) = p in
             (match p0 with
              | Coq_prodZ _ -> assert false (* absurd case *)
              | Coq_prodS (_, p1, p2) ->
                let Any (c, b0) = a in
                Big ((S O), (add (add (add (S (S O)) O) O) size), (S lvl),
                (PeanoNat.Nat.pred size2), (add (add size2 size2) size), (Mix
                (SomeGreen, NoYellow, NoRed)), (Mix (SomeGreen, NoYellow,
                NoRed)), (Triple (O, (S (S O)), O, size, NoYellow, (Mix
                (SomeGreen, NoYellow, NoRed)), (Mix (SomeGreen, NoYellow,
                NoRed)), (Mix (SomeGreen, NoYellow, NoRed)), (B2 (SomeGreen,
                NoYellow, p1, p2)), Hole, b, PCGreen)), (Small
                ((PeanoNat.Nat.pred size2), c, b0)), (CCGreen (SomeGreen,
                NoRed))))
           | None ->
             cdeque_translate lvl size (add (add size2 size2) size) (Mix
               (SomeGreen, NoYellow, NoRed)) (Small (size, (Mix (SomeGreen,
               NoYellow, NoRed)), b))))
     | Overflow (size, b, p) ->
       let Coq_pair (p0, b0) = suffix_rot (S lvl) size2 c2 buf p in
       Big ((S O),
       (add (add (add (add (S (S O)) (size_option o)) O) O) size), (S lvl),
       size2, (add (add (add (size_option o) size2) size2) (S (S size))),
       (Mix (SomeGreen, NoYellow, NoRed)), (Mix (SomeGreen, NoYellow,
       NoRed)), (Triple (O, (add (S (S O)) (size_option o)), O, size,
       NoYellow, (Mix (SomeGreen, NoYellow, NoRed)), (Mix (SomeGreen,
       NoYellow, NoRed)), (Mix (SomeGreen, NoYellow, NoRed)),
       (prefix23 lvl SomeGreen NoYellow o p0), Hole, b, PCGreen)), (Small
       (size2, c2, b0)), (CCGreen (SomeGreen, NoRed))))
  | Ok (size, b) ->
    (match suffix_decompose lvl size3 c3 suffix1 with
     | Underflow o ->
       (match o with
        | Some p ->
          (match buffer_eject (S lvl) size2 c2 buf with
           | Some p0 ->
             let Coq_pair (a, p1) = p0 in
             let Any (c, b0) = a in
             (match p1 with
              | Coq_prodZ _ -> assert false (* absurd case *)
              | Coq_prodS (_, p2, p3) ->
                Big ((S O), (add (add (add size O) O) (S (S (S O)))), (S
                  lvl), (PeanoNat.Nat.pred size2),
                  (add (add (add size size2) size2) (S O)), (Mix (SomeGreen,
                  NoYellow, NoRed)), (Mix (SomeGreen, NoYellow, NoRed)),
                  (Triple (O, size, O, (S (S (S O))), NoYellow, (Mix
                  (SomeGreen, NoYellow, NoRed)), (Mix (SomeGreen, NoYellow,
                  NoRed)), (Mix (SomeGreen, NoYellow, NoRed)), b, Hole, (B3
                  (SomeGreen, NoYellow, p2, p3, p)), PCGreen)), (Small
                  ((PeanoNat.Nat.pred size2), c, b0)), (CCGreen (SomeGreen,
                  NoRed))))
           | None ->
             cdeque_translate lvl (S size)
               (add (add (add size size2) size2) (S O)) (Mix (SomeGreen,
               NoYellow, NoRed))
               (buffer_inject lvl size (Mix (SomeGreen, NoYellow, NoRed)) b p))
        | None ->
          (match buffer_eject (S lvl) size2 c2 buf with
           | Some p ->
             let Coq_pair (a, p0) = p in
             let Any (c, b0) = a in
             (match p0 with
              | Coq_prodZ _ -> assert false (* absurd case *)
              | Coq_prodS (_, p1, p2) ->
                Big ((S O), (add (add (add size O) O) (S (S O))), (S lvl),
                  (PeanoNat.Nat.pred size2),
                  (add (add (add size size2) size2) O), (Mix (SomeGreen,
                  NoYellow, NoRed)), (Mix (SomeGreen, NoYellow, NoRed)),
                  (Triple (O, size, O, (S (S O)), NoYellow, (Mix (SomeGreen,
                  NoYellow, NoRed)), (Mix (SomeGreen, NoYellow, NoRed)), (Mix
                  (SomeGreen, NoYellow, NoRed)), b, Hole, (B2 (SomeGreen,
                  NoYellow, p1, p2)), PCGreen)), (Small
                  ((PeanoNat.Nat.pred size2), c, b0)), (CCGreen (SomeGreen,
                  NoRed))))
           | None ->
             cdeque_translate lvl size (add (add (add size size2) size2) O)
               (Mix (SomeGreen, NoYellow, NoRed)) (Small (size, (Mix
               (SomeGreen, NoYellow, NoRed)), b))))
     | Ok (size0, b0) ->
       Big ((S O), (add (add (add size O) O) size0), (S lvl), size2,
         (add (add (add size size2) size2) size0), (Mix (SomeGreen, NoYellow,
         NoRed)), (Mix (SomeGreen, NoYellow, NoRed)), (Triple (O, size, O,
         size0, NoYellow, (Mix (SomeGreen, NoYellow, NoRed)), (Mix
         (SomeGreen, NoYellow, NoRed)), (Mix (SomeGreen, NoYellow, NoRed)),
         b, Hole, b0, PCGreen)), (Small (size2, c2, buf)), (CCGreen
         (SomeGreen, NoRed)))
     | Overflow (size0, b0, p) ->
       Big ((S O), (add (add (add size O) O) size0), (S lvl), (S size2),
         (add (add (add size size2) size2) (S (S size0))), (Mix (SomeGreen,
         NoYellow, NoRed)), (Mix (SomeGreen, NoYellow, NoRed)), (Triple (O,
         size, O, size0, NoYellow, (Mix (SomeGreen, NoYellow, NoRed)), (Mix
         (SomeGreen, NoYellow, NoRed)), (Mix (SomeGreen, NoYellow, NoRed)),
         b, Hole, b0, PCGreen)), (buffer_inject (S lvl) size2 c2 buf p),
         (CCGreen (SomeGreen, NoRed))))
  | Overflow (size, b, p) ->
    (match suffix_decompose lvl size3 c3 suffix1 with
     | Underflow o ->
       let Coq_pair (b0, p0) = prefix_rot (S lvl) size2 c2 p buf in
       Big ((S O),
       (add (add (add size O) O) (add (S (S O)) (size_option o))), (S lvl),
       size2, (S (S (add (add (add size size2) size2) (size_option o)))),
       (Mix (SomeGreen, NoYellow, NoRed)), (Mix (SomeGreen, NoYellow,
       NoRed)), (Triple (O, size, O, (add (S (S O)) (size_option o)),
       NoYellow, (Mix (SomeGreen, NoYellow, NoRed)), (Mix (SomeGreen,
       NoYellow, NoRed)), (Mix (SomeGreen, NoYellow, NoRed)), b, Hole,
       (suffix23 lvl SomeGreen NoYellow p0 o), PCGreen)), (Small (size2, c2,
       b0)), (CCGreen (SomeGreen, NoRed)))
     | Ok (size0, b0) ->
       Big ((S O), (add (add (add size O) O) size0), (S lvl), (S size2), (S
         (S (add (add (add size size2) size2) size0))), (Mix (SomeGreen,
         NoYellow, NoRed)), (Mix (SomeGreen, NoYellow, NoRed)), (Triple (O,
         size, O, size0, NoYellow, (Mix (SomeGreen, NoYellow, NoRed)), (Mix
         (SomeGreen, NoYellow, NoRed)), (Mix (SomeGreen, NoYellow, NoRed)),
         b, Hole, b0, PCGreen)), (buffer_push (S lvl) size2 c2 p buf),
         (CCGreen (SomeGreen, NoRed)))
     | Overflow (size0, b0, p0) ->
       let Coq_pair (o, a) = buffer_halve (S lvl) size2 c2 buf in
       let Any (c, b1) = a in
       Big ((S (S O)),
       (add
         (add (add size (add (add (add (S (size_option o)) O) O) (S O)))
           (add (add (add (S (size_option o)) O) O) (S O))) size0), (S (S
       lvl)), (fst (PeanoNat.Nat.divmod size2 (S O) O (S O))), (S (S
       (add (add (add size size2) size2) (S (S size0))))), (Mix (SomeGreen,
       NoYellow, NoRed)), (Mix (SomeGreen, NoYellow, NoRed)), (Triple ((S O),
       size, (add (add (add (S (size_option o)) O) O) (S O)), size0,
       SomeYellow, (Mix (SomeGreen, NoYellow, NoRed)), (Mix (SomeGreen,
       NoYellow, NoRed)), (Mix (SomeGreen, NoYellow, NoRed)), b, (Triple (O,
       (S (size_option o)), O, (S O), NoYellow, (Mix (NoGreen, SomeYellow,
       NoRed)), (Mix (NoGreen, SomeYellow, NoRed)), (Mix (NoGreen,
       SomeYellow, NoRed)), (suffix12 (S lvl) p o), Hole, (B1 p0), (PCYellow
       (NoGreen, SomeYellow, NoGreen, SomeYellow)))), b0, PCGreen)), (Small
       ((fst (PeanoNat.Nat.divmod size2 (S O) O (S O))), c, b1)), (CCGreen
       (SomeGreen, NoRed))))

(** val green_of_red : nat -> nat -> 'a1 cdeque -> 'a1 cdeque **)

let green_of_red lvl _ = function
| Small (_, _, _) -> assert false (* absurd case *)
| Big (_, _, _, nsize, _, _, _, p, c, c0) ->
  (match p with
   | Hole -> assert false (* absurd case *)
   | Triple (_, psize, _, ssize, _, _, _, _, b, p0, b0, p1) ->
     (match p0 with
      | Hole ->
        (match p1 with
         | PCRed (c1, c2) ->
           (match c with
            | Small (size, c3, b1) ->
              (match c0 with
               | CCRed ->
                 cdeque_translate lvl (add (add (add psize size) size) ssize)
                   (add (add (add (add psize O) O) ssize)
                     (add size (add size O))) (Mix (SomeGreen, NoYellow,
                   NoRed)) (make_small lvl psize size ssize c1 c3 c2 b b1 b0)
               | _ -> assert false (* absurd case *))
            | Big (_, _, _, nsize0, _, _, _, p2, c3, c4) ->
              (match p2 with
               | Hole -> assert false (* absurd case *)
               | Triple (len, psize0, pktsize, ssize0, y, _, _, _, b1, p3,
                         b2, p4) ->
                 (match p4 with
                  | PCGreen ->
                    (match c4 with
                     | CCGreen (g, r) ->
                       (match c0 with
                        | CCRed ->
                          let Coq_pair (b3, y0) =
                            green_prefix_concat lvl psize psize0 c1 b b1
                          in
                          let Yellowish (g0, y1, b4) = y0 in
                          let Coq_pair (y2, b5) =
                            green_suffix_concat (add O lvl) ssize0 ssize c2
                              b2 b0
                          in
                          let Yellowish (g1, y3, b6) = y2 in
                          Big ((S (S len)),
                          (add
                            (add
                              (add
                                (add (S (S O))
                                  (PeanoNat.Nat.modulo psize (S (S O))))
                                (add
                                  (add
                                    (add
                                      (add (sub psize0 (S O))
                                        (PeanoNat.Nat.div psize (S (S O))))
                                      pktsize) pktsize)
                                  (add (sub ssize0 (S O))
                                    (PeanoNat.Nat.div ssize (S (S O))))))
                              (add
                                (add
                                  (add
                                    (add (sub psize0 (S O))
                                      (PeanoNat.Nat.div psize (S (S O))))
                                    pktsize) pktsize)
                                (add (sub ssize0 (S O))
                                  (PeanoNat.Nat.div ssize (S (S O))))))
                            (add (S (S O))
                              (PeanoNat.Nat.modulo ssize (S (S O))))), (S
                          (add len (S (add O lvl)))), nsize0,
                          (add (add (add (add psize O) O) ssize)
                            (add
                              (add
                                (add (add (add psize0 pktsize) pktsize)
                                  ssize0)
                                (mul (add (power2 len) (power2 len)) nsize0))
                              (add
                                (add
                                  (add (add (add psize0 pktsize) pktsize)
                                    ssize0)
                                  (mul (add (power2 len) (power2 len)) nsize0))
                                O))), (Mix (SomeGreen, NoYellow, NoRed)),
                          (Mix (g, NoYellow, r)), (Triple ((S len),
                          (add (S (S O))
                            (PeanoNat.Nat.modulo psize (S (S O)))),
                          (add
                            (add
                              (add
                                (add (sub psize0 (S O))
                                  (PeanoNat.Nat.div psize (S (S O)))) pktsize)
                              pktsize)
                            (add (sub ssize0 (S O))
                              (PeanoNat.Nat.div ssize (S (S O))))),
                          (add (S (S O))
                            (PeanoNat.Nat.modulo ssize (S (S O)))),
                          SomeYellow, (Mix (SomeGreen, NoYellow, NoRed)),
                          (Mix (SomeGreen, NoYellow, NoRed)), (Mix
                          (SomeGreen, NoYellow, NoRed)), b3, (Triple (len,
                          (add (sub psize0 (S O))
                            (PeanoNat.Nat.div psize (S (S O)))), pktsize,
                          (add (sub ssize0 (S O))
                            (PeanoNat.Nat.div ssize (S (S O)))), y, (Mix (g0,
                          y1, NoRed)), (Mix (g1, y3, NoRed)), (Mix (NoGreen,
                          SomeYellow, NoRed)), b4, p3, b6, (PCYellow (g0, y1,
                          g1, y3)))), b5, PCGreen)), c3, (CCGreen (g, r)))
                        | _ -> assert false (* absurd case *))
                     | _ -> assert false (* absurd case *))
                  | _ -> assert false (* absurd case *))))
         | _ -> assert false (* absurd case *))
      | Triple (len, psize0, pktsize, ssize0, y, _, _, _, b1, p2, b2, p3) ->
        (match p3 with
         | PCYellow (g1, y1, g2, y2) ->
           (match p1 with
            | PCRed (c1, c2) ->
              (match c0 with
               | CCRed ->
                 let Coq_pair (b3, a) =
                   yellow_prefix_concat lvl psize psize0 c1 b (Yellowish (g1,
                     y1, b1))
                 in
                 let Any (c3, b4) = a in
                 let Coq_pair (a0, b5) =
                   yellow_suffix_concat lvl ssize0 ssize c2 (Yellowish (g2,
                     y2, b2)) b0
                 in
                 let Any (c4, b6) = a0 in
                 Big ((S O),
                 (add
                   (add
                     (add
                       (add (S (S O)) (PeanoNat.Nat.modulo psize (S (S O))))
                       O) O)
                   (add (S (S O)) (PeanoNat.Nat.modulo ssize (S (S O))))), (S
                 lvl),
                 (add
                   (add
                     (add
                       (add
                         (add (sub psize0 (S O))
                           (PeanoNat.Nat.div psize (S (S O)))) pktsize)
                       pktsize)
                     (add (sub ssize0 (S O))
                       (PeanoNat.Nat.div ssize (S (S O)))))
                   (mul (power2 (S len)) nsize)),
                 (add
                   (add
                     (add
                       (add psize
                         (add (add (add psize0 pktsize) pktsize) ssize0))
                       (add (add (add psize0 pktsize) pktsize) ssize0)) ssize)
                   (mul
                     (add (add (power2 len) (power2 len))
                       (add (power2 len) (power2 len))) nsize)), (Mix
                 (SomeGreen, NoYellow, NoRed)), (Mix (NoGreen, NoYellow,
                 SomeRed)), (Triple (O,
                 (add (S (S O)) (PeanoNat.Nat.modulo psize (S (S O)))), O,
                 (add (S (S O)) (PeanoNat.Nat.modulo ssize (S (S O)))),
                 NoYellow, (Mix (SomeGreen, NoYellow, NoRed)), (Mix
                 (SomeGreen, NoYellow, NoRed)), (Mix (SomeGreen, NoYellow,
                 NoRed)), b3, Hole, b5, PCGreen)), (Big ((S len),
                 (add
                   (add
                     (add
                       (add (sub psize0 (S O))
                         (PeanoNat.Nat.div psize (S (S O)))) pktsize) pktsize)
                   (add (sub ssize0 (S O)) (PeanoNat.Nat.div ssize (S (S O))))),
                 (S (add (S len) lvl)), nsize,
                 (add
                   (add
                     (add
                       (add
                         (add (sub psize0 (S O))
                           (PeanoNat.Nat.div psize (S (S O)))) pktsize)
                       pktsize)
                     (add (sub ssize0 (S O))
                       (PeanoNat.Nat.div ssize (S (S O)))))
                   (mul (power2 (S len)) nsize)), (Mix (NoGreen, NoYellow,
                 SomeRed)), (Mix (SomeGreen, NoYellow, NoRed)), (Triple (len,
                 (add (sub psize0 (S O)) (PeanoNat.Nat.div psize (S (S O)))),
                 pktsize,
                 (add (sub ssize0 (S O)) (PeanoNat.Nat.div ssize (S (S O)))),
                 y, c3, c4, (Mix (NoGreen, NoYellow, SomeRed)), b4, p2, b6,
                 (PCRed (c3, c4)))), c, CCRed)), (CCGreen (NoGreen, SomeRed)))
               | _ -> assert false (* absurd case *))
            | _ -> assert false (* absurd case *))
         | _ -> assert false (* absurd case *))))

(** val ensure_green :
    nat -> nat -> green_hue -> red_hue -> 'a1 cdeque -> 'a1 cdeque **)

let ensure_green lvl _ _ _ = function
| Small (size, c, b) -> Small (size, c, b)
| Big (len, pktsize, _, nsize, _, _, _, p, c, c0) ->
  (match c0 with
   | CCGreen (g, r) ->
     Big (len, pktsize, (add len lvl), nsize,
       (add pktsize (mul (power2 len) nsize)), (Mix (SomeGreen, NoYellow,
       NoRed)), (Mix (g, NoYellow, r)), p, c, (CCGreen (g, r)))
   | CCYellow -> assert false (* absurd case *)
   | CCRed ->
     green_of_red lvl (add pktsize (mul (power2 len) nsize)) (Big (len,
       pktsize, (add len lvl), nsize, (add pktsize (mul (power2 len) nsize)),
       (Mix (NoGreen, NoYellow, SomeRed)), (Mix (SomeGreen, NoYellow,
       NoRed)), p, c, CCRed)))

(** val make_yellow :
    nat -> nat -> nat -> nat -> nat -> green_hue -> yellow_hue -> yellow_hue
    -> green_hue -> yellow_hue -> green_hue -> red_hue -> 'a1 buffer -> 'a1
    packet -> 'a1 buffer -> 'a1 cdeque -> 'a1 deque **)

let make_yellow len size1 pktsize size2 cdsize g1 y1 y2 g3 y3 g4 r4 p1 child s1 cd =
  T (NoGreen, SomeYellow, (Big ((S len),
    (add (add (add size1 pktsize) pktsize) size2), (add (S len) O), cdsize,
    (add (add (add (add size1 pktsize) pktsize) size2)
      (mul (power2 (S len)) cdsize)), (Mix (NoGreen, SomeYellow, NoRed)),
    (Mix (SomeGreen, NoYellow, NoRed)), (Triple (len, size1, pktsize, size2,
    y2, (Mix (g1, y1, NoRed)), (Mix (g3, y3, NoRed)), (Mix (NoGreen,
    SomeYellow, NoRed)), p1, child, s1, (PCYellow (g1, y1, g3, y3)))),
    (ensure_green (add (S len) O) cdsize g4 r4 cd), CCYellow)))

(** val make_red :
    nat -> nat -> nat -> nat -> nat -> color -> yellow_hue -> color -> 'a1
    buffer -> 'a1 packet -> 'a1 buffer -> 'a1 cdeque -> 'a1 deque **)

let make_red len size1 pktsize size2 cdsize c1 y2 c3 p1 child s1 cd =
  T (SomeGreen, NoYellow,
    (green_of_red O
      (add (add (add (add size1 pktsize) pktsize) size2)
        (mul (power2 (S len)) cdsize)) (Big ((S len),
      (add (add (add size1 pktsize) pktsize) size2), (add (S len) O), cdsize,
      (add (add (add (add size1 pktsize) pktsize) size2)
        (mul (power2 (S len)) cdsize)), (Mix (NoGreen, NoYellow, SomeRed)),
      (Mix (SomeGreen, NoYellow, NoRed)), (Triple (len, size1, pktsize,
      size2, y2, c1, c3, (Mix (NoGreen, NoYellow, SomeRed)), p1, child, s1,
      (PCRed (c1, c3)))), cd, CCRed))))

(** val deque_translate : nat -> nat -> 'a1 deque -> 'a1 deque **)

let deque_translate _ _ d =
  d

(** val push : nat -> 'a1 -> 'a1 deque -> 'a1 deque **)

let push _ x = function
| T (_, _, c) ->
  (match c with
   | Small (size, c0, b) ->
     T (SomeGreen, NoYellow, (buffer_push O size c0 (Coq_prodZ x) b))
   | Big (_, _, _, nsize, _, _, _, p, c0, c1) ->
     (match p with
      | Hole -> assert false (* absurd case *)
      | Triple (len, psize, pktsize, ssize, y, _, _, _, b, p0, b0, p1) ->
        (match p1 with
         | PCGreen ->
           (match c1 with
            | CCGreen (g, r) ->
              make_yellow len (S psize) pktsize ssize nsize NoGreen
                SomeYellow y SomeGreen NoYellow g r
                (green_push O psize (Coq_prodZ x) b) p0 b0 c0
            | _ -> assert false (* absurd case *))
         | PCYellow (g1, y1, g2, y2) ->
           (match c1 with
            | CCYellow ->
              let Any (c2, b1) =
                yellow_push O psize (Coq_prodZ x) (Yellowish (g1, y1, b))
              in
              make_red len (S psize) pktsize ssize nsize c2 y (Mix (g2, y2,
                NoRed)) b1 p0 b0 c0
            | _ -> assert false (* absurd case *))
         | PCRed (_, _) -> assert false (* absurd case *))))

(** val inject : nat -> 'a1 deque -> 'a1 -> 'a1 deque **)

let inject _ d x =
  let T (_, _, c) = d in
  (match c with
   | Small (size, c0, b) ->
     T (SomeGreen, NoYellow, (buffer_inject O size c0 b (Coq_prodZ x)))
   | Big (_, _, _, nsize, _, _, _, p, c0, c1) ->
     (match p with
      | Hole -> assert false (* absurd case *)
      | Triple (len, psize, pktsize, ssize, y, _, _, _, b, p0, b0, p1) ->
        (match p1 with
         | PCGreen ->
           (match c1 with
            | CCGreen (g, r) ->
              deque_translate
                (add (add (add (add psize pktsize) pktsize) (S ssize))
                  (mul (power2 (S len)) nsize)) (S
                (add (add (add (add psize pktsize) pktsize) ssize)
                  (mul (add (power2 len) (power2 len)) nsize)))
                (make_yellow len psize pktsize (S ssize) nsize SomeGreen
                  NoYellow y NoGreen SomeYellow g r b p0
                  (green_inject O ssize b0 (Coq_prodZ x)) c0)
            | _ -> assert false (* absurd case *))
         | PCYellow (g1, y1, g2, y2) ->
           (match c1 with
            | CCYellow ->
              let Any (c2, b1) =
                yellow_inject O ssize (Yellowish (g2, y2, b0)) (Coq_prodZ x)
              in
              deque_translate
                (add (add (add (add psize pktsize) pktsize) (S ssize))
                  (mul (power2 (S len)) nsize)) (S
                (add (add (add (add psize pktsize) pktsize) ssize)
                  (mul (add (power2 len) (power2 len)) nsize)))
                (make_red len psize pktsize (S ssize) nsize (Mix (g1, y1,
                  NoRed)) y c2 b p0 b1 c0)
            | _ -> assert false (* absurd case *))
         | PCRed (_, _) -> assert false (* absurd case *))))

(** val unsafe_pop : nat -> 'a1 deque -> ('a1, 'a1 deque) prod option **)

let unsafe_pop _ = function
| T (_, _, c) ->
  (match c with
   | Small (size, c0, b) ->
     (match buffer_pop O size c0 b with
      | Some p ->
        let Coq_pair (p0, a) = p in
        (match p0 with
         | Coq_prodZ y ->
           let Any (c1, b0) = a in
           Some (Coq_pair (y, (T (SomeGreen, NoYellow, (Small
           ((PeanoNat.Nat.pred size), c1, b0))))))
         | Coq_prodS (_, _, _) -> assert false (* absurd case *))
      | None -> None)
   | Big (_, _, _, nsize, _, _, _, p, c0, c1) ->
     (match p with
      | Hole -> assert false (* absurd case *)
      | Triple (len, psize, pktsize, ssize, y, _, _, _, b, p0, b0, p1) ->
        (match p1 with
         | PCGreen ->
           (match c1 with
            | CCGreen (g, r) ->
              let Coq_pair (p2, y0) = green_pop O psize b in
              (match p2 with
               | Coq_prodZ y1 ->
                 let Yellowish (g0, y2, b1) = y0 in
                 Some (Coq_pair (y1,
                 (deque_translate
                   (add
                     (add
                       (add (add (PeanoNat.Nat.pred psize) pktsize) pktsize)
                       ssize) (mul (power2 (S len)) nsize))
                   (PeanoNat.Nat.pred
                     (add (add (add (add psize pktsize) pktsize) ssize)
                       (mul (add (power2 len) (power2 len)) nsize)))
                   (make_yellow len (PeanoNat.Nat.pred psize) pktsize ssize
                     nsize g0 y2 y SomeGreen NoYellow g r b1 p0 b0 c0))))
               | Coq_prodS (_, _, _) -> assert false (* absurd case *))
            | _ -> assert false (* absurd case *))
         | PCYellow (g1, y1, g2, y2) ->
           (match c1 with
            | CCYellow ->
              let Coq_pair (p2, a) =
                yellow_pop O psize (Yellowish (g1, y1, b))
              in
              (match p2 with
               | Coq_prodZ y0 ->
                 let Any (c2, b1) = a in
                 Some (Coq_pair (y0,
                 (deque_translate
                   (add
                     (add
                       (add (add (PeanoNat.Nat.pred psize) pktsize) pktsize)
                       ssize) (mul (power2 (S len)) nsize))
                   (PeanoNat.Nat.pred
                     (add (add (add (add psize pktsize) pktsize) ssize)
                       (mul (add (power2 len) (power2 len)) nsize)))
                   (make_red len (PeanoNat.Nat.pred psize) pktsize ssize
                     nsize c2 y (Mix (g2, y2, NoRed)) b1 p0 b0 c0))))
               | Coq_prodS (_, _, _) -> assert false (* absurd case *))
            | _ -> assert false (* absurd case *))
         | PCRed (_, _) -> assert false (* absurd case *))))

(** val pop_obligations_obligation_2 :
    nat -> 'a1 deque -> ('a1, 'a1 deque) prod **)

let pop_obligations_obligation_2 _ _ =
  assert false (* absurd case *)

(** val pop : nat -> 'a1 deque -> ('a1, 'a1 deque) prod **)

let pop size d =
  match unsafe_pop (S size) d with
  | Some p -> p
  | None -> pop_obligations_obligation_2 size d

(** val unsafe_eject : nat -> 'a1 deque -> ('a1 deque, 'a1) prod option **)

let unsafe_eject _ = function
| T (_, _, c) ->
  (match c with
   | Small (size, c0, b) ->
     (match buffer_eject O size c0 b with
      | Some p ->
        let Coq_pair (a, p0) = p in
        let Any (c1, b0) = a in
        (match p0 with
         | Coq_prodZ y ->
           Some (Coq_pair ((T (SomeGreen, NoYellow, (Small
             ((PeanoNat.Nat.pred size), c1, b0)))), y))
         | Coq_prodS (_, _, _) -> assert false (* absurd case *))
      | None -> None)
   | Big (_, _, _, nsize, _, _, _, p, c0, c1) ->
     (match p with
      | Hole -> assert false (* absurd case *)
      | Triple (len, psize, pktsize, ssize, y, _, _, _, b, p0, b0, p1) ->
        (match p1 with
         | PCGreen ->
           (match c1 with
            | CCGreen (g, r) ->
              let Coq_pair (y0, p2) = green_eject O ssize b0 in
              let Yellowish (g0, y1, b1) = y0 in
              (match p2 with
               | Coq_prodZ y2 ->
                 Some (Coq_pair
                   ((deque_translate
                      (add
                        (add (add (add psize pktsize) pktsize)
                          (PeanoNat.Nat.pred ssize))
                        (mul (power2 (S len)) nsize))
                      (PeanoNat.Nat.pred
                        (add (add (add (add psize pktsize) pktsize) ssize)
                          (mul (add (power2 len) (power2 len)) nsize)))
                      (make_yellow len psize pktsize
                        (PeanoNat.Nat.pred ssize) nsize SomeGreen NoYellow y
                        g0 y1 g r b p0 b1 c0)), y2))
               | Coq_prodS (_, _, _) -> assert false (* absurd case *))
            | _ -> assert false (* absurd case *))
         | PCYellow (g1, y1, g2, y2) ->
           (match c1 with
            | CCYellow ->
              let Coq_pair (a, p2) =
                yellow_eject O ssize (Yellowish (g2, y2, b0))
              in
              let Any (c2, b1) = a in
              (match p2 with
               | Coq_prodZ y0 ->
                 Some (Coq_pair
                   ((deque_translate
                      (add
                        (add (add (add psize pktsize) pktsize)
                          (PeanoNat.Nat.pred ssize))
                        (mul (power2 (S len)) nsize))
                      (PeanoNat.Nat.pred
                        (add (add (add (add psize pktsize) pktsize) ssize)
                          (mul (add (power2 len) (power2 len)) nsize)))
                      (make_red len psize pktsize (PeanoNat.Nat.pred ssize)
                        nsize (Mix (g1, y1, NoRed)) y c2 b p0 b1 c0)), y0))
               | Coq_prodS (_, _, _) -> assert false (* absurd case *))
            | _ -> assert false (* absurd case *))
         | PCRed (_, _) -> assert false (* absurd case *))))

(** val eject_obligations_obligation_2 :
    nat -> 'a1 deque -> ('a1 deque, 'a1) prod **)

let eject_obligations_obligation_2 _ _ =
  assert false (* absurd case *)

(** val eject : nat -> 'a1 deque -> ('a1 deque, 'a1) prod **)

let eject size d =
  match unsafe_eject (S size) d with
  | Some p -> p
  | None -> eject_obligations_obligation_2 size d
