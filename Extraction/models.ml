(* open Classes *)
open Datatypes
open List
open Nat
open Buffer
open Types

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val path_seq : nat -> kind -> color -> 'a1 path -> 'a1 list **)

let rec path_seq _ _ _ p =
  let ne_cdeque_seq0 = fun _ _ cd ->
    match cd with
    | Only_path (lvl0, g, r, p0) ->
      path_seq lvl0 Only (Mix (g, NoYellow, NoOrange, r)) p0
    | Pair_green (lvl0, pl, pr) ->
      app
        (path_seq lvl0 Left (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) pl)
        (path_seq lvl0 Right (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) pr)
    | Pair_red (lvl0, cl, cr, pl, pr) ->
      app (path_seq lvl0 Left cl pl) (path_seq lvl0 Right cr pr)
  in
  let cdeque_seq0 = fun _ _ cd ->
    match cd with
    | Empty _ -> Coq_nil
    | NonEmpty (lvl0, g, r, necd) ->
      ne_cdeque_seq0 lvl0 (Mix (g, NoYellow, NoOrange, r)) necd
  in
  let stored_triple_seq0 =
    let rec stored_triple_seq0 _ st =
      let buffer_seq0 = fun lvl q b -> map_buffer stored_triple_seq0 lvl q b
      in
      (match st with
       | ST_ground b -> Coq_cons (b, Coq_nil)
       | ST_small (lvl0, q, p0) -> buffer_seq0 lvl0 (add (S (S (S O))) q) p0
       | ST_triple (lvl0, qp, qs, c0, p0, cd, s) ->
         app (buffer_seq0 lvl0 (add (S (S (S O))) qp) p0)
           (app (cdeque_seq0 (S lvl0) c0 cd)
             (buffer_seq0 lvl0 (add (S (S (S O))) qs) s)))
    in stored_triple_seq0
  in
  let buffer_seq0 = fun lvl q b -> map_buffer stored_triple_seq0 lvl q b in
  let triple_front_seq0 =
    let rec triple_front_seq0 _ _ _ _ _ _ t0 =
      let packet_front_seq0 = fun _ _ _ _ pkt ->
        match pkt with
        | Only_child (lvl0, len0, is_hole0, k0, y, o, _, t1) ->
          triple_front_seq0 lvl0 len0 is_hole0 Only k0 (Mix (NoGreen, y, o,
            NoRed)) t1
        | Left_child (lvl0, len0, is_hole0, k0, y, o, _, t1, _) ->
          triple_front_seq0 lvl0 len0 is_hole0 Left k0 (Mix (NoGreen, y, o,
            NoRed)) t1
        | Right_child (lvl0, len0, is_hole0, k0, y, o, p0, t1) ->
          app
            (path_seq lvl0 Left (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
              p0)
            (triple_front_seq0 lvl0 len0 is_hole0 Right k0 (Mix (NoGreen, y,
              o, NoRed)) t1)
      in
      (match t0 with
       | Hole (_, _) -> Coq_nil
       | Small (lvl0, qp, _, _, p0, _, _) -> buffer_seq0 lvl0 qp p0
       | Green (lvl0, qp, _, _, g, r, p0, cd, _, _) ->
         app (buffer_seq0 lvl0 qp p0)
           (ne_cdeque_seq0 (S lvl0) (Mix (g, NoYellow, NoOrange, r)) cd)
       | Yellow (lvl0, len0, qp, _, _, k3, p0, pkt, _, _) ->
         app (buffer_seq0 lvl0 qp p0)
           (packet_front_seq0 (S lvl0) len0 Preferred_left k3 pkt)
       | Orange (lvl0, len0, qp, _, _, k3, p0, pkt, _, _) ->
         app (buffer_seq0 lvl0 qp p0)
           (packet_front_seq0 (S lvl0) len0 Preferred_right k3 pkt)
       | Red (lvl0, qp, _, _, p0, cd, _, _) ->
         app (buffer_seq0 lvl0 qp p0)
           (ne_cdeque_seq0 (S lvl0) (Mix (SomeGreen, NoYellow, NoOrange,
             NoRed)) cd))
    in triple_front_seq0
  in
  let triple_rear_seq0 =
    let rec triple_rear_seq0 _ _ _ _ _ _ t0 =
      let packet_rear_seq0 = fun _ _ _ _ pkt ->
        match pkt with
        | Only_child (lvl0, len0, is_hole0, k0, y, o, _, t1) ->
          triple_rear_seq0 lvl0 len0 is_hole0 Only k0 (Mix (NoGreen, y, o,
            NoRed)) t1
        | Left_child (lvl0, len0, is_hole0, k0, y, o, c0, t1, p0) ->
          app
            (triple_rear_seq0 lvl0 len0 is_hole0 Left k0 (Mix (NoGreen, y, o,
              NoRed)) t1) (path_seq lvl0 Right c0 p0)
        | Right_child (lvl0, len0, is_hole0, k0, y, o, _, t1) ->
          triple_rear_seq0 lvl0 len0 is_hole0 Right k0 (Mix (NoGreen, y, o,
            NoRed)) t1
      in
      (match t0 with
       | Hole (_, _) -> Coq_nil
       | Small (lvl0, _, qs, _, _, s, _) -> buffer_seq0 lvl0 qs s
       | Green (lvl0, _, qs, _, _, _, _, _, s, _) -> buffer_seq0 lvl0 qs s
       | Yellow (lvl0, len0, _, qs, _, k3, _, pkt, s, _) ->
         app (packet_rear_seq0 (S lvl0) len0 Preferred_left k3 pkt)
           (buffer_seq0 lvl0 qs s)
       | Orange (lvl0, len0, _, qs, _, k3, _, pkt, s, _) ->
         app (packet_rear_seq0 (S lvl0) len0 Preferred_right k3 pkt)
           (buffer_seq0 lvl0 qs s)
       | Red (lvl0, _, qs, _, _, _, s, _) -> buffer_seq0 lvl0 qs s)
    in triple_rear_seq0
  in
  let Children (lvl0, len, nlvl, is_hole, k1, k2, g, y, o, r, natur, adopt) =
    p
  in
  app
    (triple_front_seq0 lvl0 len is_hole k1 k2 (Mix (NoGreen, y, o, NoRed))
      natur)
    (app
      (triple_front_seq0 nlvl O Coq_false k2 k2 (Mix (g, NoYellow, NoOrange,
        r)) adopt)
      (app
        (triple_rear_seq0 nlvl O Coq_false k2 k2 (Mix (g, NoYellow, NoOrange,
          r)) adopt)
        (triple_rear_seq0 lvl0 len is_hole k1 k2 (Mix (NoGreen, y, o, NoRed))
          natur)))

(** val ne_cdeque_seq : nat -> color -> 'a1 non_empty_cdeque -> 'a1 list **)

let ne_cdeque_seq _ _ = function
| Only_path (lvl, g, r, p) ->
  path_seq lvl Only (Mix (g, NoYellow, NoOrange, r)) p
| Pair_green (lvl, p, p0) ->
  app (path_seq lvl Left (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) p)
    (path_seq lvl Right (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) p0)
| Pair_red (lvl, cl, cr, p, p0) ->
  app (path_seq lvl Left cl p) (path_seq lvl Right cr p0)

type 'a ne_cdeque_seq_graph =
| Coq_ne_cdeque_seq_graph_equation_1 of nat * green_hue * red_hue * 'a path
| Coq_ne_cdeque_seq_graph_equation_2 of nat * 'a path * 'a path
| Coq_ne_cdeque_seq_graph_equation_3 of nat * color * color * 'a path
   * 'a path

(** val ne_cdeque_seq_graph_rect :
    (__ -> nat -> green_hue -> red_hue -> __ path -> 'a1) -> (__ -> nat -> __
    path -> __ path -> 'a1) -> (__ -> nat -> color -> color -> __ path -> __
    path -> 'a1) -> nat -> color -> 'a2 non_empty_cdeque -> 'a2 list -> 'a2
    ne_cdeque_seq_graph -> 'a1 **)

let ne_cdeque_seq_graph_rect f f0 f1 _ _ _ _ = function
| Coq_ne_cdeque_seq_graph_equation_1 (lvl, g, r, p) ->
  Obj.magic f __ lvl g r p
| Coq_ne_cdeque_seq_graph_equation_2 (lvl, pl, pd) ->
  Obj.magic f0 __ lvl pl pd
| Coq_ne_cdeque_seq_graph_equation_3 (lvl, cl, cr, pl, pd) ->
  Obj.magic f1 __ lvl cl cr pl pd

(** val ne_cdeque_seq_graph_correct :
    nat -> color -> 'a1 non_empty_cdeque -> 'a1 ne_cdeque_seq_graph **)

let ne_cdeque_seq_graph_correct _ _ = function
| Only_path (lvl, g, r, p) ->
  Coq_ne_cdeque_seq_graph_equation_1 (lvl, g, r, p)
| Pair_green (lvl, p, p0) -> Coq_ne_cdeque_seq_graph_equation_2 (lvl, p, p0)
| Pair_red (lvl, cl, cr, p, p0) ->
  Coq_ne_cdeque_seq_graph_equation_3 (lvl, cl, cr, p, p0)

(** val ne_cdeque_seq_elim :
    (__ -> nat -> green_hue -> red_hue -> __ path -> 'a1) -> (__ -> nat -> __
    path -> __ path -> 'a1) -> (__ -> nat -> color -> color -> __ path -> __
    path -> 'a1) -> nat -> color -> 'a2 non_empty_cdeque -> 'a1 **)

let ne_cdeque_seq_elim f f0 f1 lvl c n =
  match ne_cdeque_seq_graph_correct lvl c n with
  | Coq_ne_cdeque_seq_graph_equation_1 (lvl0, g, r, p) ->
    Obj.magic f __ lvl0 g r p
  | Coq_ne_cdeque_seq_graph_equation_2 (lvl0, pl, pd) ->
    Obj.magic f0 __ lvl0 pl pd
  | Coq_ne_cdeque_seq_graph_equation_3 (lvl0, cl, cr, pl, pd) ->
    Obj.magic f1 __ lvl0 cl cr pl pd

(** val coq_FunctionalElimination_ne_cdeque_seq :
    (__ -> nat -> green_hue -> red_hue -> __ path -> __) -> (__ -> nat -> __
    path -> __ path -> __) -> (__ -> nat -> color -> color -> __ path -> __
    path -> __) -> nat -> color -> __ non_empty_cdeque -> __ **)

let coq_FunctionalElimination_ne_cdeque_seq =
  ne_cdeque_seq_elim

(** val coq_FunctionalInduction_ne_cdeque_seq :
    (__ -> nat -> color -> __ non_empty_cdeque -> __ list)
    coq_FunctionalInduction **)

let coq_FunctionalInduction_ne_cdeque_seq =
  Obj.magic (fun _ -> ne_cdeque_seq_graph_correct)

(** val cdeque_seq : nat -> color -> 'a1 cdeque -> 'a1 list **)

let cdeque_seq _ _ = function
| Empty _ -> Coq_nil
| NonEmpty (lvl, g, r, n) ->
  ne_cdeque_seq lvl (Mix (g, NoYellow, NoOrange, r)) n

type 'a cdeque_seq_graph =
| Coq_cdeque_seq_graph_equation_1 of nat
| Coq_cdeque_seq_graph_equation_2 of nat * green_hue * red_hue
   * 'a non_empty_cdeque

(** val cdeque_seq_graph_rect :
    (__ -> nat -> 'a1) -> (__ -> nat -> green_hue -> red_hue -> __
    non_empty_cdeque -> 'a1) -> nat -> color -> 'a2 cdeque -> 'a2 list -> 'a2
    cdeque_seq_graph -> 'a1 **)

let cdeque_seq_graph_rect f f0 _ _ _ _ = function
| Coq_cdeque_seq_graph_equation_1 lvl -> f __ lvl
| Coq_cdeque_seq_graph_equation_2 (lvl, g, r, cd) ->
  Obj.magic f0 __ lvl g r cd

(** val cdeque_seq_graph_correct :
    nat -> color -> 'a1 cdeque -> 'a1 cdeque_seq_graph **)

let cdeque_seq_graph_correct _ _ = function
| Empty lvl -> Coq_cdeque_seq_graph_equation_1 lvl
| NonEmpty (lvl, g, r, n) -> Coq_cdeque_seq_graph_equation_2 (lvl, g, r, n)

(** val cdeque_seq_elim :
    (__ -> nat -> 'a1) -> (__ -> nat -> green_hue -> red_hue -> __
    non_empty_cdeque -> 'a1) -> nat -> color -> 'a2 cdeque -> 'a1 **)

let cdeque_seq_elim f f0 lvl c c0 =
  match cdeque_seq_graph_correct lvl c c0 with
  | Coq_cdeque_seq_graph_equation_1 lvl0 -> f __ lvl0
  | Coq_cdeque_seq_graph_equation_2 (lvl0, g, r, cd) ->
    Obj.magic f0 __ lvl0 g r cd

(** val coq_FunctionalElimination_cdeque_seq :
    (__ -> nat -> __) -> (__ -> nat -> green_hue -> red_hue -> __
    non_empty_cdeque -> __) -> nat -> color -> __ cdeque -> __ **)

let coq_FunctionalElimination_cdeque_seq =
  cdeque_seq_elim

(** val coq_FunctionalInduction_cdeque_seq :
    (__ -> nat -> color -> __ cdeque -> __ list) coq_FunctionalInduction **)

let coq_FunctionalInduction_cdeque_seq =
  Obj.magic (fun _ -> cdeque_seq_graph_correct)

(** val stored_triple_seq : nat -> 'a1 stored_triple -> 'a1 list **)

let rec stored_triple_seq _ st =
  let buffer_seq0 = fun lvl q b -> map_buffer stored_triple_seq lvl q b in
  (match st with
   | ST_ground a -> Coq_cons (a, Coq_nil)
   | ST_small (lvl0, q, p) -> buffer_seq0 lvl0 (add (S (S (S O))) q) p
   | ST_triple (lvl0, qp, qs, c, p, cd, s) ->
     app (buffer_seq0 lvl0 (add (S (S (S O))) qp) p)
       (app (cdeque_seq (S lvl0) c cd)
         (buffer_seq0 lvl0 (add (S (S (S O))) qs) s)))

(** val buffer_seq : nat -> nat -> 'a1 stored_triple t -> 'a1 list **)

let buffer_seq lvl q p =
  concat (map (stored_triple_seq lvl) (seq q p))

type 'a buffer_seq_graph =
| Coq_buffer_seq_graph_equation_1 of nat * nat * 'a stored_triple t

(** val buffer_seq_graph_rect :
    (__ -> nat -> nat -> __ stored_triple t -> 'a1) -> nat -> nat -> 'a2
    stored_triple t -> 'a2 list -> 'a2 buffer_seq_graph -> 'a1 **)

let buffer_seq_graph_rect f _ _ _ _ = function
| Coq_buffer_seq_graph_equation_1 (lvl, q, p) -> Obj.magic f __ lvl q p

(** val buffer_seq_graph_correct :
    nat -> nat -> 'a1 stored_triple t -> 'a1 buffer_seq_graph **)

let buffer_seq_graph_correct lvl q t0 =
  Coq_buffer_seq_graph_equation_1 (lvl, q, t0)

(** val buffer_seq_elim :
    (__ -> nat -> nat -> __ stored_triple t -> 'a1) -> nat -> nat -> 'a2
    stored_triple t -> 'a1 **)

let buffer_seq_elim f lvl q t0 =
  let Coq_buffer_seq_graph_equation_1 (lvl0, q0, p) =
    buffer_seq_graph_correct lvl q t0
  in
  Obj.magic f __ lvl0 q0 p

(** val coq_FunctionalElimination_buffer_seq :
    (__ -> nat -> nat -> __ stored_triple t -> __) -> nat -> nat -> __
    stored_triple t -> __ **)

let coq_FunctionalElimination_buffer_seq =
  buffer_seq_elim

(** val coq_FunctionalInduction_buffer_seq :
    (__ -> nat -> nat -> __ stored_triple t -> __ list)
    coq_FunctionalInduction **)

let coq_FunctionalInduction_buffer_seq =
  Obj.magic (fun _ -> buffer_seq_graph_correct)

(** val path_buffer_seq : nat -> nat -> 'a1 stored_triple t -> 'a1 list **)

let path_buffer_seq lvl q b =
  map_buffer (fun lvl0 ->
    let rec stored_triple_seq0 _ = function
    | ST_ground b0 -> Coq_cons (b0, Coq_nil)
    | ST_small (lvl', q0, p) ->
      map_buffer stored_triple_seq0 lvl' (add (S (S (S O))) q0) p
    | ST_triple (lvl', qp, qs, c, p, cd, s) ->
      app (map_buffer stored_triple_seq0 lvl' (add (S (S (S O))) qp) p)
        (app (cdeque_seq (S lvl') c cd)
          (map_buffer stored_triple_seq0 lvl' (add (S (S (S O))) qs) s))
    in stored_triple_seq0 lvl0) lvl q b

(** val triple_front_seq :
    nat -> nat -> bool -> kind -> kind -> color -> 'a1 triple -> 'a1 list **)

let rec triple_front_seq _ _ _ _ _ _ t0 =
  let packet_front_seq0 = fun _ _ _ _ pkt ->
    match pkt with
    | Only_child (lvl0, len0, is_hole0, k0, y, o, _, t1) ->
      triple_front_seq lvl0 len0 is_hole0 Only k0 (Mix (NoGreen, y, o,
        NoRed)) t1
    | Left_child (lvl0, len0, is_hole0, k0, y, o, _, t1, _) ->
      triple_front_seq lvl0 len0 is_hole0 Left k0 (Mix (NoGreen, y, o,
        NoRed)) t1
    | Right_child (lvl0, len0, is_hole0, k0, y, o, p, t1) ->
      app (path_seq lvl0 Left (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) p)
        (triple_front_seq lvl0 len0 is_hole0 Right k0 (Mix (NoGreen, y, o,
          NoRed)) t1)
  in
  (match t0 with
   | Hole (_, _) -> Coq_nil
   | Small (lvl0, qp, _, _, p, _, _) -> path_buffer_seq lvl0 qp p
   | Green (lvl0, qp, _, _, g, r, p, cd, _, _) ->
     app (path_buffer_seq lvl0 qp p)
       (ne_cdeque_seq (S lvl0) (Mix (g, NoYellow, NoOrange, r)) cd)
   | Yellow (lvl0, len0, qp, _, _, k3, p, pkt, _, _) ->
     app (path_buffer_seq lvl0 qp p)
       (packet_front_seq0 (S lvl0) len0 Preferred_left k3 pkt)
   | Orange (lvl0, len0, qp, _, _, k3, p, pkt, _, _) ->
     app (path_buffer_seq lvl0 qp p)
       (packet_front_seq0 (S lvl0) len0 Preferred_right k3 pkt)
   | Red (lvl0, qp, _, _, p, cd, _, _) ->
     app (path_buffer_seq lvl0 qp p)
       (ne_cdeque_seq (S lvl0) (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
         cd))

(** val packet_front_seq :
    nat -> nat -> preferred_child -> kind -> 'a1 packet -> 'a1 list **)

let packet_front_seq _ _ _ _ = function
| Only_child (lvl, len, is_hole, k, y, o, _, t0) ->
  triple_front_seq lvl len is_hole Only k (Mix (NoGreen, y, o, NoRed)) t0
| Left_child (lvl, len, is_hole, k, y, o, _, t0, _) ->
  triple_front_seq lvl len is_hole Left k (Mix (NoGreen, y, o, NoRed)) t0
| Right_child (lvl, len, is_hole, k, y, o, p0, t0) ->
  app (path_seq lvl Left (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) p0)
    (triple_front_seq lvl len is_hole Right k (Mix (NoGreen, y, o, NoRed)) t0)

type 'a packet_front_seq_graph =
| Coq_packet_front_seq_graph_equation_1 of nat * nat * preferred_child * 
   kind * bool * yellow_hue * orange_hue * 'a triple
| Coq_packet_front_seq_graph_equation_2 of nat * nat * kind * bool
   * yellow_hue * orange_hue * color * 'a triple * 'a path
| Coq_packet_front_seq_graph_equation_3 of nat * nat * kind * bool
   * yellow_hue * orange_hue * 'a path * 'a triple

(** val packet_front_seq_graph_rect :
    (__ -> nat -> nat -> preferred_child -> kind -> bool -> yellow_hue ->
    orange_hue -> __ triple -> 'a1) -> (__ -> nat -> nat -> kind -> bool ->
    yellow_hue -> orange_hue -> color -> __ triple -> __ path -> 'a1) -> (__
    -> nat -> nat -> kind -> bool -> yellow_hue -> orange_hue -> __ path ->
    __ triple -> 'a1) -> nat -> nat -> preferred_child -> kind -> 'a2 packet
    -> 'a2 list -> 'a2 packet_front_seq_graph -> 'a1 **)

let packet_front_seq_graph_rect f f0 f1 _ _ _ _ _ _ = function
| Coq_packet_front_seq_graph_equation_1 (lvl, len, pc, k, is_hole, y, o0, t0) ->
  Obj.magic f __ lvl len pc k is_hole y o0 t0
| Coq_packet_front_seq_graph_equation_2 (lvl, len, k, is_hole0, y0, o1, c,
                                         t0, p) ->
  Obj.magic f0 __ lvl len k is_hole0 y0 o1 c t0 p
| Coq_packet_front_seq_graph_equation_3 (lvl, len, k, is_hole1, y1, o2, p, t0) ->
  Obj.magic f1 __ lvl len k is_hole1 y1 o2 p t0

(** val packet_front_seq_graph_correct :
    nat -> nat -> preferred_child -> kind -> 'a1 packet -> 'a1
    packet_front_seq_graph **)

let packet_front_seq_graph_correct _ _ _ _ = function
| Only_child (lvl, len, is_hole, k, y, o, pref, t0) ->
  Coq_packet_front_seq_graph_equation_1 (lvl, len, pref, k, is_hole, y, o, t0)
| Left_child (lvl, len, is_hole, k, y, o, c, t0, p0) ->
  Coq_packet_front_seq_graph_equation_2 (lvl, len, k, is_hole, y, o, c, t0,
    p0)
| Right_child (lvl, len, is_hole, k, y, o, p0, t0) ->
  Coq_packet_front_seq_graph_equation_3 (lvl, len, k, is_hole, y, o, p0, t0)

(** val packet_front_seq_elim :
    (__ -> nat -> nat -> preferred_child -> kind -> bool -> yellow_hue ->
    orange_hue -> __ triple -> 'a1) -> (__ -> nat -> nat -> kind -> bool ->
    yellow_hue -> orange_hue -> color -> __ triple -> __ path -> 'a1) -> (__
    -> nat -> nat -> kind -> bool -> yellow_hue -> orange_hue -> __ path ->
    __ triple -> 'a1) -> nat -> nat -> preferred_child -> kind -> 'a2 packet
    -> 'a1 **)

let packet_front_seq_elim f f0 f1 lvl len pc k p =
  match packet_front_seq_graph_correct lvl len pc k p with
  | Coq_packet_front_seq_graph_equation_1 (lvl0, len0, pc0, k0, is_hole, y,
                                           o0, t0) ->
    Obj.magic f __ lvl0 len0 pc0 k0 is_hole y o0 t0
  | Coq_packet_front_seq_graph_equation_2 (lvl0, len0, k0, is_hole0, y0, o1,
                                           c, t0, p0) ->
    Obj.magic f0 __ lvl0 len0 k0 is_hole0 y0 o1 c t0 p0
  | Coq_packet_front_seq_graph_equation_3 (lvl0, len0, k0, is_hole1, y1, o2,
                                           p0, t0) ->
    Obj.magic f1 __ lvl0 len0 k0 is_hole1 y1 o2 p0 t0

(** val coq_FunctionalElimination_packet_front_seq :
    (__ -> nat -> nat -> preferred_child -> kind -> bool -> yellow_hue ->
    orange_hue -> __ triple -> __) -> (__ -> nat -> nat -> kind -> bool ->
    yellow_hue -> orange_hue -> color -> __ triple -> __ path -> __) -> (__
    -> nat -> nat -> kind -> bool -> yellow_hue -> orange_hue -> __ path ->
    __ triple -> __) -> nat -> nat -> preferred_child -> kind -> __ packet ->
    __ **)

let coq_FunctionalElimination_packet_front_seq =
  packet_front_seq_elim

(** val coq_FunctionalInduction_packet_front_seq :
    (__ -> nat -> nat -> preferred_child -> kind -> __ packet -> __ list)
    coq_FunctionalInduction **)

let coq_FunctionalInduction_packet_front_seq =
  Obj.magic (fun _ -> packet_front_seq_graph_correct)

(** val triple_rear_seq :
    nat -> nat -> bool -> kind -> kind -> color -> 'a1 triple -> 'a1 list **)

let rec triple_rear_seq _ _ _ _ _ _ t0 =
  let packet_rear_seq0 = fun _ _ _ _ pkt ->
    match pkt with
    | Only_child (lvl0, len0, is_hole0, k0, y, o, _, t1) ->
      triple_rear_seq lvl0 len0 is_hole0 Only k0 (Mix (NoGreen, y, o, NoRed))
        t1
    | Left_child (lvl0, len0, is_hole0, k0, y, o, c0, t1, p) ->
      app
        (triple_rear_seq lvl0 len0 is_hole0 Left k0 (Mix (NoGreen, y, o,
          NoRed)) t1) (path_seq lvl0 Right c0 p)
    | Right_child (lvl0, len0, is_hole0, k0, y, o, _, t1) ->
      triple_rear_seq lvl0 len0 is_hole0 Right k0 (Mix (NoGreen, y, o,
        NoRed)) t1
  in
  (match t0 with
   | Hole (_, _) -> Coq_nil
   | Small (lvl0, _, qs, _, _, s, _) -> path_buffer_seq lvl0 qs s
   | Green (lvl0, _, qs, _, _, _, _, _, s, _) -> path_buffer_seq lvl0 qs s
   | Yellow (lvl0, len0, _, qs, _, k3, _, pkt, s, _) ->
     app (packet_rear_seq0 (S lvl0) len0 Preferred_left k3 pkt)
       (path_buffer_seq lvl0 qs s)
   | Orange (lvl0, len0, _, qs, _, k3, _, pkt, s, _) ->
     app (packet_rear_seq0 (S lvl0) len0 Preferred_right k3 pkt)
       (path_buffer_seq lvl0 qs s)
   | Red (lvl0, _, qs, _, _, _, s, _) -> path_buffer_seq lvl0 qs s)

(** val packet_rear_seq :
    nat -> nat -> preferred_child -> kind -> 'a1 packet -> 'a1 list **)

let packet_rear_seq _ _ _ _ = function
| Only_child (lvl, len, is_hole, k, y, o, _, t0) ->
  triple_rear_seq lvl len is_hole Only k (Mix (NoGreen, y, o, NoRed)) t0
| Left_child (lvl, len, is_hole, k, y, o, c, t0, p0) ->
  app
    (triple_rear_seq lvl len is_hole Left k (Mix (NoGreen, y, o, NoRed)) t0)
    (path_seq lvl Right c p0)
| Right_child (lvl, len, is_hole, k, y, o, _, t0) ->
  triple_rear_seq lvl len is_hole Right k (Mix (NoGreen, y, o, NoRed)) t0

type 'a packet_rear_seq_graph =
| Coq_packet_rear_seq_graph_equation_1 of nat * nat * preferred_child * 
   kind * bool * yellow_hue * orange_hue * 'a triple
| Coq_packet_rear_seq_graph_equation_2 of nat * nat * kind * bool
   * yellow_hue * orange_hue * color * 'a triple * 'a path
| Coq_packet_rear_seq_graph_equation_3 of nat * nat * kind * bool
   * yellow_hue * orange_hue * 'a path * 'a triple

(** val packet_rear_seq_graph_rect :
    (__ -> nat -> nat -> preferred_child -> kind -> bool -> yellow_hue ->
    orange_hue -> __ triple -> 'a1) -> (__ -> nat -> nat -> kind -> bool ->
    yellow_hue -> orange_hue -> color -> __ triple -> __ path -> 'a1) -> (__
    -> nat -> nat -> kind -> bool -> yellow_hue -> orange_hue -> __ path ->
    __ triple -> 'a1) -> nat -> nat -> preferred_child -> kind -> 'a2 packet
    -> 'a2 list -> 'a2 packet_rear_seq_graph -> 'a1 **)

let packet_rear_seq_graph_rect f f0 f1 _ _ _ _ _ _ = function
| Coq_packet_rear_seq_graph_equation_1 (lvl, len, pc, k, is_hole, y, o0, t0) ->
  Obj.magic f __ lvl len pc k is_hole y o0 t0
| Coq_packet_rear_seq_graph_equation_2 (lvl, len, k, is_hole0, y0, o1, c, t0,
                                        p) ->
  Obj.magic f0 __ lvl len k is_hole0 y0 o1 c t0 p
| Coq_packet_rear_seq_graph_equation_3 (lvl, len, k, is_hole1, y1, o2, p1, t0) ->
  Obj.magic f1 __ lvl len k is_hole1 y1 o2 p1 t0

(** val packet_rear_seq_graph_correct :
    nat -> nat -> preferred_child -> kind -> 'a1 packet -> 'a1
    packet_rear_seq_graph **)

let packet_rear_seq_graph_correct _ _ _ _ = function
| Only_child (lvl, len, is_hole, k, y, o, pref, t0) ->
  Coq_packet_rear_seq_graph_equation_1 (lvl, len, pref, k, is_hole, y, o, t0)
| Left_child (lvl, len, is_hole, k, y, o, c, t0, p0) ->
  Coq_packet_rear_seq_graph_equation_2 (lvl, len, k, is_hole, y, o, c, t0, p0)
| Right_child (lvl, len, is_hole, k, y, o, p0, t0) ->
  Coq_packet_rear_seq_graph_equation_3 (lvl, len, k, is_hole, y, o, p0, t0)

(** val packet_rear_seq_elim :
    (__ -> nat -> nat -> preferred_child -> kind -> bool -> yellow_hue ->
    orange_hue -> __ triple -> 'a1) -> (__ -> nat -> nat -> kind -> bool ->
    yellow_hue -> orange_hue -> color -> __ triple -> __ path -> 'a1) -> (__
    -> nat -> nat -> kind -> bool -> yellow_hue -> orange_hue -> __ path ->
    __ triple -> 'a1) -> nat -> nat -> preferred_child -> kind -> 'a2 packet
    -> 'a1 **)

let packet_rear_seq_elim f f0 f1 lvl len pc k p =
  match packet_rear_seq_graph_correct lvl len pc k p with
  | Coq_packet_rear_seq_graph_equation_1 (lvl0, len0, pc0, k0, is_hole, y,
                                          o0, t0) ->
    Obj.magic f __ lvl0 len0 pc0 k0 is_hole y o0 t0
  | Coq_packet_rear_seq_graph_equation_2 (lvl0, len0, k0, is_hole0, y0, o1,
                                          c, t0, p0) ->
    Obj.magic f0 __ lvl0 len0 k0 is_hole0 y0 o1 c t0 p0
  | Coq_packet_rear_seq_graph_equation_3 (lvl0, len0, k0, is_hole1, y1, o2,
                                          p0, t0) ->
    Obj.magic f1 __ lvl0 len0 k0 is_hole1 y1 o2 p0 t0

(** val coq_FunctionalElimination_packet_rear_seq :
    (__ -> nat -> nat -> preferred_child -> kind -> bool -> yellow_hue ->
    orange_hue -> __ triple -> __) -> (__ -> nat -> nat -> kind -> bool ->
    yellow_hue -> orange_hue -> color -> __ triple -> __ path -> __) -> (__
    -> nat -> nat -> kind -> bool -> yellow_hue -> orange_hue -> __ path ->
    __ triple -> __) -> nat -> nat -> preferred_child -> kind -> __ packet ->
    __ **)

let coq_FunctionalElimination_packet_rear_seq =
  packet_rear_seq_elim

(** val coq_FunctionalInduction_packet_rear_seq :
    (__ -> nat -> nat -> preferred_child -> kind -> __ packet -> __ list)
    coq_FunctionalInduction **)

let coq_FunctionalInduction_packet_rear_seq =
  Obj.magic (fun _ -> packet_rear_seq_graph_correct)

(** val triple_seq :
    nat -> nat -> bool -> kind -> kind -> color -> 'a1 triple -> 'a1 list **)

let triple_seq lvl len is_hole k1 k2 c t0 =
  app (triple_front_seq lvl len is_hole k1 k2 c t0)
    (triple_rear_seq lvl len is_hole k1 k2 c t0)

type 'a triple_seq_graph =
| Coq_triple_seq_graph_equation_1 of nat * nat * bool * kind * kind * 
   color * 'a triple

(** val triple_seq_graph_rect :
    (__ -> nat -> nat -> bool -> kind -> kind -> color -> __ triple -> 'a1)
    -> nat -> nat -> bool -> kind -> kind -> color -> 'a2 triple -> 'a2 list
    -> 'a2 triple_seq_graph -> 'a1 **)

let triple_seq_graph_rect f _ _ _ _ _ _ _ _ = function
| Coq_triple_seq_graph_equation_1 (lvl, len, is_hole, k1, k2, c, t1) ->
  Obj.magic f __ lvl len is_hole k1 k2 c t1

(** val triple_seq_graph_correct :
    nat -> nat -> bool -> kind -> kind -> color -> 'a1 triple -> 'a1
    triple_seq_graph **)

let triple_seq_graph_correct lvl len is_hole k1 k2 c t0 =
  Coq_triple_seq_graph_equation_1 (lvl, len, is_hole, k1, k2, c, t0)

(** val triple_seq_elim :
    (__ -> nat -> nat -> bool -> kind -> kind -> color -> __ triple -> 'a1)
    -> nat -> nat -> bool -> kind -> kind -> color -> 'a2 triple -> 'a1 **)

let triple_seq_elim f lvl len is_hole k1 k2 c t0 =
  let Coq_triple_seq_graph_equation_1 (lvl0, len0, is_hole0, k3, k4, c0, t1) =
    triple_seq_graph_correct lvl len is_hole k1 k2 c t0
  in
  Obj.magic f __ lvl0 len0 is_hole0 k3 k4 c0 t1

(** val coq_FunctionalElimination_triple_seq :
    (__ -> nat -> nat -> bool -> kind -> kind -> color -> __ triple -> __) ->
    nat -> nat -> bool -> kind -> kind -> color -> __ triple -> __ **)

let coq_FunctionalElimination_triple_seq =
  triple_seq_elim

(** val coq_FunctionalInduction_triple_seq :
    (__ -> nat -> nat -> bool -> kind -> kind -> color -> __ triple -> __
    list) coq_FunctionalInduction **)

let coq_FunctionalInduction_triple_seq =
  Obj.magic (fun _ -> triple_seq_graph_correct)

(** val pref_left_seq : nat -> 'a1 pref_left -> 'a1 list **)

let pref_left_seq lvl = function
| Pref_left (len, _, k, g, r, p0, t0) ->
  app (packet_front_seq lvl len Preferred_left k p0)
    (app
      (triple_seq (add len lvl) O Coq_false k k (Mix (g, NoYellow, NoOrange,
        r)) t0) (packet_rear_seq lvl len Preferred_left k p0))

type 'a pref_left_seq_graph =
| Coq_pref_left_seq_graph_equation_1 of nat * nat * kind * green_hue
   * red_hue * 'a packet * 'a triple

(** val pref_left_seq_graph_rect :
    (__ -> nat -> nat -> kind -> green_hue -> red_hue -> __ packet -> __
    triple -> 'a1) -> nat -> 'a2 pref_left -> 'a2 list -> 'a2
    pref_left_seq_graph -> 'a1 **)

let pref_left_seq_graph_rect f _ _ _ = function
| Coq_pref_left_seq_graph_equation_1 (lvl, len, k, g, r, pkt, t0) ->
  Obj.magic f __ lvl len k g r pkt t0

(** val pref_left_seq_graph_correct :
    nat -> 'a1 pref_left -> 'a1 pref_left_seq_graph **)

let pref_left_seq_graph_correct lvl = function
| Pref_left (len, _, k, g, r, p0, t0) ->
  Coq_pref_left_seq_graph_equation_1 (lvl, len, k, g, r, p0, t0)

(** val pref_left_seq_elim :
    (__ -> nat -> nat -> kind -> green_hue -> red_hue -> __ packet -> __
    triple -> 'a1) -> nat -> 'a2 pref_left -> 'a1 **)

let pref_left_seq_elim f lvl p =
  let Coq_pref_left_seq_graph_equation_1 (lvl0, len, k, g, r, pkt, t0) =
    pref_left_seq_graph_correct lvl p
  in
  Obj.magic f __ lvl0 len k g r pkt t0

(** val coq_FunctionalElimination_pref_left_seq :
    (__ -> nat -> nat -> kind -> green_hue -> red_hue -> __ packet -> __
    triple -> __) -> nat -> __ pref_left -> __ **)

let coq_FunctionalElimination_pref_left_seq =
  pref_left_seq_elim

(** val coq_FunctionalInduction_pref_left_seq :
    (__ -> nat -> __ pref_left -> __ list) coq_FunctionalInduction **)

let coq_FunctionalInduction_pref_left_seq =
  Obj.magic (fun _ -> pref_left_seq_graph_correct)

(** val pref_right_seq : nat -> 'a1 pref_right -> 'a1 list **)

let pref_right_seq lvl = function
| Pref_right (len, _, k, g, r, p0, t0) ->
  app (packet_front_seq lvl len Preferred_right k p0)
    (app
      (triple_seq (add len lvl) O Coq_false k k (Mix (g, NoYellow, NoOrange,
        r)) t0) (packet_rear_seq lvl len Preferred_right k p0))

type 'a pref_right_seq_graph =
| Coq_pref_right_seq_graph_equation_1 of nat * nat * kind * green_hue
   * red_hue * 'a packet * 'a triple

(** val pref_right_seq_graph_rect :
    (__ -> nat -> nat -> kind -> green_hue -> red_hue -> __ packet -> __
    triple -> 'a1) -> nat -> 'a2 pref_right -> 'a2 list -> 'a2
    pref_right_seq_graph -> 'a1 **)

let pref_right_seq_graph_rect f _ _ _ = function
| Coq_pref_right_seq_graph_equation_1 (lvl, len, k, g, r, pkt, t0) ->
  Obj.magic f __ lvl len k g r pkt t0

(** val pref_right_seq_graph_correct :
    nat -> 'a1 pref_right -> 'a1 pref_right_seq_graph **)

let pref_right_seq_graph_correct lvl = function
| Pref_right (len, _, k, g, r, p0, t0) ->
  Coq_pref_right_seq_graph_equation_1 (lvl, len, k, g, r, p0, t0)

(** val pref_right_seq_elim :
    (__ -> nat -> nat -> kind -> green_hue -> red_hue -> __ packet -> __
    triple -> 'a1) -> nat -> 'a2 pref_right -> 'a1 **)

let pref_right_seq_elim f lvl p =
  let Coq_pref_right_seq_graph_equation_1 (lvl0, len, k, g, r, pkt, t0) =
    pref_right_seq_graph_correct lvl p
  in
  Obj.magic f __ lvl0 len k g r pkt t0

(** val coq_FunctionalElimination_pref_right_seq :
    (__ -> nat -> nat -> kind -> green_hue -> red_hue -> __ packet -> __
    triple -> __) -> nat -> __ pref_right -> __ **)

let coq_FunctionalElimination_pref_right_seq =
  pref_right_seq_elim

(** val coq_FunctionalInduction_pref_right_seq :
    (__ -> nat -> __ pref_right -> __ list) coq_FunctionalInduction **)

let coq_FunctionalInduction_pref_right_seq =
  Obj.magic (fun _ -> pref_right_seq_graph_correct)

(** val buffer_12_seq : nat -> 'a1 buffer_12 -> 'a1 list **)

let buffer_12_seq lvl = function
| Coq_pair (s, v) ->
  app (stored_triple_seq lvl s)
    (concat (map (stored_triple_seq lvl) (vector_seq (S O) v)))

type 'a buffer_12_seq_graph =
| Coq_buffer_12_seq_graph_equation_1 of nat * 'a stored_triple
   * 'a stored_triple vector

(** val buffer_12_seq_graph_rect :
    (__ -> nat -> __ stored_triple -> __ stored_triple vector -> 'a1) -> nat
    -> 'a2 buffer_12 -> 'a2 list -> 'a2 buffer_12_seq_graph -> 'a1 **)

let buffer_12_seq_graph_rect f _ _ _ = function
| Coq_buffer_12_seq_graph_equation_1 (lvl, x, v) -> Obj.magic f __ lvl x v

(** val buffer_12_seq_graph_correct :
    nat -> 'a1 buffer_12 -> 'a1 buffer_12_seq_graph **)

let buffer_12_seq_graph_correct lvl = function
| Coq_pair (s, v) -> Coq_buffer_12_seq_graph_equation_1 (lvl, s, v)

(** val buffer_12_seq_elim :
    (__ -> nat -> __ stored_triple -> __ stored_triple vector -> 'a1) -> nat
    -> 'a2 buffer_12 -> 'a1 **)

let buffer_12_seq_elim f lvl b =
  let Coq_buffer_12_seq_graph_equation_1 (lvl0, x, v) =
    buffer_12_seq_graph_correct lvl b
  in
  Obj.magic f __ lvl0 x v

(** val coq_FunctionalElimination_buffer_12_seq :
    (__ -> nat -> __ stored_triple -> __ stored_triple vector -> __) -> nat
    -> __ buffer_12 -> __ **)

let coq_FunctionalElimination_buffer_12_seq =
  buffer_12_seq_elim

(** val coq_FunctionalInduction_buffer_12_seq :
    (__ -> nat -> __ buffer_12 -> __ list) coq_FunctionalInduction **)

let coq_FunctionalInduction_buffer_12_seq =
  Obj.magic (fun _ -> buffer_12_seq_graph_correct)

(** val path_attempt_seq :
    nat -> kind -> color -> 'a1 path_attempt -> 'a1 list **)

let path_attempt_seq lvl _ _ = function
| ZeroSix (_, _, v) ->
  concat
    (map (stored_triple_seq lvl) (vector_seq (S (S (S (S (S (S O)))))) v))
| Ok (k, c, p0) -> path_seq lvl k c p0
| Any (k, c, p0) -> path_seq lvl k c p0

type 'a path_attempt_seq_graph =
| Coq_path_attempt_seq_graph_equation_1 of nat * kind * color
   * 'a stored_triple vector
| Coq_path_attempt_seq_graph_equation_2 of nat * kind * color * 'a path
| Coq_path_attempt_seq_graph_equation_3 of nat * kind * color * 'a path

(** val path_attempt_seq_graph_rect :
    (__ -> nat -> kind -> color -> __ stored_triple vector -> 'a1) -> (__ ->
    nat -> kind -> color -> __ path -> 'a1) -> (__ -> nat -> kind -> color ->
    __ path -> 'a1) -> nat -> kind -> color -> 'a2 path_attempt -> 'a2 list
    -> 'a2 path_attempt_seq_graph -> 'a1 **)

let path_attempt_seq_graph_rect f f0 f1 _ _ _ _ _ = function
| Coq_path_attempt_seq_graph_equation_1 (lvl, k, c, v) ->
  Obj.magic f __ lvl k c v
| Coq_path_attempt_seq_graph_equation_2 (lvl, k, c, p) ->
  Obj.magic f0 __ lvl k c p
| Coq_path_attempt_seq_graph_equation_3 (lvl, k, c2, p) ->
  Obj.magic f1 __ lvl k c2 p

(** val path_attempt_seq_graph_correct :
    nat -> kind -> color -> 'a1 path_attempt -> 'a1 path_attempt_seq_graph **)

let path_attempt_seq_graph_correct lvl _ _ = function
| ZeroSix (k, c, v) -> Coq_path_attempt_seq_graph_equation_1 (lvl, k, c, v)
| Ok (k, c, p0) -> Coq_path_attempt_seq_graph_equation_2 (lvl, k, c, p0)
| Any (k, c, p0) -> Coq_path_attempt_seq_graph_equation_3 (lvl, k, c, p0)

(** val path_attempt_seq_elim :
    (__ -> nat -> kind -> color -> __ stored_triple vector -> 'a1) -> (__ ->
    nat -> kind -> color -> __ path -> 'a1) -> (__ -> nat -> kind -> color ->
    __ path -> 'a1) -> nat -> kind -> color -> 'a2 path_attempt -> 'a1 **)

let path_attempt_seq_elim f f0 f1 lvl k c p =
  match path_attempt_seq_graph_correct lvl k c p with
  | Coq_path_attempt_seq_graph_equation_1 (lvl0, k0, c0, v) ->
    Obj.magic f __ lvl0 k0 c0 v
  | Coq_path_attempt_seq_graph_equation_2 (lvl0, k0, c0, p0) ->
    Obj.magic f0 __ lvl0 k0 c0 p0
  | Coq_path_attempt_seq_graph_equation_3 (lvl0, k0, c2, p0) ->
    Obj.magic f1 __ lvl0 k0 c2 p0

(** val coq_FunctionalElimination_path_attempt_seq :
    (__ -> nat -> kind -> color -> __ stored_triple vector -> __) -> (__ ->
    nat -> kind -> color -> __ path -> __) -> (__ -> nat -> kind -> color ->
    __ path -> __) -> nat -> kind -> color -> __ path_attempt -> __ **)

let coq_FunctionalElimination_path_attempt_seq =
  path_attempt_seq_elim

(** val coq_FunctionalInduction_path_attempt_seq :
    (__ -> nat -> kind -> color -> __ path_attempt -> __ list)
    coq_FunctionalInduction **)

let coq_FunctionalInduction_path_attempt_seq =
  Obj.magic (fun _ -> path_attempt_seq_graph_correct)

(** val path_uncolored_seq : nat -> kind -> 'a1 path_uncolored -> 'a1 list **)

let path_uncolored_seq lvl k = function
| Six (s, s0, s1, s2, s3, s4) ->
  app (stored_triple_seq lvl s)
    (app (stored_triple_seq lvl s0)
      (app (stored_triple_seq lvl s1)
        (app (stored_triple_seq lvl s2)
          (app (stored_triple_seq lvl s3) (stored_triple_seq lvl s4)))))
| AnyColor (c, p0) -> path_seq lvl k c p0

type 'a path_uncolored_seq_graph =
| Coq_path_uncolored_seq_graph_equation_1 of nat * kind * 'a stored_triple
   * 'a stored_triple * 'a stored_triple * 'a stored_triple
   * 'a stored_triple * 'a stored_triple
| Coq_path_uncolored_seq_graph_equation_2 of nat * kind * color * 'a path

(** val path_uncolored_seq_graph_rect :
    (__ -> nat -> kind -> __ stored_triple -> __ stored_triple -> __
    stored_triple -> __ stored_triple -> __ stored_triple -> __ stored_triple
    -> 'a1) -> (__ -> nat -> kind -> color -> __ path -> 'a1) -> nat -> kind
    -> 'a2 path_uncolored -> 'a2 list -> 'a2 path_uncolored_seq_graph -> 'a1 **)

let path_uncolored_seq_graph_rect f f0 _ _ _ _ = function
| Coq_path_uncolored_seq_graph_equation_1 (lvl, k, x1, x2, x3, x4, x5, x6) ->
  Obj.magic f __ lvl k x1 x2 x3 x4 x5 x6
| Coq_path_uncolored_seq_graph_equation_2 (lvl, k, c, p) ->
  Obj.magic f0 __ lvl k c p

(** val path_uncolored_seq_graph_correct :
    nat -> kind -> 'a1 path_uncolored -> 'a1 path_uncolored_seq_graph **)

let path_uncolored_seq_graph_correct lvl k = function
| Six (s, s0, s1, s2, s3, s4) ->
  Coq_path_uncolored_seq_graph_equation_1 (lvl, k, s, s0, s1, s2, s3, s4)
| AnyColor (c, p0) -> Coq_path_uncolored_seq_graph_equation_2 (lvl, k, c, p0)

(** val path_uncolored_seq_elim :
    (__ -> nat -> kind -> __ stored_triple -> __ stored_triple -> __
    stored_triple -> __ stored_triple -> __ stored_triple -> __ stored_triple
    -> 'a1) -> (__ -> nat -> kind -> color -> __ path -> 'a1) -> nat -> kind
    -> 'a2 path_uncolored -> 'a1 **)

let path_uncolored_seq_elim f f0 lvl k p =
  match path_uncolored_seq_graph_correct lvl k p with
  | Coq_path_uncolored_seq_graph_equation_1 (lvl0, k0, x1, x2, x3, x4, x5, x6) ->
    Obj.magic f __ lvl0 k0 x1 x2 x3 x4 x5 x6
  | Coq_path_uncolored_seq_graph_equation_2 (lvl0, k0, c, p0) ->
    Obj.magic f0 __ lvl0 k0 c p0

(** val coq_FunctionalElimination_path_uncolored_seq :
    (__ -> nat -> kind -> __ stored_triple -> __ stored_triple -> __
    stored_triple -> __ stored_triple -> __ stored_triple -> __ stored_triple
    -> __) -> (__ -> nat -> kind -> color -> __ path -> __) -> nat -> kind ->
    __ path_uncolored -> __ **)

let coq_FunctionalElimination_path_uncolored_seq =
  path_uncolored_seq_elim

(** val coq_FunctionalInduction_path_uncolored_seq :
    (__ -> nat -> kind -> __ path_uncolored -> __ list)
    coq_FunctionalInduction **)

let coq_FunctionalInduction_path_uncolored_seq =
  Obj.magic (fun _ -> path_uncolored_seq_graph_correct)

(** val sdeque_seq : nat -> 'a1 sdeque -> 'a1 list **)

let sdeque_seq lvl = function
| Sd (c, c0) -> cdeque_seq lvl c c0

type 'a sdeque_seq_graph =
| Coq_sdeque_seq_graph_equation_1 of nat * color * 'a cdeque

(** val sdeque_seq_graph_rect :
    (__ -> nat -> color -> __ cdeque -> 'a1) -> nat -> 'a2 sdeque -> 'a2 list
    -> 'a2 sdeque_seq_graph -> 'a1 **)

let sdeque_seq_graph_rect f _ _ _ = function
| Coq_sdeque_seq_graph_equation_1 (lvl, c, cd) -> Obj.magic f __ lvl c cd

(** val sdeque_seq_graph_correct :
    nat -> 'a1 sdeque -> 'a1 sdeque_seq_graph **)

let sdeque_seq_graph_correct lvl = function
| Sd (c, c0) -> Coq_sdeque_seq_graph_equation_1 (lvl, c, c0)

(** val sdeque_seq_elim :
    (__ -> nat -> color -> __ cdeque -> 'a1) -> nat -> 'a2 sdeque -> 'a1 **)

let sdeque_seq_elim f lvl s =
  let Coq_sdeque_seq_graph_equation_1 (lvl0, c, cd) =
    sdeque_seq_graph_correct lvl s
  in
  Obj.magic f __ lvl0 c cd

(** val coq_FunctionalElimination_sdeque_seq :
    (__ -> nat -> color -> __ cdeque -> __) -> nat -> __ sdeque -> __ **)

let coq_FunctionalElimination_sdeque_seq =
  sdeque_seq_elim

(** val coq_FunctionalInduction_sdeque_seq :
    (__ -> nat -> __ sdeque -> __ list) coq_FunctionalInduction **)

let coq_FunctionalInduction_sdeque_seq =
  Obj.magic (fun _ -> sdeque_seq_graph_correct)

(** val unstored_front_seq : nat -> 'a1 unstored -> 'a1 list **)

let unstored_front_seq lvl = function
| Unstored (q, p, _) -> buffer_seq lvl (add (S (S (S O))) q) p

type 'a unstored_front_seq_graph =
| Coq_unstored_front_seq_graph_equation_1 of nat * nat * 'a prefix * 'a sdeque

(** val unstored_front_seq_graph_rect :
    (__ -> nat -> nat -> __ prefix -> __ sdeque -> 'a1) -> nat -> 'a2
    unstored -> 'a2 list -> 'a2 unstored_front_seq_graph -> 'a1 **)

let unstored_front_seq_graph_rect f _ _ _ = function
| Coq_unstored_front_seq_graph_equation_1 (lvl, q, p, s) ->
  Obj.magic f __ lvl q p s

(** val unstored_front_seq_graph_correct :
    nat -> 'a1 unstored -> 'a1 unstored_front_seq_graph **)

let unstored_front_seq_graph_correct lvl = function
| Unstored (q, p, s) -> Coq_unstored_front_seq_graph_equation_1 (lvl, q, p, s)

(** val unstored_front_seq_elim :
    (__ -> nat -> nat -> __ prefix -> __ sdeque -> 'a1) -> nat -> 'a2
    unstored -> 'a1 **)

let unstored_front_seq_elim f lvl u =
  let Coq_unstored_front_seq_graph_equation_1 (lvl0, q, p, s) =
    unstored_front_seq_graph_correct lvl u
  in
  Obj.magic f __ lvl0 q p s

(** val coq_FunctionalElimination_unstored_front_seq :
    (__ -> nat -> nat -> __ prefix -> __ sdeque -> __) -> nat -> __ unstored
    -> __ **)

let coq_FunctionalElimination_unstored_front_seq =
  unstored_front_seq_elim

(** val coq_FunctionalInduction_unstored_front_seq :
    (__ -> nat -> __ unstored -> __ list) coq_FunctionalInduction **)

let coq_FunctionalInduction_unstored_front_seq =
  Obj.magic (fun _ -> unstored_front_seq_graph_correct)

(** val unstored_rear_seq : nat -> 'a1 unstored -> 'a1 list **)

let unstored_rear_seq lvl = function
| Unstored (_, _, s) -> sdeque_seq (S lvl) s

type 'a unstored_rear_seq_graph =
| Coq_unstored_rear_seq_graph_equation_1 of nat * nat * 'a prefix * 'a sdeque

(** val unstored_rear_seq_graph_rect :
    (__ -> nat -> nat -> __ prefix -> __ sdeque -> 'a1) -> nat -> 'a2
    unstored -> 'a2 list -> 'a2 unstored_rear_seq_graph -> 'a1 **)

let unstored_rear_seq_graph_rect f _ _ _ = function
| Coq_unstored_rear_seq_graph_equation_1 (lvl, q, p, sd) ->
  Obj.magic f __ lvl q p sd

(** val unstored_rear_seq_graph_correct :
    nat -> 'a1 unstored -> 'a1 unstored_rear_seq_graph **)

let unstored_rear_seq_graph_correct lvl = function
| Unstored (q, p, s) -> Coq_unstored_rear_seq_graph_equation_1 (lvl, q, p, s)

(** val unstored_rear_seq_elim :
    (__ -> nat -> nat -> __ prefix -> __ sdeque -> 'a1) -> nat -> 'a2
    unstored -> 'a1 **)

let unstored_rear_seq_elim f lvl u =
  let Coq_unstored_rear_seq_graph_equation_1 (lvl0, q, p, sd) =
    unstored_rear_seq_graph_correct lvl u
  in
  Obj.magic f __ lvl0 q p sd

(** val coq_FunctionalElimination_unstored_rear_seq :
    (__ -> nat -> nat -> __ prefix -> __ sdeque -> __) -> nat -> __ unstored
    -> __ **)

let coq_FunctionalElimination_unstored_rear_seq =
  unstored_rear_seq_elim

(** val coq_FunctionalInduction_unstored_rear_seq :
    (__ -> nat -> __ unstored -> __ list) coq_FunctionalInduction **)

let coq_FunctionalInduction_unstored_rear_seq =
  Obj.magic (fun _ -> unstored_rear_seq_graph_correct)

(** val sandwich_seq : nat -> 'a1 sandwich -> 'a1 list **)

let sandwich_seq lvl = function
| Alone s0 -> stored_triple_seq lvl s0
| Sandwich (s0, s1, s2) ->
  app (stored_triple_seq lvl s0)
    (app (sdeque_seq lvl s1) (stored_triple_seq lvl s2))

type 'a sandwich_seq_graph =
| Coq_sandwich_seq_graph_equation_1 of nat * 'a stored_triple
| Coq_sandwich_seq_graph_equation_2 of nat * 'a stored_triple * 'a sdeque
   * 'a stored_triple

(** val sandwich_seq_graph_rect :
    (__ -> nat -> __ stored_triple -> 'a1) -> (__ -> nat -> __ stored_triple
    -> __ sdeque -> __ stored_triple -> 'a1) -> nat -> 'a2 sandwich -> 'a2
    list -> 'a2 sandwich_seq_graph -> 'a1 **)

let sandwich_seq_graph_rect f f0 _ _ _ = function
| Coq_sandwich_seq_graph_equation_1 (lvl, x) -> Obj.magic f __ lvl x
| Coq_sandwich_seq_graph_equation_2 (lvl, xl, sd, xr) ->
  Obj.magic f0 __ lvl xl sd xr

(** val sandwich_seq_graph_correct :
    nat -> 'a1 sandwich -> 'a1 sandwich_seq_graph **)

let sandwich_seq_graph_correct lvl = function
| Alone s0 -> Coq_sandwich_seq_graph_equation_1 (lvl, s0)
| Sandwich (s0, s1, s2) -> Coq_sandwich_seq_graph_equation_2 (lvl, s0, s1, s2)

(** val sandwich_seq_elim :
    (__ -> nat -> __ stored_triple -> 'a1) -> (__ -> nat -> __ stored_triple
    -> __ sdeque -> __ stored_triple -> 'a1) -> nat -> 'a2 sandwich -> 'a1 **)

let sandwich_seq_elim f f0 lvl s =
  match sandwich_seq_graph_correct lvl s with
  | Coq_sandwich_seq_graph_equation_1 (lvl0, x) -> Obj.magic f __ lvl0 x
  | Coq_sandwich_seq_graph_equation_2 (lvl0, xl, sd, xr) ->
    Obj.magic f0 __ lvl0 xl sd xr

(** val coq_FunctionalElimination_sandwich_seq :
    (__ -> nat -> __ stored_triple -> __) -> (__ -> nat -> __ stored_triple
    -> __ sdeque -> __ stored_triple -> __) -> nat -> __ sandwich -> __ **)

let coq_FunctionalElimination_sandwich_seq =
  sandwich_seq_elim

(** val coq_FunctionalInduction_sandwich_seq :
    (__ -> nat -> __ sandwich -> __ list) coq_FunctionalInduction **)

let coq_FunctionalInduction_sandwich_seq =
  Obj.magic (fun _ -> sandwich_seq_graph_correct)

(** val unstored_sandwich_seq : nat -> 'a1 unstored_sandwich -> 'a1 list **)

let unstored_sandwich_seq lvl = function
| Unstored_alone (q, p) -> buffer_seq lvl (add (S (S (S O))) q) p
| Unstored_sandwich (qp, qs, p, s, s0) ->
  app (buffer_seq lvl (add (S (S (S O))) qp) p)
    (app (sdeque_seq (S lvl) s) (buffer_seq lvl (add (S (S (S O))) qs) s0))

type 'a unstored_sandwich_seq_graph =
| Coq_unstored_sandwich_seq_graph_equation_1 of nat * nat * 'a prefix
| Coq_unstored_sandwich_seq_graph_equation_2 of nat * nat * nat * 'a prefix
   * 'a sdeque * 'a suffix

(** val unstored_sandwich_seq_graph_rect :
    (__ -> nat -> nat -> __ prefix -> 'a1) -> (__ -> nat -> nat -> nat -> __
    prefix -> __ sdeque -> __ suffix -> 'a1) -> nat -> 'a2 unstored_sandwich
    -> 'a2 list -> 'a2 unstored_sandwich_seq_graph -> 'a1 **)

let unstored_sandwich_seq_graph_rect f f0 _ _ _ = function
| Coq_unstored_sandwich_seq_graph_equation_1 (lvl, q, p) ->
  Obj.magic f __ lvl q p
| Coq_unstored_sandwich_seq_graph_equation_2 (lvl, qp, qs, p, sd, s) ->
  Obj.magic f0 __ lvl qp qs p sd s

(** val unstored_sandwich_seq_graph_correct :
    nat -> 'a1 unstored_sandwich -> 'a1 unstored_sandwich_seq_graph **)

let unstored_sandwich_seq_graph_correct lvl = function
| Unstored_alone (q, p) ->
  Coq_unstored_sandwich_seq_graph_equation_1 (lvl, q, p)
| Unstored_sandwich (qp, qs, p, s, s0) ->
  Coq_unstored_sandwich_seq_graph_equation_2 (lvl, qp, qs, p, s, s0)

(** val unstored_sandwich_seq_elim :
    (__ -> nat -> nat -> __ prefix -> 'a1) -> (__ -> nat -> nat -> nat -> __
    prefix -> __ sdeque -> __ suffix -> 'a1) -> nat -> 'a2 unstored_sandwich
    -> 'a1 **)

let unstored_sandwich_seq_elim f f0 lvl u =
  match unstored_sandwich_seq_graph_correct lvl u with
  | Coq_unstored_sandwich_seq_graph_equation_1 (lvl0, q, p) ->
    Obj.magic f __ lvl0 q p
  | Coq_unstored_sandwich_seq_graph_equation_2 (lvl0, qp, qs, p, sd, s) ->
    Obj.magic f0 __ lvl0 qp qs p sd s

(** val coq_FunctionalElimination_unstored_sandwich_seq :
    (__ -> nat -> nat -> __ prefix -> __) -> (__ -> nat -> nat -> nat -> __
    prefix -> __ sdeque -> __ suffix -> __) -> nat -> __ unstored_sandwich ->
    __ **)

let coq_FunctionalElimination_unstored_sandwich_seq =
  unstored_sandwich_seq_elim

(** val coq_FunctionalInduction_unstored_sandwich_seq :
    (__ -> nat -> __ unstored_sandwich -> __ list) coq_FunctionalInduction **)

let coq_FunctionalInduction_unstored_sandwich_seq =
  Obj.magic (fun _ -> unstored_sandwich_seq_graph_correct)

(** val deque_seq : 'a1 deque -> 'a1 list **)

let deque_seq d =
  cdeque_seq O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) d

type 'a deque_seq_graph =
  'a cdeque
  (* singleton inductive, whose constructor was deque_seq_graph_equation_1 *)

(** val deque_seq_graph_rect :
    (__ -> __ cdeque -> 'a1) -> 'a2 deque -> 'a2 list -> 'a2 deque_seq_graph
    -> 'a1 **)

let deque_seq_graph_rect f _ _ d0 =
  Obj.magic f __ d0

(** val deque_seq_graph_correct : 'a1 deque -> 'a1 deque_seq_graph **)

let deque_seq_graph_correct d =
  d

(** val deque_seq_elim : (__ -> __ cdeque -> 'a1) -> 'a2 deque -> 'a1 **)

let deque_seq_elim f d =
  Obj.magic f __ (deque_seq_graph_correct d)

(** val coq_FunctionalElimination_deque_seq :
    (__ -> __ cdeque -> __) -> __ deque -> __ **)

let coq_FunctionalElimination_deque_seq =
  deque_seq_elim

(** val coq_FunctionalInduction_deque_seq :
    (__ -> __ deque -> __ list) coq_FunctionalInduction **)

let coq_FunctionalInduction_deque_seq =
  Obj.magic (fun _ -> deque_seq_graph_correct)
