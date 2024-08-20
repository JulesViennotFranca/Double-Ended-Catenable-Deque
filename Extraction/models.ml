open Datatypes
open List
open Nat
open Buffer
open Types

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val stored_triple_seq : nat -> 'a1 stored_triple -> 'a1 list **)

let rec stored_triple_seq _ strd =
  let buffer_seq0 = fun lvl q b -> map_buffer stored_triple_seq lvl q b in
  let storage_left_seq0 = fun lvl _ _ _ st ->
    match st with
    | Only_end (q, p) -> buffer_seq0 lvl (S q) p
    | Left_end (qp, p, _) ->
      buffer_seq0 lvl (add (S (S (S (S (S Datatypes.O))))) qp) p
    | Right_end (_, p, _) -> buffer_seq0 lvl (S (S Datatypes.O)) p
    | Only_st (qp, _, _, _, p, _) ->
      buffer_seq0 lvl (add (S (S (S (S (S Datatypes.O))))) qp) p
    | Left_st (qp, _, _, _, p, _) ->
      buffer_seq0 lvl (add (S (S (S (S (S Datatypes.O))))) qp) p
    | Right_st (_, _, _, _, p, _) -> buffer_seq0 lvl (S (S Datatypes.O)) p
  in
  let storage_right_seq0 = fun lvl _ _ _ st ->
    match st with
    | Only_end (_, _) -> Coq_nil
    | Left_end (_, _, s) -> buffer_seq0 lvl (S (S Datatypes.O)) s
    | Right_end (qs, _, s) ->
      buffer_seq0 lvl (add (S (S (S (S (S Datatypes.O))))) qs) s
    | Only_st (_, qs, _, _, _, s) ->
      buffer_seq0 lvl (add (S (S (S (S (S Datatypes.O))))) qs) s
    | Left_st (_, _, _, _, _, s) -> buffer_seq0 lvl (S (S Datatypes.O)) s
    | Right_st (_, qs, _, _, _, s) ->
      buffer_seq0 lvl (add (S (S (S (S (S Datatypes.O))))) qs) s
  in
  let chain_seq0 =
    let rec chain_seq0 _ _ _ _ _ _ c =
      let body_left_seq0 = fun hlvl ->
        let rec body_left_seq0 _ _ _ _ = function
        | Hole (_, _) -> Coq_nil
        | Only_yellow (hlvl0, tlvl0, hk0, tk0, hd, bd0) ->
          app
            (storage_left_seq0 hlvl0 hk0 Not_end (Mix (NoGreen, SomeYellow,
              NoOrange, NoRed)) hd)
            (body_left_seq0 (S hlvl0) tlvl0 Only tk0 bd0)
        | Only_orange (hlvl0, tlvl0, hk0, tk0, hd, bd0) ->
          app
            (storage_left_seq0 hlvl0 hk0 Not_end (Mix (NoGreen, NoYellow,
              SomeOrange, NoRed)) hd)
            (body_left_seq0 (S hlvl0) tlvl0 Only tk0 bd0)
        | Pair_yellow (hlvl0, tlvl0, hk0, tk0, _, hd, bd0, _) ->
          app
            (storage_left_seq0 hlvl0 hk0 Not_end (Mix (NoGreen, SomeYellow,
              NoOrange, NoRed)) hd)
            (body_left_seq0 (S hlvl0) tlvl0 Left tk0 bd0)
        | Pair_orange (hlvl0, tlvl0, hk0, tk0, hd, cl, bd0) ->
          app
            (storage_left_seq0 hlvl0 hk0 Not_end (Mix (NoGreen, NoYellow,
              SomeOrange, NoRed)) hd)
            (app
              (chain_seq0 (S hlvl0) Only Left Not_end (Mix (SomeGreen,
                NoYellow, NoOrange, NoRed)) (Mix (SomeGreen, NoYellow,
                NoOrange, NoRed)) cl)
              (body_left_seq0 (S hlvl0) tlvl0 Right tk0 bd0))
        in body_left_seq0 hlvl
      in
      let body_right_seq0 = fun hlvl ->
        let rec body_right_seq0 _ _ _ _ = function
        | Hole (_, _) -> Coq_nil
        | Only_yellow (hlvl0, tlvl0, hk0, tk0, hd, bd0) ->
          app (body_right_seq0 (S hlvl0) tlvl0 Only tk0 bd0)
            (storage_right_seq0 hlvl0 hk0 Not_end (Mix (NoGreen, SomeYellow,
              NoOrange, NoRed)) hd)
        | Only_orange (hlvl0, tlvl0, hk0, tk0, hd, bd0) ->
          app (body_right_seq0 (S hlvl0) tlvl0 Only tk0 bd0)
            (storage_right_seq0 hlvl0 hk0 Not_end (Mix (NoGreen, NoYellow,
              SomeOrange, NoRed)) hd)
        | Pair_yellow (hlvl0, tlvl0, hk0, tk0, c0, hd, bd0, cr) ->
          app (body_right_seq0 (S hlvl0) tlvl0 Left tk0 bd0)
            (app (chain_seq0 (S hlvl0) Only Right Not_end c0 c0 cr)
              (storage_right_seq0 hlvl0 hk0 Not_end (Mix (NoGreen,
                SomeYellow, NoOrange, NoRed)) hd))
        | Pair_orange (hlvl0, tlvl0, hk0, tk0, hd, _, bd0) ->
          app (body_right_seq0 (S hlvl0) tlvl0 Right tk0 bd0)
            (storage_right_seq0 hlvl0 hk0 Not_end (Mix (NoGreen, NoYellow,
              SomeOrange, NoRed)) hd)
        in body_right_seq0 hlvl
      in
      let packet_left_seq0 = fun _ _ _ _ _ pkt ->
        let Packet (hlvl0, tlvl0, hk, tk, e0, g, r, bd, tl) = pkt in
        app (body_left_seq0 hlvl0 tlvl0 hk tk bd)
          (storage_left_seq0 tlvl0 tk e0 (Mix (g, NoYellow, NoOrange, r)) tl)
      in
      let packet_right_seq0 = fun _ _ _ _ _ pkt ->
        let Packet (hlvl0, tlvl0, hk, tk, e0, g, r, bd, tl) = pkt in
        app
          (storage_right_seq0 tlvl0 tk e0 (Mix (g, NoYellow, NoOrange, r)) tl)
          (body_right_seq0 hlvl0 tlvl0 hk tk bd)
      in
      (match c with
       | Empty _ -> Coq_nil
       | Only_chain (hlvl, tlvl, k0, pk0, e0, c0, cl0, cr0, _, pkt, rest) ->
         app (packet_left_seq0 hlvl tlvl k0 e0 c0 pkt)
           (app (chain_seq0 (S tlvl) pk0 Only e0 cl0 cr0 rest)
             (packet_right_seq0 hlvl tlvl k0 e0 c0 pkt))
       | Pair_chain (lvl0, cl0, cr0, cl, cr) ->
         app (chain_seq0 lvl0 Only Left Not_end cl0 cl0 cl)
           (chain_seq0 lvl0 Only Right Not_end cr0 cr0 cr))
    in chain_seq0
  in
  (match strd with
   | Ground a -> Coq_cons (a, Coq_nil)
   | Small (lvl0, q, s) -> buffer_seq0 lvl0 (add (S (S (S Datatypes.O))) q) s
   | Big (lvl0, qp, qs, pk, e, cl, cr, p, child, s) ->
     app (buffer_seq0 lvl0 (add (S (S (S Datatypes.O))) qp) p)
       (app (chain_seq0 (S lvl0) pk Only e cl cr child)
         (buffer_seq0 lvl0 (add (S (S (S Datatypes.O))) qs) s)))

(** val strd_buffer_seq : nat -> nat -> 'a1 stored_triple t -> 'a1 list **)

let strd_buffer_seq lvl q b =
  map_buffer stored_triple_seq lvl q b

(** val strd_storage_left_seq :
    nat -> kind -> ending -> color -> 'a1 storage -> 'a1 list **)

let strd_storage_left_seq lvl _ _ _ = function
| Only_end (q, p) -> strd_buffer_seq lvl (S q) p
| Left_end (qp, p, _) ->
  strd_buffer_seq lvl (add (S (S (S (S (S Datatypes.O))))) qp) p
| Right_end (_, p, _) -> strd_buffer_seq lvl (S (S Datatypes.O)) p
| Only_st (qp, _, _, _, p, _) ->
  strd_buffer_seq lvl (add (S (S (S (S (S Datatypes.O))))) qp) p
| Left_st (qp, _, _, _, p, _) ->
  strd_buffer_seq lvl (add (S (S (S (S (S Datatypes.O))))) qp) p
| Right_st (_, _, _, _, p, _) -> strd_buffer_seq lvl (S (S Datatypes.O)) p

(** val strd_storage_right_seq :
    nat -> kind -> ending -> color -> 'a1 storage -> 'a1 list **)

let strd_storage_right_seq lvl _ _ _ = function
| Only_end (_, _) -> Coq_nil
| Left_end (_, _, s) -> strd_buffer_seq lvl (S (S Datatypes.O)) s
| Right_end (qs, _, s) ->
  strd_buffer_seq lvl (add (S (S (S (S (S Datatypes.O))))) qs) s
| Only_st (_, qs, _, _, _, s) ->
  strd_buffer_seq lvl (add (S (S (S (S (S Datatypes.O))))) qs) s
| Left_st (_, _, _, _, _, s) -> strd_buffer_seq lvl (S (S Datatypes.O)) s
| Right_st (_, qs, _, _, _, s) ->
  strd_buffer_seq lvl (add (S (S (S (S (S Datatypes.O))))) qs) s

(** val chain_seq :
    nat -> kind -> kind -> ending -> color -> color -> 'a1 chain -> 'a1 list **)

let rec chain_seq _ _ _ _ _ _ c =
  let body_left_seq0 =
    let rec body_left_seq0 _ _ _ _ = function
    | Hole (_, _) -> Coq_nil
    | Only_yellow (hlvl0, tlvl0, hk0, tk0, hd, bd0) ->
      app
        (strd_storage_left_seq hlvl0 hk0 Not_end (Mix (NoGreen, SomeYellow,
          NoOrange, NoRed)) hd) (body_left_seq0 (S hlvl0) tlvl0 Only tk0 bd0)
    | Only_orange (hlvl0, tlvl0, hk0, tk0, hd, bd0) ->
      app
        (strd_storage_left_seq hlvl0 hk0 Not_end (Mix (NoGreen, NoYellow,
          SomeOrange, NoRed)) hd)
        (body_left_seq0 (S hlvl0) tlvl0 Only tk0 bd0)
    | Pair_yellow (hlvl0, tlvl0, hk0, tk0, _, hd, bd0, _) ->
      app
        (strd_storage_left_seq hlvl0 hk0 Not_end (Mix (NoGreen, SomeYellow,
          NoOrange, NoRed)) hd) (body_left_seq0 (S hlvl0) tlvl0 Left tk0 bd0)
    | Pair_orange (hlvl0, tlvl0, hk0, tk0, hd, cl, bd0) ->
      app
        (strd_storage_left_seq hlvl0 hk0 Not_end (Mix (NoGreen, NoYellow,
          SomeOrange, NoRed)) hd)
        (app
          (chain_seq (S hlvl0) Only Left Not_end (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) cl)
          (body_left_seq0 (S hlvl0) tlvl0 Right tk0 bd0))
    in body_left_seq0
  in
  let body_right_seq0 =
    let rec body_right_seq0 _ _ _ _ = function
    | Hole (_, _) -> Coq_nil
    | Only_yellow (hlvl0, tlvl0, hk0, tk0, hd, bd0) ->
      app (body_right_seq0 (S hlvl0) tlvl0 Only tk0 bd0)
        (strd_storage_right_seq hlvl0 hk0 Not_end (Mix (NoGreen, SomeYellow,
          NoOrange, NoRed)) hd)
    | Only_orange (hlvl0, tlvl0, hk0, tk0, hd, bd0) ->
      app (body_right_seq0 (S hlvl0) tlvl0 Only tk0 bd0)
        (strd_storage_right_seq hlvl0 hk0 Not_end (Mix (NoGreen, NoYellow,
          SomeOrange, NoRed)) hd)
    | Pair_yellow (hlvl0, tlvl0, hk0, tk0, c0, hd, bd0, cr) ->
      app (body_right_seq0 (S hlvl0) tlvl0 Left tk0 bd0)
        (app (chain_seq (S hlvl0) Only Right Not_end c0 c0 cr)
          (strd_storage_right_seq hlvl0 hk0 Not_end (Mix (NoGreen,
            SomeYellow, NoOrange, NoRed)) hd))
    | Pair_orange (hlvl0, tlvl0, hk0, tk0, hd, _, bd0) ->
      app (body_right_seq0 (S hlvl0) tlvl0 Right tk0 bd0)
        (strd_storage_right_seq hlvl0 hk0 Not_end (Mix (NoGreen, NoYellow,
          SomeOrange, NoRed)) hd)
    in body_right_seq0
  in
  let packet_left_seq0 = fun _ _ _ _ _ pkt ->
    let Packet (hlvl0, tlvl0, hk, tk, e0, g, r, bd, tl) = pkt in
    app (body_left_seq0 hlvl0 tlvl0 hk tk bd)
      (strd_storage_left_seq tlvl0 tk e0 (Mix (g, NoYellow, NoOrange, r)) tl)
  in
  let packet_right_seq0 = fun _ _ _ _ _ pkt ->
    let Packet (hlvl0, tlvl0, hk, tk, e0, g, r, bd, tl) = pkt in
    app
      (strd_storage_right_seq tlvl0 tk e0 (Mix (g, NoYellow, NoOrange, r)) tl)
      (body_right_seq0 hlvl0 tlvl0 hk tk bd)
  in
  (match c with
   | Empty _ -> Coq_nil
   | Only_chain (hlvl, tlvl, k0, pk0, e0, c0, cl0, cr0, _, pkt, rest) ->
     app (packet_left_seq0 hlvl tlvl k0 e0 c0 pkt)
       (app (chain_seq (S tlvl) pk0 Only e0 cl0 cr0 rest)
         (packet_right_seq0 hlvl tlvl k0 e0 c0 pkt))
   | Pair_chain (lvl0, cl0, cr0, cl, cr) ->
     app (chain_seq lvl0 Only Left Not_end cl0 cl0 cl)
       (chain_seq lvl0 Only Right Not_end cr0 cr0 cr))

(** val buffer_seq : nat -> nat -> 'a1 stored_triple t -> 'a1 list **)

let buffer_seq lvl q b =
  concat (map (stored_triple_seq lvl) (seq q b))

type 'a buffer_seq_graph =
| Coq_buffer_seq_graph_equation_1 of nat * nat * 'a stored_triple t

(** val buffer_seq_graph_rect :
    (__ -> nat -> nat -> __ stored_triple t -> 'a1) -> nat -> nat -> 'a2
    stored_triple t -> 'a2 list -> 'a2 buffer_seq_graph -> 'a1 **)

let buffer_seq_graph_rect f _ _ _ _ = function
| Coq_buffer_seq_graph_equation_1 (lvl, q, b0) -> Obj.magic f __ lvl q b0

(** val buffer_seq_graph_correct :
    nat -> nat -> 'a1 stored_triple t -> 'a1 buffer_seq_graph **)

let buffer_seq_graph_correct lvl q t0 =
  Coq_buffer_seq_graph_equation_1 (lvl, q, t0)

(** val buffer_seq_elim :
    (__ -> nat -> nat -> __ stored_triple t -> 'a1) -> nat -> nat -> 'a2
    stored_triple t -> 'a1 **)

let buffer_seq_elim f lvl q t0 =
  let Coq_buffer_seq_graph_equation_1 (lvl0, q0, b) =
    buffer_seq_graph_correct lvl q t0
  in
  Obj.magic f __ lvl0 q0 b

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

(** val prefix_seq : nat -> nat -> 'a1 prefix -> 'a1 list **)

let prefix_seq =
  buffer_seq

(** val suffix_seq : nat -> nat -> 'a1 suffix -> 'a1 list **)

let suffix_seq =
  buffer_seq

(** val green_buffer_seq : nat -> 'a1 green_buffer -> 'a1 list **)

let green_buffer_seq lvl = function
| Gbuf (q, t0) ->
  buffer_seq lvl (add (S (S (S (S (S (S (S (S Datatypes.O)))))))) q) t0

type 'a green_buffer_seq_graph =
| Coq_green_buffer_seq_graph_equation_1 of nat * nat * 'a stored_triple t

(** val green_buffer_seq_graph_rect :
    (__ -> nat -> nat -> __ stored_triple t -> 'a1) -> nat -> 'a2
    green_buffer -> 'a2 list -> 'a2 green_buffer_seq_graph -> 'a1 **)

let green_buffer_seq_graph_rect f _ _ _ = function
| Coq_green_buffer_seq_graph_equation_1 (lvl, q, b) -> Obj.magic f __ lvl q b

(** val green_buffer_seq_graph_correct :
    nat -> 'a1 green_buffer -> 'a1 green_buffer_seq_graph **)

let green_buffer_seq_graph_correct lvl = function
| Gbuf (q, t0) -> Coq_green_buffer_seq_graph_equation_1 (lvl, q, t0)

(** val green_buffer_seq_elim :
    (__ -> nat -> nat -> __ stored_triple t -> 'a1) -> nat -> 'a2
    green_buffer -> 'a1 **)

let green_buffer_seq_elim f lvl g =
  let Coq_green_buffer_seq_graph_equation_1 (lvl0, q, b) =
    green_buffer_seq_graph_correct lvl g
  in
  Obj.magic f __ lvl0 q b

(** val coq_FunctionalElimination_green_buffer_seq :
    (__ -> nat -> nat -> __ stored_triple t -> __) -> nat -> __ green_buffer
    -> __ **)

let coq_FunctionalElimination_green_buffer_seq =
  green_buffer_seq_elim

(** val coq_FunctionalInduction_green_buffer_seq :
    (__ -> nat -> __ green_buffer -> __ list) coq_FunctionalInduction **)

let coq_FunctionalInduction_green_buffer_seq =
  Obj.magic (fun _ -> green_buffer_seq_graph_correct)

(** val stored_buffer_seq : nat -> 'a1 stored_buffer -> 'a1 list **)

let stored_buffer_seq lvl = function
| Sbuf (q, t0) -> buffer_seq lvl (add (S (S (S Datatypes.O))) q) t0

type 'a stored_buffer_seq_graph =
| Coq_stored_buffer_seq_graph_equation_1 of nat * nat * 'a stored_triple t

(** val stored_buffer_seq_graph_rect :
    (__ -> nat -> nat -> __ stored_triple t -> 'a1) -> nat -> 'a2
    stored_buffer -> 'a2 list -> 'a2 stored_buffer_seq_graph -> 'a1 **)

let stored_buffer_seq_graph_rect f _ _ _ = function
| Coq_stored_buffer_seq_graph_equation_1 (lvl, q, b) -> Obj.magic f __ lvl q b

(** val stored_buffer_seq_graph_correct :
    nat -> 'a1 stored_buffer -> 'a1 stored_buffer_seq_graph **)

let stored_buffer_seq_graph_correct lvl = function
| Sbuf (q, t0) -> Coq_stored_buffer_seq_graph_equation_1 (lvl, q, t0)

(** val stored_buffer_seq_elim :
    (__ -> nat -> nat -> __ stored_triple t -> 'a1) -> nat -> 'a2
    stored_buffer -> 'a1 **)

let stored_buffer_seq_elim f lvl s =
  let Coq_stored_buffer_seq_graph_equation_1 (lvl0, q, b) =
    stored_buffer_seq_graph_correct lvl s
  in
  Obj.magic f __ lvl0 q b

(** val coq_FunctionalElimination_stored_buffer_seq :
    (__ -> nat -> nat -> __ stored_triple t -> __) -> nat -> __ stored_buffer
    -> __ **)

let coq_FunctionalElimination_stored_buffer_seq =
  stored_buffer_seq_elim

(** val coq_FunctionalInduction_stored_buffer_seq :
    (__ -> nat -> __ stored_buffer -> __ list) coq_FunctionalInduction **)

let coq_FunctionalInduction_stored_buffer_seq =
  Obj.magic (fun _ -> stored_buffer_seq_graph_correct)

(** val storage_left_seq :
    nat -> kind -> ending -> color -> 'a1 storage -> 'a1 list **)

let storage_left_seq lvl _ _ _ = function
| Only_end (q, p) -> prefix_seq lvl (S q) p
| Left_end (qp, p, _) ->
  prefix_seq lvl (add (S (S (S (S (S Datatypes.O))))) qp) p
| Right_end (_, p, _) -> prefix_seq lvl (S (S Datatypes.O)) p
| Only_st (qp, _, _, _, p, _) ->
  prefix_seq lvl (add (S (S (S (S (S Datatypes.O))))) qp) p
| Left_st (qp, _, _, _, p, _) ->
  prefix_seq lvl (add (S (S (S (S (S Datatypes.O))))) qp) p
| Right_st (_, _, _, _, p, _) -> prefix_seq lvl (S (S Datatypes.O)) p

type 'a storage_left_seq_graph =
| Coq_storage_left_seq_graph_equation_1 of nat * nat
   * 'a stored_triple prefix'
| Coq_storage_left_seq_graph_equation_2 of nat * nat
   * 'a stored_triple prefix' * 'a stored_triple suffix'
| Coq_storage_left_seq_graph_equation_3 of nat * nat
   * 'a stored_triple prefix' * 'a stored_triple suffix'
| Coq_storage_left_seq_graph_equation_4 of nat * color * nat * nat *
   coloring * 'a stored_triple prefix' * 'a stored_triple suffix'
| Coq_storage_left_seq_graph_equation_5 of nat * color * nat * nat *
   coloring * 'a stored_triple prefix' * 'a stored_triple suffix'
| Coq_storage_left_seq_graph_equation_6 of nat * color * nat * nat *
   coloring * 'a stored_triple prefix' * 'a stored_triple suffix'

(** val storage_left_seq_graph_rect :
    (__ -> nat -> nat -> __ stored_triple prefix' -> 'a1) -> (__ -> nat ->
    nat -> __ stored_triple prefix' -> __ stored_triple suffix' -> 'a1) ->
    (__ -> nat -> nat -> __ stored_triple prefix' -> __ stored_triple suffix'
    -> 'a1) -> (__ -> nat -> color -> nat -> nat -> coloring -> __
    stored_triple prefix' -> __ stored_triple suffix' -> 'a1) -> (__ -> nat
    -> color -> nat -> nat -> coloring -> __ stored_triple prefix' -> __
    stored_triple suffix' -> 'a1) -> (__ -> nat -> color -> nat -> nat ->
    coloring -> __ stored_triple prefix' -> __ stored_triple suffix' -> 'a1)
    -> nat -> kind -> ending -> color -> 'a2 storage -> 'a2 list -> 'a2
    storage_left_seq_graph -> 'a1 **)

let storage_left_seq_graph_rect f f0 f1 f2 f3 f4 _ _ _ _ _ _ = function
| Coq_storage_left_seq_graph_equation_1 (lvl, q, p) -> Obj.magic f __ lvl q p
| Coq_storage_left_seq_graph_equation_2 (lvl, qp, p, s) ->
  Obj.magic f0 __ lvl qp p s
| Coq_storage_left_seq_graph_equation_3 (lvl, qs, p, s1) ->
  Obj.magic f1 __ lvl qs p s1
| Coq_storage_left_seq_graph_equation_4 (lvl, c, qp0, qs0, c0, p, s1) ->
  Obj.magic f2 __ lvl c qp0 qs0 c0 p s1
| Coq_storage_left_seq_graph_equation_5 (lvl, c, qp1, qs1, c0, p, s2) ->
  Obj.magic f3 __ lvl c qp1 qs1 c0 p s2
| Coq_storage_left_seq_graph_equation_6 (lvl, c, qp2, qs2, c1, p, s3) ->
  Obj.magic f4 __ lvl c qp2 qs2 c1 p s3

(** val storage_left_seq_graph_correct :
    nat -> kind -> ending -> color -> 'a1 storage -> 'a1
    storage_left_seq_graph **)

let storage_left_seq_graph_correct lvl _ _ _ = function
| Only_end (q, p) -> Coq_storage_left_seq_graph_equation_1 (lvl, q, p)
| Left_end (qp, p, s0) ->
  Coq_storage_left_seq_graph_equation_2 (lvl, qp, p, s0)
| Right_end (qs, p, s0) ->
  Coq_storage_left_seq_graph_equation_3 (lvl, qs, p, s0)
| Only_st (qp, qs, c, c0, p, s0) ->
  Coq_storage_left_seq_graph_equation_4 (lvl, c, qp, qs, c0, p, s0)
| Left_st (qp, qs, c, c0, p, s0) ->
  Coq_storage_left_seq_graph_equation_5 (lvl, c, qp, qs, c0, p, s0)
| Right_st (qp, qs, c, c0, p, s0) ->
  Coq_storage_left_seq_graph_equation_6 (lvl, c, qp, qs, c0, p, s0)

(** val storage_left_seq_elim :
    (__ -> nat -> nat -> __ stored_triple prefix' -> 'a1) -> (__ -> nat ->
    nat -> __ stored_triple prefix' -> __ stored_triple suffix' -> 'a1) ->
    (__ -> nat -> nat -> __ stored_triple prefix' -> __ stored_triple suffix'
    -> 'a1) -> (__ -> nat -> color -> nat -> nat -> coloring -> __
    stored_triple prefix' -> __ stored_triple suffix' -> 'a1) -> (__ -> nat
    -> color -> nat -> nat -> coloring -> __ stored_triple prefix' -> __
    stored_triple suffix' -> 'a1) -> (__ -> nat -> color -> nat -> nat ->
    coloring -> __ stored_triple prefix' -> __ stored_triple suffix' -> 'a1)
    -> nat -> kind -> ending -> color -> 'a2 storage -> 'a1 **)

let storage_left_seq_elim f f0 f1 f2 f3 f4 lvl k e c s =
  match storage_left_seq_graph_correct lvl k e c s with
  | Coq_storage_left_seq_graph_equation_1 (lvl0, q, p) ->
    Obj.magic f __ lvl0 q p
  | Coq_storage_left_seq_graph_equation_2 (lvl0, qp, p, s0) ->
    Obj.magic f0 __ lvl0 qp p s0
  | Coq_storage_left_seq_graph_equation_3 (lvl0, qs, p, s0) ->
    Obj.magic f1 __ lvl0 qs p s0
  | Coq_storage_left_seq_graph_equation_4 (lvl0, c0, qp0, qs0, c1, p, s1) ->
    Obj.magic f2 __ lvl0 c0 qp0 qs0 c1 p s1
  | Coq_storage_left_seq_graph_equation_5 (lvl0, c0, qp1, qs1, c1, p, s2) ->
    Obj.magic f3 __ lvl0 c0 qp1 qs1 c1 p s2
  | Coq_storage_left_seq_graph_equation_6 (lvl0, c0, qp2, qs2, c1, p, s3) ->
    Obj.magic f4 __ lvl0 c0 qp2 qs2 c1 p s3

(** val coq_FunctionalElimination_storage_left_seq :
    (__ -> nat -> nat -> __ stored_triple prefix' -> __) -> (__ -> nat -> nat
    -> __ stored_triple prefix' -> __ stored_triple suffix' -> __) -> (__ ->
    nat -> nat -> __ stored_triple prefix' -> __ stored_triple suffix' -> __)
    -> (__ -> nat -> color -> nat -> nat -> coloring -> __ stored_triple
    prefix' -> __ stored_triple suffix' -> __) -> (__ -> nat -> color -> nat
    -> nat -> coloring -> __ stored_triple prefix' -> __ stored_triple
    suffix' -> __) -> (__ -> nat -> color -> nat -> nat -> coloring -> __
    stored_triple prefix' -> __ stored_triple suffix' -> __) -> nat -> kind
    -> ending -> color -> __ storage -> __ **)

let coq_FunctionalElimination_storage_left_seq =
  storage_left_seq_elim

(** val coq_FunctionalInduction_storage_left_seq :
    (__ -> nat -> kind -> ending -> color -> __ storage -> __ list)
    coq_FunctionalInduction **)

let coq_FunctionalInduction_storage_left_seq =
  Obj.magic (fun _ -> storage_left_seq_graph_correct)

(** val storage_right_seq :
    nat -> kind -> ending -> color -> 'a1 storage -> 'a1 list **)

let storage_right_seq lvl _ _ _ = function
| Only_end (_, _) -> Coq_nil
| Left_end (_, _, s0) -> suffix_seq lvl (S (S Datatypes.O)) s0
| Right_end (qs, _, s0) ->
  suffix_seq lvl (add (S (S (S (S (S Datatypes.O))))) qs) s0
| Only_st (_, qs, _, _, _, s0) ->
  suffix_seq lvl (add (S (S (S (S (S Datatypes.O))))) qs) s0
| Left_st (_, _, _, _, _, s0) -> suffix_seq lvl (S (S Datatypes.O)) s0
| Right_st (_, qs, _, _, _, s0) ->
  suffix_seq lvl (add (S (S (S (S (S Datatypes.O))))) qs) s0

type 'a storage_right_seq_graph =
| Coq_storage_right_seq_graph_equation_1 of nat * nat
   * 'a stored_triple prefix'
| Coq_storage_right_seq_graph_equation_2 of nat * nat
   * 'a stored_triple prefix' * 'a stored_triple suffix'
| Coq_storage_right_seq_graph_equation_3 of nat * nat
   * 'a stored_triple prefix' * 'a stored_triple suffix'
| Coq_storage_right_seq_graph_equation_4 of nat * color * nat * nat
   * coloring * 'a stored_triple prefix' * 'a stored_triple suffix'
| Coq_storage_right_seq_graph_equation_5 of nat * color * nat * nat
   * coloring * 'a stored_triple prefix' * 'a stored_triple suffix'
| Coq_storage_right_seq_graph_equation_6 of nat * color * nat * nat
   * coloring * 'a stored_triple prefix' * 'a stored_triple suffix'

(** val storage_right_seq_graph_rect :
    (__ -> nat -> nat -> __ stored_triple prefix' -> 'a1) -> (__ -> nat ->
    nat -> __ stored_triple prefix' -> __ stored_triple suffix' -> 'a1) ->
    (__ -> nat -> nat -> __ stored_triple prefix' -> __ stored_triple suffix'
    -> 'a1) -> (__ -> nat -> color -> nat -> nat -> coloring -> __
    stored_triple prefix' -> __ stored_triple suffix' -> 'a1) -> (__ -> nat
    -> color -> nat -> nat -> coloring -> __ stored_triple prefix' -> __
    stored_triple suffix' -> 'a1) -> (__ -> nat -> color -> nat -> nat ->
    coloring -> __ stored_triple prefix' -> __ stored_triple suffix' -> 'a1)
    -> nat -> kind -> ending -> color -> 'a2 storage -> 'a2 list -> 'a2
    storage_right_seq_graph -> 'a1 **)

let storage_right_seq_graph_rect f f0 f1 f2 f3 f4 _ _ _ _ _ _ = function
| Coq_storage_right_seq_graph_equation_1 (lvl, q, p) -> Obj.magic f __ lvl q p
| Coq_storage_right_seq_graph_equation_2 (lvl, qp, p0, s) ->
  Obj.magic f0 __ lvl qp p0 s
| Coq_storage_right_seq_graph_equation_3 (lvl, qs, p1, s) ->
  Obj.magic f1 __ lvl qs p1 s
| Coq_storage_right_seq_graph_equation_4 (lvl, c, qp0, qs0, c0, p2, s) ->
  Obj.magic f2 __ lvl c qp0 qs0 c0 p2 s
| Coq_storage_right_seq_graph_equation_5 (lvl, c, qp1, qs1, c0, p3, s) ->
  Obj.magic f3 __ lvl c qp1 qs1 c0 p3 s
| Coq_storage_right_seq_graph_equation_6 (lvl, c, qp2, qs2, c1, p4, s) ->
  Obj.magic f4 __ lvl c qp2 qs2 c1 p4 s

(** val storage_right_seq_graph_correct :
    nat -> kind -> ending -> color -> 'a1 storage -> 'a1
    storage_right_seq_graph **)

let storage_right_seq_graph_correct lvl _ _ _ = function
| Only_end (q, p) -> Coq_storage_right_seq_graph_equation_1 (lvl, q, p)
| Left_end (qp, p, s0) ->
  Coq_storage_right_seq_graph_equation_2 (lvl, qp, p, s0)
| Right_end (qs, p, s0) ->
  Coq_storage_right_seq_graph_equation_3 (lvl, qs, p, s0)
| Only_st (qp, qs, c, c0, p, s0) ->
  Coq_storage_right_seq_graph_equation_4 (lvl, c, qp, qs, c0, p, s0)
| Left_st (qp, qs, c, c0, p, s0) ->
  Coq_storage_right_seq_graph_equation_5 (lvl, c, qp, qs, c0, p, s0)
| Right_st (qp, qs, c, c0, p, s0) ->
  Coq_storage_right_seq_graph_equation_6 (lvl, c, qp, qs, c0, p, s0)

(** val storage_right_seq_elim :
    (__ -> nat -> nat -> __ stored_triple prefix' -> 'a1) -> (__ -> nat ->
    nat -> __ stored_triple prefix' -> __ stored_triple suffix' -> 'a1) ->
    (__ -> nat -> nat -> __ stored_triple prefix' -> __ stored_triple suffix'
    -> 'a1) -> (__ -> nat -> color -> nat -> nat -> coloring -> __
    stored_triple prefix' -> __ stored_triple suffix' -> 'a1) -> (__ -> nat
    -> color -> nat -> nat -> coloring -> __ stored_triple prefix' -> __
    stored_triple suffix' -> 'a1) -> (__ -> nat -> color -> nat -> nat ->
    coloring -> __ stored_triple prefix' -> __ stored_triple suffix' -> 'a1)
    -> nat -> kind -> ending -> color -> 'a2 storage -> 'a1 **)

let storage_right_seq_elim f f0 f1 f2 f3 f4 lvl k e c s =
  match storage_right_seq_graph_correct lvl k e c s with
  | Coq_storage_right_seq_graph_equation_1 (lvl0, q, p) ->
    Obj.magic f __ lvl0 q p
  | Coq_storage_right_seq_graph_equation_2 (lvl0, qp, p0, s0) ->
    Obj.magic f0 __ lvl0 qp p0 s0
  | Coq_storage_right_seq_graph_equation_3 (lvl0, qs, p1, s0) ->
    Obj.magic f1 __ lvl0 qs p1 s0
  | Coq_storage_right_seq_graph_equation_4 (lvl0, c0, qp0, qs0, c1, p2, s0) ->
    Obj.magic f2 __ lvl0 c0 qp0 qs0 c1 p2 s0
  | Coq_storage_right_seq_graph_equation_5 (lvl0, c0, qp1, qs1, c1, p3, s0) ->
    Obj.magic f3 __ lvl0 c0 qp1 qs1 c1 p3 s0
  | Coq_storage_right_seq_graph_equation_6 (lvl0, c0, qp2, qs2, c1, p4, s0) ->
    Obj.magic f4 __ lvl0 c0 qp2 qs2 c1 p4 s0

(** val coq_FunctionalElimination_storage_right_seq :
    (__ -> nat -> nat -> __ stored_triple prefix' -> __) -> (__ -> nat -> nat
    -> __ stored_triple prefix' -> __ stored_triple suffix' -> __) -> (__ ->
    nat -> nat -> __ stored_triple prefix' -> __ stored_triple suffix' -> __)
    -> (__ -> nat -> color -> nat -> nat -> coloring -> __ stored_triple
    prefix' -> __ stored_triple suffix' -> __) -> (__ -> nat -> color -> nat
    -> nat -> coloring -> __ stored_triple prefix' -> __ stored_triple
    suffix' -> __) -> (__ -> nat -> color -> nat -> nat -> coloring -> __
    stored_triple prefix' -> __ stored_triple suffix' -> __) -> nat -> kind
    -> ending -> color -> __ storage -> __ **)

let coq_FunctionalElimination_storage_right_seq =
  storage_right_seq_elim

(** val coq_FunctionalInduction_storage_right_seq :
    (__ -> nat -> kind -> ending -> color -> __ storage -> __ list)
    coq_FunctionalInduction **)

let coq_FunctionalInduction_storage_right_seq =
  Obj.magic (fun _ -> storage_right_seq_graph_correct)

(** val body_left_seq : nat -> nat -> kind -> kind -> 'a1 body -> 'a1 list **)

let rec body_left_seq _ _ _ _ = function
| Hole (_, _) -> Coq_nil
| Only_yellow (hlvl, tlvl, hk, tk, s, b0) ->
  app
    (storage_left_seq hlvl hk Not_end (Mix (NoGreen, SomeYellow, NoOrange,
      NoRed)) s) (body_left_seq (S hlvl) tlvl Only tk b0)
| Only_orange (hlvl, tlvl, hk, tk, s, b0) ->
  app
    (storage_left_seq hlvl hk Not_end (Mix (NoGreen, NoYellow, SomeOrange,
      NoRed)) s) (body_left_seq (S hlvl) tlvl Only tk b0)
| Pair_yellow (hlvl, tlvl, hk, tk, _, s, b0, _) ->
  app
    (storage_left_seq hlvl hk Not_end (Mix (NoGreen, SomeYellow, NoOrange,
      NoRed)) s) (body_left_seq (S hlvl) tlvl Left tk b0)
| Pair_orange (hlvl, tlvl, hk, tk, s, c, b0) ->
  app
    (storage_left_seq hlvl hk Not_end (Mix (NoGreen, NoYellow, SomeOrange,
      NoRed)) s)
    (app
      (chain_seq (S hlvl) Only Left Not_end (Mix (SomeGreen, NoYellow,
        NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c)
      (body_left_seq (S hlvl) tlvl Right tk b0))

type 'a body_left_seq_graph =
| Coq_body_left_seq_graph_equation_1 of nat * kind
| Coq_body_left_seq_graph_equation_2 of nat * nat * kind * kind
   * 'a stored_triple storage' * 'a body * 'a body_left_seq_graph
| Coq_body_left_seq_graph_equation_3 of nat * nat * kind * kind
   * 'a stored_triple storage' * 'a body * 'a body_left_seq_graph
| Coq_body_left_seq_graph_equation_4 of nat * nat * kind * kind * color
   * 'a stored_triple storage' * 'a body * 'a chain * 'a body_left_seq_graph
| Coq_body_left_seq_graph_equation_5 of nat * nat * kind * kind
   * 'a stored_triple storage' * 'a chain * 'a body * 'a body_left_seq_graph

(** val body_left_seq_graph_rect :
    (__ -> nat -> kind -> 'a1) -> (__ -> nat -> nat -> kind -> kind -> __
    stored_triple storage' -> __ body -> __ body_left_seq_graph -> 'a1 ->
    'a1) -> (__ -> nat -> nat -> kind -> kind -> __ stored_triple storage' ->
    __ body -> __ body_left_seq_graph -> 'a1 -> 'a1) -> (__ -> nat -> nat ->
    kind -> kind -> color -> __ stored_triple storage' -> __ body -> __ chain
    -> __ body_left_seq_graph -> 'a1 -> 'a1) -> (__ -> nat -> nat -> kind ->
    kind -> __ stored_triple storage' -> __ chain -> __ body -> __
    body_left_seq_graph -> 'a1 -> 'a1) -> nat -> nat -> kind -> kind -> 'a2
    body -> 'a2 list -> 'a2 body_left_seq_graph -> 'a1 **)

let rec body_left_seq_graph_rect f f0 f1 f2 f3 _ _ _ _ _ _ = function
| Coq_body_left_seq_graph_equation_1 (hlvl, hk) -> f __ hlvl hk
| Coq_body_left_seq_graph_equation_2 (hlvl, tlvl, hk, tk, hd, bd, hind) ->
  Obj.magic f0 __ hlvl tlvl hk tk hd bd hind
    (body_left_seq_graph_rect f f0 f1 f2 f3 (S hlvl) tlvl Only tk bd
      (body_left_seq (S hlvl) tlvl Only tk bd) hind)
| Coq_body_left_seq_graph_equation_3 (hlvl, tlvl, hk, tk, hd, bd, hind) ->
  Obj.magic f1 __ hlvl tlvl hk tk hd bd hind
    (body_left_seq_graph_rect f f0 f1 f2 f3 (S hlvl) tlvl Only tk bd
      (body_left_seq (S hlvl) tlvl Only tk bd) hind)
| Coq_body_left_seq_graph_equation_4 (hlvl, tlvl, hk, tk, c, hd, bd, c0, hind) ->
  Obj.magic f2 __ hlvl tlvl hk tk c hd bd c0 hind
    (body_left_seq_graph_rect f f0 f1 f2 f3 (S hlvl) tlvl Left tk bd
      (body_left_seq (S hlvl) tlvl Left tk bd) hind)
| Coq_body_left_seq_graph_equation_5 (hlvl, tlvl, hk, tk, hd, cl, bd, hind) ->
  Obj.magic f3 __ hlvl tlvl hk tk hd cl bd hind
    (body_left_seq_graph_rect f f0 f1 f2 f3 (S hlvl) tlvl Right tk bd
      (body_left_seq (S hlvl) tlvl Right tk bd) hind)

(** val body_left_seq_graph_correct :
    nat -> nat -> kind -> kind -> 'a1 body -> 'a1 body_left_seq_graph **)

let rec body_left_seq_graph_correct _ _ _ _ = function
| Hole (lvl, k) -> Coq_body_left_seq_graph_equation_1 (lvl, k)
| Only_yellow (hlvl, tlvl, hk, tk, s, b0) ->
  Coq_body_left_seq_graph_equation_2 (hlvl, tlvl, hk, tk, s, b0,
    (body_left_seq_graph_correct (S hlvl) tlvl Only tk b0))
| Only_orange (hlvl, tlvl, hk, tk, s, b0) ->
  Coq_body_left_seq_graph_equation_3 (hlvl, tlvl, hk, tk, s, b0,
    (body_left_seq_graph_correct (S hlvl) tlvl Only tk b0))
| Pair_yellow (hlvl, tlvl, hk, tk, c, s, b0, c0) ->
  Coq_body_left_seq_graph_equation_4 (hlvl, tlvl, hk, tk, c, s, b0, c0,
    (body_left_seq_graph_correct (S hlvl) tlvl Left tk b0))
| Pair_orange (hlvl, tlvl, hk, tk, s, c, b0) ->
  Coq_body_left_seq_graph_equation_5 (hlvl, tlvl, hk, tk, s, c, b0,
    (body_left_seq_graph_correct (S hlvl) tlvl Right tk b0))

(** val body_left_seq_elim :
    (__ -> nat -> kind -> 'a1) -> (__ -> nat -> nat -> kind -> kind -> __
    stored_triple storage' -> __ body -> 'a1 -> 'a1) -> (__ -> nat -> nat ->
    kind -> kind -> __ stored_triple storage' -> __ body -> 'a1 -> 'a1) ->
    (__ -> nat -> nat -> kind -> kind -> color -> __ stored_triple storage'
    -> __ body -> __ chain -> 'a1 -> 'a1) -> (__ -> nat -> nat -> kind ->
    kind -> __ stored_triple storage' -> __ chain -> __ body -> 'a1 -> 'a1)
    -> nat -> nat -> kind -> kind -> 'a2 body -> 'a1 **)

let body_left_seq_elim f f0 f1 f2 f3 hlvl tlvl hk tk b =
  let rec f4 _ _ _ _ _ _ = function
  | Coq_body_left_seq_graph_equation_1 (hlvl0, hk0) -> f __ hlvl0 hk0
  | Coq_body_left_seq_graph_equation_2 (hlvl0, tlvl0, hk0, tk0, hd, bd, hind) ->
    Obj.magic f0 __ hlvl0 tlvl0 hk0 tk0 hd bd
      (f4 (S hlvl0) tlvl0 Only tk0 bd
        (body_left_seq (S hlvl0) tlvl0 Only tk0 bd) hind)
  | Coq_body_left_seq_graph_equation_3 (hlvl0, tlvl0, hk0, tk0, hd, bd, hind) ->
    Obj.magic f1 __ hlvl0 tlvl0 hk0 tk0 hd bd
      (f4 (S hlvl0) tlvl0 Only tk0 bd
        (body_left_seq (S hlvl0) tlvl0 Only tk0 bd) hind)
  | Coq_body_left_seq_graph_equation_4 (hlvl0, tlvl0, hk0, tk0, c, hd, bd,
                                        c0, hind) ->
    Obj.magic f2 __ hlvl0 tlvl0 hk0 tk0 c hd bd c0
      (f4 (S hlvl0) tlvl0 Left tk0 bd
        (body_left_seq (S hlvl0) tlvl0 Left tk0 bd) hind)
  | Coq_body_left_seq_graph_equation_5 (hlvl0, tlvl0, hk0, tk0, hd, cl, bd,
                                        hind) ->
    Obj.magic f3 __ hlvl0 tlvl0 hk0 tk0 hd cl bd
      (f4 (S hlvl0) tlvl0 Right tk0 bd
        (body_left_seq (S hlvl0) tlvl0 Right tk0 bd) hind)
  in f4 hlvl tlvl hk tk b (body_left_seq hlvl tlvl hk tk b)
       (body_left_seq_graph_correct hlvl tlvl hk tk b)

(** val coq_FunctionalElimination_body_left_seq :
    (__ -> nat -> kind -> __) -> (__ -> nat -> nat -> kind -> kind -> __
    stored_triple storage' -> __ body -> __ -> __) -> (__ -> nat -> nat ->
    kind -> kind -> __ stored_triple storage' -> __ body -> __ -> __) -> (__
    -> nat -> nat -> kind -> kind -> color -> __ stored_triple storage' -> __
    body -> __ chain -> __ -> __) -> (__ -> nat -> nat -> kind -> kind -> __
    stored_triple storage' -> __ chain -> __ body -> __ -> __) -> nat -> nat
    -> kind -> kind -> __ body -> __ **)

let coq_FunctionalElimination_body_left_seq =
  body_left_seq_elim

(** val coq_FunctionalInduction_body_left_seq :
    (__ -> nat -> nat -> kind -> kind -> __ body -> __ list)
    coq_FunctionalInduction **)

let coq_FunctionalInduction_body_left_seq =
  Obj.magic (fun _ -> body_left_seq_graph_correct)

(** val body_right_seq :
    nat -> nat -> kind -> kind -> 'a1 body -> 'a1 list **)

let rec body_right_seq _ _ _ _ = function
| Hole (_, _) -> Coq_nil
| Only_yellow (hlvl, tlvl, hk, tk, s, b0) ->
  app (body_right_seq (S hlvl) tlvl Only tk b0)
    (storage_right_seq hlvl hk Not_end (Mix (NoGreen, SomeYellow, NoOrange,
      NoRed)) s)
| Only_orange (hlvl, tlvl, hk, tk, s, b0) ->
  app (body_right_seq (S hlvl) tlvl Only tk b0)
    (storage_right_seq hlvl hk Not_end (Mix (NoGreen, NoYellow, SomeOrange,
      NoRed)) s)
| Pair_yellow (hlvl, tlvl, hk, tk, c, s, b0, c0) ->
  app (body_right_seq (S hlvl) tlvl Left tk b0)
    (app (chain_seq (S hlvl) Only Right Not_end c c c0)
      (storage_right_seq hlvl hk Not_end (Mix (NoGreen, SomeYellow, NoOrange,
        NoRed)) s))
| Pair_orange (hlvl, tlvl, hk, tk, s, _, b0) ->
  app (body_right_seq (S hlvl) tlvl Right tk b0)
    (storage_right_seq hlvl hk Not_end (Mix (NoGreen, NoYellow, SomeOrange,
      NoRed)) s)

type 'a body_right_seq_graph =
| Coq_body_right_seq_graph_equation_1 of nat * kind
| Coq_body_right_seq_graph_equation_2 of nat * nat * kind * kind
   * 'a stored_triple storage' * 'a body * 'a body_right_seq_graph
| Coq_body_right_seq_graph_equation_3 of nat * nat * kind * kind
   * 'a stored_triple storage' * 'a body * 'a body_right_seq_graph
| Coq_body_right_seq_graph_equation_4 of nat * nat * kind * kind * color
   * 'a stored_triple storage' * 'a body * 'a chain * 'a body_right_seq_graph
| Coq_body_right_seq_graph_equation_5 of nat * nat * kind * kind
   * 'a stored_triple storage' * 'a chain * 'a body * 'a body_right_seq_graph

(** val body_right_seq_graph_rect :
    (__ -> nat -> kind -> 'a1) -> (__ -> nat -> nat -> kind -> kind -> __
    stored_triple storage' -> __ body -> __ body_right_seq_graph -> 'a1 ->
    'a1) -> (__ -> nat -> nat -> kind -> kind -> __ stored_triple storage' ->
    __ body -> __ body_right_seq_graph -> 'a1 -> 'a1) -> (__ -> nat -> nat ->
    kind -> kind -> color -> __ stored_triple storage' -> __ body -> __ chain
    -> __ body_right_seq_graph -> 'a1 -> 'a1) -> (__ -> nat -> nat -> kind ->
    kind -> __ stored_triple storage' -> __ chain -> __ body -> __
    body_right_seq_graph -> 'a1 -> 'a1) -> nat -> nat -> kind -> kind -> 'a2
    body -> 'a2 list -> 'a2 body_right_seq_graph -> 'a1 **)

let rec body_right_seq_graph_rect f f0 f1 f2 f3 _ _ _ _ _ _ = function
| Coq_body_right_seq_graph_equation_1 (hlvl, hk) -> f __ hlvl hk
| Coq_body_right_seq_graph_equation_2 (hlvl, tlvl, hk, tk, hd, bd, hind) ->
  Obj.magic f0 __ hlvl tlvl hk tk hd bd hind
    (body_right_seq_graph_rect f f0 f1 f2 f3 (S hlvl) tlvl Only tk bd
      (body_right_seq (S hlvl) tlvl Only tk bd) hind)
| Coq_body_right_seq_graph_equation_3 (hlvl, tlvl, hk, tk, hd, bd, hind) ->
  Obj.magic f1 __ hlvl tlvl hk tk hd bd hind
    (body_right_seq_graph_rect f f0 f1 f2 f3 (S hlvl) tlvl Only tk bd
      (body_right_seq (S hlvl) tlvl Only tk bd) hind)
| Coq_body_right_seq_graph_equation_4 (hlvl, tlvl, hk, tk, c, hd, bd, cr, hind) ->
  Obj.magic f2 __ hlvl tlvl hk tk c hd bd cr hind
    (body_right_seq_graph_rect f f0 f1 f2 f3 (S hlvl) tlvl Left tk bd
      (body_right_seq (S hlvl) tlvl Left tk bd) hind)
| Coq_body_right_seq_graph_equation_5 (hlvl, tlvl, hk, tk, hd, c0, bd, hind) ->
  Obj.magic f3 __ hlvl tlvl hk tk hd c0 bd hind
    (body_right_seq_graph_rect f f0 f1 f2 f3 (S hlvl) tlvl Right tk bd
      (body_right_seq (S hlvl) tlvl Right tk bd) hind)

(** val body_right_seq_graph_correct :
    nat -> nat -> kind -> kind -> 'a1 body -> 'a1 body_right_seq_graph **)

let rec body_right_seq_graph_correct _ _ _ _ = function
| Hole (lvl, k) -> Coq_body_right_seq_graph_equation_1 (lvl, k)
| Only_yellow (hlvl, tlvl, hk, tk, s, b0) ->
  Coq_body_right_seq_graph_equation_2 (hlvl, tlvl, hk, tk, s, b0,
    (body_right_seq_graph_correct (S hlvl) tlvl Only tk b0))
| Only_orange (hlvl, tlvl, hk, tk, s, b0) ->
  Coq_body_right_seq_graph_equation_3 (hlvl, tlvl, hk, tk, s, b0,
    (body_right_seq_graph_correct (S hlvl) tlvl Only tk b0))
| Pair_yellow (hlvl, tlvl, hk, tk, c, s, b0, c0) ->
  Coq_body_right_seq_graph_equation_4 (hlvl, tlvl, hk, tk, c, s, b0, c0,
    (body_right_seq_graph_correct (S hlvl) tlvl Left tk b0))
| Pair_orange (hlvl, tlvl, hk, tk, s, c, b0) ->
  Coq_body_right_seq_graph_equation_5 (hlvl, tlvl, hk, tk, s, c, b0,
    (body_right_seq_graph_correct (S hlvl) tlvl Right tk b0))

(** val body_right_seq_elim :
    (__ -> nat -> kind -> 'a1) -> (__ -> nat -> nat -> kind -> kind -> __
    stored_triple storage' -> __ body -> 'a1 -> 'a1) -> (__ -> nat -> nat ->
    kind -> kind -> __ stored_triple storage' -> __ body -> 'a1 -> 'a1) ->
    (__ -> nat -> nat -> kind -> kind -> color -> __ stored_triple storage'
    -> __ body -> __ chain -> 'a1 -> 'a1) -> (__ -> nat -> nat -> kind ->
    kind -> __ stored_triple storage' -> __ chain -> __ body -> 'a1 -> 'a1)
    -> nat -> nat -> kind -> kind -> 'a2 body -> 'a1 **)

let body_right_seq_elim f f0 f1 f2 f3 hlvl tlvl hk tk b =
  let rec f4 _ _ _ _ _ _ = function
  | Coq_body_right_seq_graph_equation_1 (hlvl0, hk0) -> f __ hlvl0 hk0
  | Coq_body_right_seq_graph_equation_2 (hlvl0, tlvl0, hk0, tk0, hd, bd, hind) ->
    Obj.magic f0 __ hlvl0 tlvl0 hk0 tk0 hd bd
      (f4 (S hlvl0) tlvl0 Only tk0 bd
        (body_right_seq (S hlvl0) tlvl0 Only tk0 bd) hind)
  | Coq_body_right_seq_graph_equation_3 (hlvl0, tlvl0, hk0, tk0, hd, bd, hind) ->
    Obj.magic f1 __ hlvl0 tlvl0 hk0 tk0 hd bd
      (f4 (S hlvl0) tlvl0 Only tk0 bd
        (body_right_seq (S hlvl0) tlvl0 Only tk0 bd) hind)
  | Coq_body_right_seq_graph_equation_4 (hlvl0, tlvl0, hk0, tk0, c, hd, bd,
                                         cr, hind) ->
    Obj.magic f2 __ hlvl0 tlvl0 hk0 tk0 c hd bd cr
      (f4 (S hlvl0) tlvl0 Left tk0 bd
        (body_right_seq (S hlvl0) tlvl0 Left tk0 bd) hind)
  | Coq_body_right_seq_graph_equation_5 (hlvl0, tlvl0, hk0, tk0, hd, c0, bd,
                                         hind) ->
    Obj.magic f3 __ hlvl0 tlvl0 hk0 tk0 hd c0 bd
      (f4 (S hlvl0) tlvl0 Right tk0 bd
        (body_right_seq (S hlvl0) tlvl0 Right tk0 bd) hind)
  in f4 hlvl tlvl hk tk b (body_right_seq hlvl tlvl hk tk b)
       (body_right_seq_graph_correct hlvl tlvl hk tk b)

(** val coq_FunctionalElimination_body_right_seq :
    (__ -> nat -> kind -> __) -> (__ -> nat -> nat -> kind -> kind -> __
    stored_triple storage' -> __ body -> __ -> __) -> (__ -> nat -> nat ->
    kind -> kind -> __ stored_triple storage' -> __ body -> __ -> __) -> (__
    -> nat -> nat -> kind -> kind -> color -> __ stored_triple storage' -> __
    body -> __ chain -> __ -> __) -> (__ -> nat -> nat -> kind -> kind -> __
    stored_triple storage' -> __ chain -> __ body -> __ -> __) -> nat -> nat
    -> kind -> kind -> __ body -> __ **)

let coq_FunctionalElimination_body_right_seq =
  body_right_seq_elim

(** val coq_FunctionalInduction_body_right_seq :
    (__ -> nat -> nat -> kind -> kind -> __ body -> __ list)
    coq_FunctionalInduction **)

let coq_FunctionalInduction_body_right_seq =
  Obj.magic (fun _ -> body_right_seq_graph_correct)

(** val packet_left_seq :
    nat -> nat -> kind -> ending -> color -> 'a1 packet -> 'a1 list **)

let packet_left_seq _ _ _ _ _ = function
| Packet (hlvl, tlvl, hk, tk, e, g, r, b, s) ->
  app (body_left_seq hlvl tlvl hk tk b)
    (storage_left_seq tlvl tk e (Mix (g, NoYellow, NoOrange, r)) s)

type 'a packet_left_seq_graph =
| Coq_packet_left_seq_graph_equation_1 of nat * nat * kind * ending
   * green_hue * red_hue * kind * 'a body * 'a stored_triple storage'

(** val packet_left_seq_graph_rect :
    (__ -> nat -> nat -> kind -> ending -> green_hue -> red_hue -> kind -> __
    body -> __ stored_triple storage' -> 'a1) -> nat -> nat -> kind -> ending
    -> color -> 'a2 packet -> 'a2 list -> 'a2 packet_left_seq_graph -> 'a1 **)

let packet_left_seq_graph_rect f _ _ _ _ _ _ _ = function
| Coq_packet_left_seq_graph_equation_1 (hlvl, tlvl, k, e, g0, r0, tk, bd, tl) ->
  Obj.magic f __ hlvl tlvl k e g0 r0 tk bd tl

(** val packet_left_seq_graph_correct :
    nat -> nat -> kind -> ending -> color -> 'a1 packet -> 'a1
    packet_left_seq_graph **)

let packet_left_seq_graph_correct _ _ _ _ _ = function
| Packet (hlvl, tlvl, hk, tk, e, g, r, b, s) ->
  Coq_packet_left_seq_graph_equation_1 (hlvl, tlvl, hk, e, g, r, tk, b, s)

(** val packet_left_seq_elim :
    (__ -> nat -> nat -> kind -> ending -> green_hue -> red_hue -> kind -> __
    body -> __ stored_triple storage' -> 'a1) -> nat -> nat -> kind -> ending
    -> color -> 'a2 packet -> 'a1 **)

let packet_left_seq_elim f hlvl tlvl k e c p =
  let Coq_packet_left_seq_graph_equation_1 (hlvl0, tlvl0, k0, e0, g0, r0, tk,
                                            bd, tl) =
    packet_left_seq_graph_correct hlvl tlvl k e c p
  in
  Obj.magic f __ hlvl0 tlvl0 k0 e0 g0 r0 tk bd tl

(** val coq_FunctionalElimination_packet_left_seq :
    (__ -> nat -> nat -> kind -> ending -> green_hue -> red_hue -> kind -> __
    body -> __ stored_triple storage' -> __) -> nat -> nat -> kind -> ending
    -> color -> __ packet -> __ **)

let coq_FunctionalElimination_packet_left_seq =
  packet_left_seq_elim

(** val coq_FunctionalInduction_packet_left_seq :
    (__ -> nat -> nat -> kind -> ending -> color -> __ packet -> __ list)
    coq_FunctionalInduction **)

let coq_FunctionalInduction_packet_left_seq =
  Obj.magic (fun _ -> packet_left_seq_graph_correct)

(** val packet_right_seq :
    nat -> nat -> kind -> ending -> color -> 'a1 packet -> 'a1 list **)

let packet_right_seq _ _ _ _ _ = function
| Packet (hlvl, tlvl, hk, tk, e, g, r, b, s) ->
  app (storage_right_seq tlvl tk e (Mix (g, NoYellow, NoOrange, r)) s)
    (body_right_seq hlvl tlvl hk tk b)

type 'a packet_right_seq_graph =
| Coq_packet_right_seq_graph_equation_1 of nat * nat * kind * ending
   * green_hue * red_hue * kind * 'a body * 'a stored_triple storage'

(** val packet_right_seq_graph_rect :
    (__ -> nat -> nat -> kind -> ending -> green_hue -> red_hue -> kind -> __
    body -> __ stored_triple storage' -> 'a1) -> nat -> nat -> kind -> ending
    -> color -> 'a2 packet -> 'a2 list -> 'a2 packet_right_seq_graph -> 'a1 **)

let packet_right_seq_graph_rect f _ _ _ _ _ _ _ = function
| Coq_packet_right_seq_graph_equation_1 (hlvl, tlvl, k, e, g0, r0, tk, bd, tl) ->
  Obj.magic f __ hlvl tlvl k e g0 r0 tk bd tl

(** val packet_right_seq_graph_correct :
    nat -> nat -> kind -> ending -> color -> 'a1 packet -> 'a1
    packet_right_seq_graph **)

let packet_right_seq_graph_correct _ _ _ _ _ = function
| Packet (hlvl, tlvl, hk, tk, e, g, r, b, s) ->
  Coq_packet_right_seq_graph_equation_1 (hlvl, tlvl, hk, e, g, r, tk, b, s)

(** val packet_right_seq_elim :
    (__ -> nat -> nat -> kind -> ending -> green_hue -> red_hue -> kind -> __
    body -> __ stored_triple storage' -> 'a1) -> nat -> nat -> kind -> ending
    -> color -> 'a2 packet -> 'a1 **)

let packet_right_seq_elim f hlvl tlvl k e c p =
  let Coq_packet_right_seq_graph_equation_1 (hlvl0, tlvl0, k0, e0, g0, r0,
                                             tk, bd, tl) =
    packet_right_seq_graph_correct hlvl tlvl k e c p
  in
  Obj.magic f __ hlvl0 tlvl0 k0 e0 g0 r0 tk bd tl

(** val coq_FunctionalElimination_packet_right_seq :
    (__ -> nat -> nat -> kind -> ending -> green_hue -> red_hue -> kind -> __
    body -> __ stored_triple storage' -> __) -> nat -> nat -> kind -> ending
    -> color -> __ packet -> __ **)

let coq_FunctionalElimination_packet_right_seq =
  packet_right_seq_elim

(** val coq_FunctionalInduction_packet_right_seq :
    (__ -> nat -> nat -> kind -> ending -> color -> __ packet -> __ list)
    coq_FunctionalInduction **)

let coq_FunctionalInduction_packet_right_seq =
  Obj.magic (fun _ -> packet_right_seq_graph_correct)

(** val ne_chain_seq :
    nat -> kind -> kind -> color -> color -> 'a1 non_ending_chain -> 'a1 list **)

let ne_chain_seq _ _ _ _ _ = function
| NE_chain (lvl, pk, k, e, cl, cr, c) -> chain_seq lvl pk k e cl cr c

type 'a ne_chain_seq_graph =
| Coq_ne_chain_seq_graph_equation_1 of nat * kind * kind * color * color
   * ending * 'a chain

(** val ne_chain_seq_graph_rect :
    (__ -> nat -> kind -> kind -> color -> color -> ending -> __ chain ->
    'a1) -> nat -> kind -> kind -> color -> color -> 'a2 non_ending_chain ->
    'a2 list -> 'a2 ne_chain_seq_graph -> 'a1 **)

let ne_chain_seq_graph_rect f _ _ _ _ _ _ _ = function
| Coq_ne_chain_seq_graph_equation_1 (lvl, pk, k, cl, cr, e, c) ->
  Obj.magic f __ lvl pk k cl cr e c

(** val ne_chain_seq_graph_correct :
    nat -> kind -> kind -> color -> color -> 'a1 non_ending_chain -> 'a1
    ne_chain_seq_graph **)

let ne_chain_seq_graph_correct _ _ _ _ _ = function
| NE_chain (lvl, pk, k, e, cl, cr, c) ->
  Coq_ne_chain_seq_graph_equation_1 (lvl, pk, k, cl, cr, e, c)

(** val ne_chain_seq_elim :
    (__ -> nat -> kind -> kind -> color -> color -> ending -> __ chain ->
    'a1) -> nat -> kind -> kind -> color -> color -> 'a2 non_ending_chain ->
    'a1 **)

let ne_chain_seq_elim f lvl pk k cl cr n =
  let Coq_ne_chain_seq_graph_equation_1 (lvl0, pk0, k0, cl0, cr0, e, c) =
    ne_chain_seq_graph_correct lvl pk k cl cr n
  in
  Obj.magic f __ lvl0 pk0 k0 cl0 cr0 e c

(** val coq_FunctionalElimination_ne_chain_seq :
    (__ -> nat -> kind -> kind -> color -> color -> ending -> __ chain -> __)
    -> nat -> kind -> kind -> color -> color -> __ non_ending_chain -> __ **)

let coq_FunctionalElimination_ne_chain_seq =
  ne_chain_seq_elim

(** val coq_FunctionalInduction_ne_chain_seq :
    (__ -> nat -> kind -> kind -> color -> color -> __ non_ending_chain -> __
    list) coq_FunctionalInduction **)

let coq_FunctionalInduction_ne_chain_seq =
  Obj.magic (fun _ -> ne_chain_seq_graph_correct)

(** val triple_seq : nat -> kind -> color -> 'a1 triple -> 'a1 list **)

let triple_seq _ _ _ = function
| Triple (lvl, pk, k, e, c, cl, cr, _, _, s, c0) ->
  app (storage_left_seq lvl k e c s)
    (app (chain_seq (S lvl) pk Only e cl cr c0)
      (storage_right_seq lvl k e c s))

type 'a triple_seq_graph =
| Coq_triple_seq_graph_equation_1 of nat * kind * color * kind * ending
   * color * color * color * regularity * 'a storage * 'a chain

(** val triple_seq_graph_rect :
    (__ -> nat -> kind -> color -> kind -> ending -> color -> color -> color
    -> regularity -> __ storage -> __ chain -> 'a1) -> nat -> kind -> color
    -> 'a2 triple -> 'a2 list -> 'a2 triple_seq_graph -> 'a1 **)

let triple_seq_graph_rect f _ _ _ _ _ = function
| Coq_triple_seq_graph_equation_1 (lvl, k, c, pk, e, c0, cl, cr, r, hd, child) ->
  Obj.magic f __ lvl k c pk e c0 cl cr r hd child

(** val triple_seq_graph_correct :
    nat -> kind -> color -> 'a1 triple -> 'a1 triple_seq_graph **)

let triple_seq_graph_correct _ _ _ = function
| Triple (lvl, pk, k, e, c, cl, cr, cpkt, r, s, c0) ->
  Coq_triple_seq_graph_equation_1 (lvl, k, cpkt, pk, e, c, cl, cr, r, s, c0)

(** val triple_seq_elim :
    (__ -> nat -> kind -> color -> kind -> ending -> color -> color -> color
    -> regularity -> __ storage -> __ chain -> 'a1) -> nat -> kind -> color
    -> 'a2 triple -> 'a1 **)

let triple_seq_elim f lvl k c t0 =
  let Coq_triple_seq_graph_equation_1 (lvl0, k0, c0, pk, e, c1, cl, cr, r,
                                       hd, child) =
    triple_seq_graph_correct lvl k c t0
  in
  Obj.magic f __ lvl0 k0 c0 pk e c1 cl cr r hd child

(** val coq_FunctionalElimination_triple_seq :
    (__ -> nat -> kind -> color -> kind -> ending -> color -> color -> color
    -> regularity -> __ storage -> __ chain -> __) -> nat -> kind -> color ->
    __ triple -> __ **)

let coq_FunctionalElimination_triple_seq =
  triple_seq_elim

(** val coq_FunctionalInduction_triple_seq :
    (__ -> nat -> kind -> color -> __ triple -> __ list)
    coq_FunctionalInduction **)

let coq_FunctionalInduction_triple_seq =
  Obj.magic (fun _ -> triple_seq_graph_correct)

(** val lr_triple_seq :
    nat -> kind -> color -> 'a1 left_right_triple -> 'a1 list **)

let lr_triple_seq _ _ _ = function
| Not_enough (lvl, _, v) ->
  concat
    (map (stored_triple_seq lvl)
      (vector_seq (S (S (S (S (S (S Datatypes.O)))))) v))
| Ok_lrt (lvl, k, cpkt, t0) -> triple_seq lvl k cpkt t0

type 'a lr_triple_seq_graph =
| Coq_lr_triple_seq_graph_equation_1 of nat * kind * 'a stored_triple vector
| Coq_lr_triple_seq_graph_equation_2 of nat * kind * color * 'a triple

(** val lr_triple_seq_graph_rect :
    (__ -> nat -> kind -> __ stored_triple vector -> 'a1) -> (__ -> nat ->
    kind -> color -> __ triple -> 'a1) -> nat -> kind -> color -> 'a2
    left_right_triple -> 'a2 list -> 'a2 lr_triple_seq_graph -> 'a1 **)

let lr_triple_seq_graph_rect f f0 _ _ _ _ _ = function
| Coq_lr_triple_seq_graph_equation_1 (lvl, k, v) -> Obj.magic f __ lvl k v
| Coq_lr_triple_seq_graph_equation_2 (lvl, k, c, t0) ->
  Obj.magic f0 __ lvl k c t0

(** val lr_triple_seq_graph_correct :
    nat -> kind -> color -> 'a1 left_right_triple -> 'a1 lr_triple_seq_graph **)

let lr_triple_seq_graph_correct _ _ _ = function
| Not_enough (lvl, k, v) -> Coq_lr_triple_seq_graph_equation_1 (lvl, k, v)
| Ok_lrt (lvl, k, cpkt, t0) ->
  Coq_lr_triple_seq_graph_equation_2 (lvl, k, cpkt, t0)

(** val lr_triple_seq_elim :
    (__ -> nat -> kind -> __ stored_triple vector -> 'a1) -> (__ -> nat ->
    kind -> color -> __ triple -> 'a1) -> nat -> kind -> color -> 'a2
    left_right_triple -> 'a1 **)

let lr_triple_seq_elim f f0 lvl k c l =
  match lr_triple_seq_graph_correct lvl k c l with
  | Coq_lr_triple_seq_graph_equation_1 (lvl0, k0, v) ->
    Obj.magic f __ lvl0 k0 v
  | Coq_lr_triple_seq_graph_equation_2 (lvl0, k0, c0, t0) ->
    Obj.magic f0 __ lvl0 k0 c0 t0

(** val coq_FunctionalElimination_lr_triple_seq :
    (__ -> nat -> kind -> __ stored_triple vector -> __) -> (__ -> nat ->
    kind -> color -> __ triple -> __) -> nat -> kind -> color -> __
    left_right_triple -> __ **)

let coq_FunctionalElimination_lr_triple_seq =
  lr_triple_seq_elim

(** val coq_FunctionalInduction_lr_triple_seq :
    (__ -> nat -> kind -> color -> __ left_right_triple -> __ list)
    coq_FunctionalInduction **)

let coq_FunctionalInduction_lr_triple_seq =
  Obj.magic (fun _ -> lr_triple_seq_graph_correct)

(** val six_stored_triple_seq : nat -> 'a1 six_stored_triple -> 'a1 list **)

let six_stored_triple_seq lvl = function
| Coq_pair (p, s0) ->
  let Coq_pair (p0, s1) = p in
  let Coq_pair (p1, s2) = p0 in
  let Coq_pair (p2, s3) = p1 in
  let Coq_pair (s4, s5) = p2 in
  app (stored_triple_seq lvl s4)
    (app (stored_triple_seq lvl s5)
      (app (stored_triple_seq lvl s3)
        (app (stored_triple_seq lvl s2)
          (app (stored_triple_seq lvl s1) (stored_triple_seq lvl s0)))))

type 'a six_stored_triple_seq_graph =
| Coq_six_stored_triple_seq_graph_equation_1 of nat * 'a stored_triple
   * 'a stored_triple * 'a stored_triple * 'a stored_triple
   * 'a stored_triple * 'a stored_triple

(** val six_stored_triple_seq_graph_rect :
    (__ -> nat -> __ stored_triple -> __ stored_triple -> __ stored_triple ->
    __ stored_triple -> __ stored_triple -> __ stored_triple -> 'a1) -> nat
    -> 'a2 six_stored_triple -> 'a2 list -> 'a2 six_stored_triple_seq_graph
    -> 'a1 **)

let six_stored_triple_seq_graph_rect f _ _ _ = function
| Coq_six_stored_triple_seq_graph_equation_1 (lvl, a1, a2, a3, a4, a5, a6) ->
  Obj.magic f __ lvl a1 a2 a3 a4 a5 a6

(** val six_stored_triple_seq_graph_correct :
    nat -> 'a1 six_stored_triple -> 'a1 six_stored_triple_seq_graph **)

let six_stored_triple_seq_graph_correct lvl = function
| Coq_pair (p, s0) ->
  let Coq_pair (p0, s1) = p in
  let Coq_pair (p1, s2) = p0 in
  let Coq_pair (p2, s3) = p1 in
  let Coq_pair (s4, s5) = p2 in
  Coq_six_stored_triple_seq_graph_equation_1 (lvl, s4, s5, s3, s2, s1, s0)

(** val six_stored_triple_seq_elim :
    (__ -> nat -> __ stored_triple -> __ stored_triple -> __ stored_triple ->
    __ stored_triple -> __ stored_triple -> __ stored_triple -> 'a1) -> nat
    -> 'a2 six_stored_triple -> 'a1 **)

let six_stored_triple_seq_elim f lvl s =
  let Coq_six_stored_triple_seq_graph_equation_1 (lvl0, a1, a2, a3, a4, a5, a6) =
    six_stored_triple_seq_graph_correct lvl s
  in
  Obj.magic f __ lvl0 a1 a2 a3 a4 a5 a6

(** val coq_FunctionalElimination_six_stored_triple_seq :
    (__ -> nat -> __ stored_triple -> __ stored_triple -> __ stored_triple ->
    __ stored_triple -> __ stored_triple -> __ stored_triple -> __) -> nat ->
    __ six_stored_triple -> __ **)

let coq_FunctionalElimination_six_stored_triple_seq =
  six_stored_triple_seq_elim

(** val coq_FunctionalInduction_six_stored_triple_seq :
    (__ -> nat -> __ six_stored_triple -> __ list) coq_FunctionalInduction **)

let coq_FunctionalInduction_six_stored_triple_seq =
  Obj.magic (fun _ -> six_stored_triple_seq_graph_correct)

(** val pt_triple_seq :
    nat -> kind -> kind -> 'a1 partial_triple -> 'a1 list **)

let pt_triple_seq _ _ _ = function
| Zero_element (_, _) -> Coq_nil
| Six_elements (lvl, _, s) -> six_stored_triple_seq lvl s
| Ok_pt (lvl, _, k, c, t0) -> triple_seq lvl k c t0

type 'a pt_triple_seq_graph =
| Coq_pt_triple_seq_graph_equation_1 of nat * kind
| Coq_pt_triple_seq_graph_equation_2 of nat * kind * 'a six_stored_triple
| Coq_pt_triple_seq_graph_equation_3 of nat * kind * kind * color * 'a triple

(** val pt_triple_seq_graph_rect :
    (__ -> nat -> kind -> 'a1) -> (__ -> nat -> kind -> __ six_stored_triple
    -> 'a1) -> (__ -> nat -> kind -> kind -> color -> __ triple -> 'a1) ->
    nat -> kind -> kind -> 'a2 partial_triple -> 'a2 list -> 'a2
    pt_triple_seq_graph -> 'a1 **)

let pt_triple_seq_graph_rect f f0 f1 _ _ _ _ _ = function
| Coq_pt_triple_seq_graph_equation_1 (lvl, k) -> f __ lvl k
| Coq_pt_triple_seq_graph_equation_2 (lvl, k, six) ->
  Obj.magic f0 __ lvl k six
| Coq_pt_triple_seq_graph_equation_3 (lvl, pk, k, c, t0) ->
  Obj.magic f1 __ lvl pk k c t0

(** val pt_triple_seq_graph_correct :
    nat -> kind -> kind -> 'a1 partial_triple -> 'a1 pt_triple_seq_graph **)

let pt_triple_seq_graph_correct _ _ _ = function
| Zero_element (lvl, k) -> Coq_pt_triple_seq_graph_equation_1 (lvl, k)
| Six_elements (lvl, k, s) -> Coq_pt_triple_seq_graph_equation_2 (lvl, k, s)
| Ok_pt (lvl, pk, k, c, t0) ->
  Coq_pt_triple_seq_graph_equation_3 (lvl, pk, k, c, t0)

(** val pt_triple_seq_elim :
    (__ -> nat -> kind -> 'a1) -> (__ -> nat -> kind -> __ six_stored_triple
    -> 'a1) -> (__ -> nat -> kind -> kind -> color -> __ triple -> 'a1) ->
    nat -> kind -> kind -> 'a2 partial_triple -> 'a1 **)

let pt_triple_seq_elim f f0 f1 lvl pk k p =
  match pt_triple_seq_graph_correct lvl pk k p with
  | Coq_pt_triple_seq_graph_equation_1 (lvl0, k0) -> f __ lvl0 k0
  | Coq_pt_triple_seq_graph_equation_2 (lvl0, k0, six) ->
    Obj.magic f0 __ lvl0 k0 six
  | Coq_pt_triple_seq_graph_equation_3 (lvl0, pk0, k0, c, t0) ->
    Obj.magic f1 __ lvl0 pk0 k0 c t0

(** val coq_FunctionalElimination_pt_triple_seq :
    (__ -> nat -> kind -> __) -> (__ -> nat -> kind -> __ six_stored_triple
    -> __) -> (__ -> nat -> kind -> kind -> color -> __ triple -> __) -> nat
    -> kind -> kind -> __ partial_triple -> __ **)

let coq_FunctionalElimination_pt_triple_seq =
  pt_triple_seq_elim

(** val coq_FunctionalInduction_pt_triple_seq :
    (__ -> nat -> kind -> kind -> __ partial_triple -> __ list)
    coq_FunctionalInduction **)

let coq_FunctionalInduction_pt_triple_seq =
  Obj.magic (fun _ -> pt_triple_seq_graph_correct)

(** val sandwich_seq :
    ('a1 -> 'a3 list) -> ('a2 -> 'a3 list) -> ('a1, 'a2) sandwich -> 'a3 list **)

let sandwich_seq l l0 = function
| Alone a -> l a
| Sandwich (a, b, a0) -> app (l a) (app (l0 b) (l a0))

type ('a, 'b, 'c) sandwich_seq_graph =
| Coq_sandwich_seq_graph_equation_1 of ('a -> 'c list) * ('b -> 'c list) * 'a
| Coq_sandwich_seq_graph_equation_2 of ('a -> 'c list) * ('b -> 'c list) *
   'a * 'b * 'a

(** val sandwich_seq_graph_rect :
    (__ -> __ -> __ -> (__ -> __ list) -> (__ -> __ list) -> __ -> 'a1) ->
    (__ -> __ -> __ -> (__ -> __ list) -> (__ -> __ list) -> __ -> __ -> __
    -> 'a1) -> ('a2 -> 'a4 list) -> ('a3 -> 'a4 list) -> ('a2, 'a3) sandwich
    -> 'a4 list -> ('a2, 'a3, 'a4) sandwich_seq_graph -> 'a1 **)

let sandwich_seq_graph_rect f f0 _ _ _ _ = function
| Coq_sandwich_seq_graph_equation_1 (a_seq, l0, a) ->
  Obj.magic f __ __ __ a_seq l0 a
| Coq_sandwich_seq_graph_equation_2 (a_seq, b_seq, a, m, z) ->
  Obj.magic f0 __ __ __ a_seq b_seq a m z

(** val sandwich_seq_graph_correct :
    ('a1 -> 'a3 list) -> ('a2 -> 'a3 list) -> ('a1, 'a2) sandwich -> ('a1,
    'a2, 'a3) sandwich_seq_graph **)

let sandwich_seq_graph_correct l l0 = function
| Alone a -> Coq_sandwich_seq_graph_equation_1 (l, l0, a)
| Sandwich (a, b, a0) -> Coq_sandwich_seq_graph_equation_2 (l, l0, a, b, a0)

(** val sandwich_seq_elim :
    (__ -> __ -> __ -> (__ -> __ list) -> (__ -> __ list) -> __ -> 'a1) ->
    (__ -> __ -> __ -> (__ -> __ list) -> (__ -> __ list) -> __ -> __ -> __
    -> 'a1) -> ('a2 -> 'a4 list) -> ('a3 -> 'a4 list) -> ('a2, 'a3) sandwich
    -> 'a1 **)

let sandwich_seq_elim f f0 l l0 s =
  match sandwich_seq_graph_correct l l0 s with
  | Coq_sandwich_seq_graph_equation_1 (a_seq, l1, a) ->
    Obj.magic f __ __ __ a_seq l1 a
  | Coq_sandwich_seq_graph_equation_2 (a_seq, b_seq, a, m, z) ->
    Obj.magic f0 __ __ __ a_seq b_seq a m z

(** val coq_FunctionalElimination_sandwich_seq :
    (__ -> __ -> __ -> (__ -> __ list) -> (__ -> __ list) -> __ -> __) -> (__
    -> __ -> __ -> (__ -> __ list) -> (__ -> __ list) -> __ -> __ -> __ ->
    __) -> (__ -> __ list) -> (__ -> __ list) -> (__, __) sandwich -> __ **)

let coq_FunctionalElimination_sandwich_seq =
  sandwich_seq_elim

(** val coq_FunctionalInduction_sandwich_seq :
    (__ -> __ -> __ -> (__ -> __ list) -> (__ -> __ list) -> (__, __)
    sandwich -> __ list) coq_FunctionalInduction **)

let coq_FunctionalInduction_sandwich_seq =
  Obj.magic (fun _ _ _ -> sandwich_seq_graph_correct)

(** val semi_deque_seq : nat -> 'a1 semi_deque -> 'a1 list **)

let semi_deque_seq _ = function
| Semi (lvl, pk, e, cl, cr, c) -> chain_seq lvl pk Only e cl cr c

type 'a semi_deque_seq_graph =
| Coq_semi_deque_seq_graph_equation_1 of nat * kind * ending * color *
   color * 'a chain

(** val semi_deque_seq_graph_rect :
    (__ -> nat -> kind -> ending -> color -> color -> __ chain -> 'a1) -> nat
    -> 'a2 semi_deque -> 'a2 list -> 'a2 semi_deque_seq_graph -> 'a1 **)

let semi_deque_seq_graph_rect f _ _ _ = function
| Coq_semi_deque_seq_graph_equation_1 (lvl, pk, e, cl, cr, c) ->
  Obj.magic f __ lvl pk e cl cr c

(** val semi_deque_seq_graph_correct :
    nat -> 'a1 semi_deque -> 'a1 semi_deque_seq_graph **)

let semi_deque_seq_graph_correct _ = function
| Semi (lvl, pk, e, cl, cr, c) ->
  Coq_semi_deque_seq_graph_equation_1 (lvl, pk, e, cl, cr, c)

(** val semi_deque_seq_elim :
    (__ -> nat -> kind -> ending -> color -> color -> __ chain -> 'a1) -> nat
    -> 'a2 semi_deque -> 'a1 **)

let semi_deque_seq_elim f lvl s =
  let Coq_semi_deque_seq_graph_equation_1 (lvl0, pk, e, cl, cr, c) =
    semi_deque_seq_graph_correct lvl s
  in
  Obj.magic f __ lvl0 pk e cl cr c

(** val coq_FunctionalElimination_semi_deque_seq :
    (__ -> nat -> kind -> ending -> color -> color -> __ chain -> __) -> nat
    -> __ semi_deque -> __ **)

let coq_FunctionalElimination_semi_deque_seq =
  semi_deque_seq_elim

(** val coq_FunctionalInduction_semi_deque_seq :
    (__ -> nat -> __ semi_deque -> __ list) coq_FunctionalInduction **)

let coq_FunctionalInduction_semi_deque_seq =
  Obj.magic (fun _ -> semi_deque_seq_graph_correct)

(** val deque_seq : 'a1 deque -> 'a1 list **)

let deque_seq = function
| T (pk, e, c) ->
  chain_seq Datatypes.O pk Only e (Mix (SomeGreen, NoYellow, NoOrange,
    NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c

type 'a deque_seq_graph =
| Coq_deque_seq_graph_equation_1 of kind * ending * 'a chain

(** val deque_seq_graph_rect :
    (__ -> kind -> ending -> __ chain -> 'a1) -> 'a2 deque -> 'a2 list -> 'a2
    deque_seq_graph -> 'a1 **)

let deque_seq_graph_rect f _ _ = function
| Coq_deque_seq_graph_equation_1 (pk, e, c) -> Obj.magic f __ pk e c

(** val deque_seq_graph_correct : 'a1 deque -> 'a1 deque_seq_graph **)

let deque_seq_graph_correct = function
| T (pk, e, c) -> Coq_deque_seq_graph_equation_1 (pk, e, c)

(** val deque_seq_elim :
    (__ -> kind -> ending -> __ chain -> 'a1) -> 'a2 deque -> 'a1 **)

let deque_seq_elim f d =
  let Coq_deque_seq_graph_equation_1 (pk, e, c) = deque_seq_graph_correct d in
  Obj.magic f __ pk e c

(** val coq_FunctionalElimination_deque_seq :
    (__ -> kind -> ending -> __ chain -> __) -> __ deque -> __ **)

let coq_FunctionalElimination_deque_seq =
  deque_seq_elim

(** val coq_FunctionalInduction_deque_seq :
    (__ -> __ deque -> __ list) coq_FunctionalInduction **)

let coq_FunctionalInduction_deque_seq =
  Obj.magic (fun _ -> deque_seq_graph_correct)
