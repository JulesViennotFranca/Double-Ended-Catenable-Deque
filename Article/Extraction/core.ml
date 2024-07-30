open Datatypes
open EqDec
open Nat
open Buffer
open Types

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val push_left_storage_obligations_obligation_2 : nat -> nat **)

let push_left_storage_obligations_obligation_2 qs =
  qs

(** val push_left_storage_obligations_obligation_4 : nat -> nat **)

let push_left_storage_obligations_obligation_4 qs0 =
  qs0

(** val push_left_storage_obligations_obligation_6 : nat -> nat **)

let push_left_storage_obligations_obligation_6 qs2 =
  qs2

(** val push_left_storage_obligations_obligation_8 : nat -> nat **)

let push_left_storage_obligations_obligation_8 qs3 =
  qs3

(** val push_left_storage :
    nat -> ending -> color -> 'a1 stored_triple -> 'a1 storage -> 'a1 storage **)

let push_left_storage _ _ _ a1 = function
| Left_end (qp, p, s) ->
  Left_end ((S
    (let rec add0 n m =
       match n with
       | Datatypes.O -> m
       | S p0 -> S (add0 p0 m)
     in add0 Datatypes.O qp)),
    (push (add (S (S (S (S (S Datatypes.O))))) qp) a1 p), s)
| Left_st (_, _, _, c, p, s) ->
  (match c with
   | G (qp, qs) ->
     Left_st
       ((add (S (S (S Datatypes.O))) (S
          (let rec add0 n m =
             match n with
             | Datatypes.O -> m
             | S p0 -> S (add0 p0 m)
           in add0 Datatypes.O qp))),
       (add (S (S (S Datatypes.O)))
         (push_left_storage_obligations_obligation_2 qs)), (Mix (SomeGreen,
       NoYellow, NoOrange, NoRed)), (G ((S
       (let rec add0 n m =
          match n with
          | Datatypes.O -> m
          | S p0 -> S (add0 p0 m)
        in add0 Datatypes.O qp)),
       (push_left_storage_obligations_obligation_2 qs))),
       (push
         (add (S (S (S (S (S Datatypes.O)))))
           (add (S (S (S Datatypes.O))) qp)) a1 p), s)
   | Y (qp, qs) ->
     Left_st
       ((add (S (S Datatypes.O)) (S
          (let rec add0 n m =
             match n with
             | Datatypes.O -> m
             | S p0 -> S (add0 p0 m)
           in add0 Datatypes.O qp))),
       (add (S (S Datatypes.O))
         (push_left_storage_obligations_obligation_4 qs)), (Mix (NoGreen,
       SomeYellow, NoOrange, NoRed)), (Y ((S
       (let rec add0 n m =
          match n with
          | Datatypes.O -> m
          | S p0 -> S (add0 p0 m)
        in add0 Datatypes.O qp)),
       (push_left_storage_obligations_obligation_4 qs))),
       (push
         (add (S (S (S (S (S Datatypes.O))))) (add (S (S Datatypes.O)) qp))
         a1 p), s)
   | O (qp, qs) ->
     Left_st ((add (S Datatypes.O) (add (S Datatypes.O) qp)),
       (add (S Datatypes.O) (push_left_storage_obligations_obligation_6 qs)),
       (Mix (NoGreen, NoYellow, SomeOrange, NoRed)), (O
       ((add (S Datatypes.O) qp),
       (push_left_storage_obligations_obligation_6 qs))),
       (push (add (S (S (S (S (S Datatypes.O))))) (add (S Datatypes.O) qp))
         a1 p), s)
   | R (qp, qs) ->
     Left_st
       ((add Datatypes.O (S
          (let rec add0 n m =
             match n with
             | Datatypes.O -> m
             | S p0 -> S (add0 p0 m)
           in add0 Datatypes.O (add Datatypes.O qp)))),
       (add Datatypes.O (push_left_storage_obligations_obligation_8 qs)),
       (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (R ((S
       (let rec add0 n m =
          match n with
          | Datatypes.O -> m
          | S p0 -> S (add0 p0 m)
        in add0 Datatypes.O (add Datatypes.O qp))),
       (push_left_storage_obligations_obligation_8 qs))),
       (push (add (S (S (S (S (S Datatypes.O))))) (add Datatypes.O qp)) a1 p),
       s))
| _ -> assert false (* absurd case *)

(** val inject_right_storage_obligations_obligation_2 : nat -> nat **)

let inject_right_storage_obligations_obligation_2 qs =
  qs

(** val inject_right_storage_obligations_obligation_4 : nat -> nat **)

let inject_right_storage_obligations_obligation_4 qs0 =
  qs0

(** val inject_right_storage_obligations_obligation_6 : nat -> nat **)

let inject_right_storage_obligations_obligation_6 qs1 =
  qs1

(** val inject_right_storage_obligations_obligation_8 : nat -> nat **)

let inject_right_storage_obligations_obligation_8 qs3 =
  qs3

(** val inject_right_storage :
    nat -> ending -> color -> 'a1 storage -> 'a1 stored_triple -> 'a1 storage **)

let inject_right_storage _ _ _ st a1 =
  match st with
  | Right_end (qs, p, s) ->
    Right_end ((S
      (let rec add0 n m =
         match n with
         | Datatypes.O -> m
         | S p0 -> S (add0 p0 m)
       in add0 Datatypes.O qs)), p,
      (inject (add (S (S (S (S (S Datatypes.O))))) qs) s a1))
  | Right_st (_, _, _, c, p, s) ->
    (match c with
     | G (_, qs) ->
       Right_st
         ((add (S (S (S Datatypes.O)))
            (inject_right_storage_obligations_obligation_2 qs)),
         (add (S (S (S Datatypes.O))) (S
           (let rec add0 n m =
              match n with
              | Datatypes.O -> m
              | S p0 -> S (add0 p0 m)
            in add0 Datatypes.O qs))), (Mix (SomeGreen, NoYellow, NoOrange,
         NoRed)), (G ((inject_right_storage_obligations_obligation_2 qs), (S
         (let rec add0 n m =
            match n with
            | Datatypes.O -> m
            | S p0 -> S (add0 p0 m)
          in add0 Datatypes.O qs)))), p,
         (inject
           (add (S (S (S (S (S Datatypes.O)))))
             (add (S (S (S Datatypes.O))) qs)) s a1))
     | Y (_, qs) ->
       Right_st
         ((add (S (S Datatypes.O))
            (inject_right_storage_obligations_obligation_4 qs)),
         (add (S (S Datatypes.O)) (S
           (let rec add0 n m =
              match n with
              | Datatypes.O -> m
              | S p0 -> S (add0 p0 m)
            in add0 Datatypes.O qs))), (Mix (NoGreen, SomeYellow, NoOrange,
         NoRed)), (Y ((inject_right_storage_obligations_obligation_4 qs), (S
         (let rec add0 n m =
            match n with
            | Datatypes.O -> m
            | S p0 -> S (add0 p0 m)
          in add0 Datatypes.O qs)))), p,
         (inject
           (add (S (S (S (S (S Datatypes.O))))) (add (S (S Datatypes.O)) qs))
           s a1))
     | O (_, qs) ->
       Right_st
         ((add (S Datatypes.O)
            (inject_right_storage_obligations_obligation_6 qs)),
         (add (S Datatypes.O) (add (S Datatypes.O) qs)), (Mix (NoGreen,
         NoYellow, SomeOrange, NoRed)), (O
         ((inject_right_storage_obligations_obligation_6 qs),
         (add (S Datatypes.O) qs))), p,
         (inject
           (add (S (S (S (S (S Datatypes.O))))) (add (S Datatypes.O) qs)) s
           a1))
     | R (_, qs) ->
       Right_st
         ((add Datatypes.O (inject_right_storage_obligations_obligation_8 qs)),
         (add Datatypes.O (S
           (let rec add0 n m =
              match n with
              | Datatypes.O -> m
              | S p0 -> S (add0 p0 m)
            in add0 Datatypes.O (add Datatypes.O qs)))), (Mix (NoGreen,
         NoYellow, NoOrange, SomeRed)), (R
         ((inject_right_storage_obligations_obligation_8 qs), (S
         (let rec add0 n m =
            match n with
            | Datatypes.O -> m
            | S p0 -> S (add0 p0 m)
          in add0 Datatypes.O (add Datatypes.O qs))))), p,
         (inject (add (S (S (S (S (S Datatypes.O))))) (add Datatypes.O qs)) s
           a1)))
  | _ -> assert false (* absurd case *)

(** val push_only_storage :
    nat -> ending -> color -> 'a1 stored_triple -> 'a1 storage -> 'a1 storage **)

let push_only_storage _ _ _ a1 = function
| Only_end (q, p) -> Only_end ((S q), (push (S q) a1 p))
| Only_st (_, _, _, c, p, s) ->
  (match c with
   | G (qp, qs) ->
     Only_st
       ((add (S (S (S Datatypes.O))) (S
          (let rec add0 n m =
             match n with
             | Datatypes.O -> m
             | S p0 -> S (add0 p0 m)
           in add0 Datatypes.O qp))), (add (S (S (S Datatypes.O))) qs), (Mix
       (SomeGreen, NoYellow, NoOrange, NoRed)), (G ((S
       (let rec add0 n m =
          match n with
          | Datatypes.O -> m
          | S p0 -> S (add0 p0 m)
        in add0 Datatypes.O qp)), qs)),
       (push
         (add (S (S (S (S (S Datatypes.O)))))
           (add (S (S (S Datatypes.O))) qp)) a1 p), s)
   | Y (qp, qs) ->
     Only_st
       ((add (S (S Datatypes.O)) (S
          (let rec add0 n m =
             match n with
             | Datatypes.O -> m
             | S p0 -> S (add0 p0 m)
           in add0 Datatypes.O qp))), (add (S (S Datatypes.O)) qs), (Mix
       (NoGreen, SomeYellow, NoOrange, NoRed)), (Y ((S
       (let rec add0 n m =
          match n with
          | Datatypes.O -> m
          | S p0 -> S (add0 p0 m)
        in add0 Datatypes.O qp)), qs)),
       (push
         (add (S (S (S (S (S Datatypes.O))))) (add (S (S Datatypes.O)) qp))
         a1 p), s)
   | O (qp, qs) ->
     Only_st ((add (S Datatypes.O) (add (S Datatypes.O) qp)),
       (add (S Datatypes.O) qs), (Mix (NoGreen, NoYellow, SomeOrange,
       NoRed)), (O ((add (S Datatypes.O) qp), qs)),
       (push (add (S (S (S (S (S Datatypes.O))))) (add (S Datatypes.O) qp))
         a1 p), s)
   | R (qp, qs) ->
     Only_st
       ((add Datatypes.O (S
          (let rec add0 n m =
             match n with
             | Datatypes.O -> m
             | S p0 -> S (add0 p0 m)
           in add0 Datatypes.O (add Datatypes.O qp)))), (add Datatypes.O qs),
       (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (R ((S
       (let rec add0 n m =
          match n with
          | Datatypes.O -> m
          | S p0 -> S (add0 p0 m)
        in add0 Datatypes.O (add Datatypes.O qp))), qs)),
       (push (add (S (S (S (S (S Datatypes.O))))) (add Datatypes.O qp)) a1 p),
       s))
| _ -> assert false (* absurd case *)

(** val inject_only_storage :
    nat -> ending -> color -> 'a1 storage -> 'a1 stored_triple -> 'a1 storage **)

let inject_only_storage _ _ _ st a1 =
  match st with
  | Only_end (q, p) -> Only_end ((S q), (inject (S q) p a1))
  | Only_st (_, _, _, c, p, s) ->
    (match c with
     | G (qp, qs) ->
       Only_st ((add (S (S (S Datatypes.O))) qp),
         (add (S (S (S Datatypes.O))) (S
           (let rec add0 n m =
              match n with
              | Datatypes.O -> m
              | S p0 -> S (add0 p0 m)
            in add0 Datatypes.O qs))), (Mix (SomeGreen, NoYellow, NoOrange,
         NoRed)), (G (qp, (S
         (let rec add0 n m =
            match n with
            | Datatypes.O -> m
            | S p0 -> S (add0 p0 m)
          in add0 Datatypes.O qs)))), p,
         (inject
           (add (S (S (S (S (S Datatypes.O)))))
             (add (S (S (S Datatypes.O))) qs)) s a1))
     | Y (qp, qs) ->
       Only_st ((add (S (S Datatypes.O)) qp),
         (add (S (S Datatypes.O)) (S
           (let rec add0 n m =
              match n with
              | Datatypes.O -> m
              | S p0 -> S (add0 p0 m)
            in add0 Datatypes.O qs))), (Mix (NoGreen, SomeYellow, NoOrange,
         NoRed)), (Y (qp, (S
         (let rec add0 n m =
            match n with
            | Datatypes.O -> m
            | S p0 -> S (add0 p0 m)
          in add0 Datatypes.O qs)))), p,
         (inject
           (add (S (S (S (S (S Datatypes.O))))) (add (S (S Datatypes.O)) qs))
           s a1))
     | O (qp, qs) ->
       Only_st ((add (S Datatypes.O) qp),
         (add (S Datatypes.O) (add (S Datatypes.O) qs)), (Mix (NoGreen,
         NoYellow, SomeOrange, NoRed)), (O (qp, (add (S Datatypes.O) qs))),
         p,
         (inject
           (add (S (S (S (S (S Datatypes.O))))) (add (S Datatypes.O) qs)) s
           a1))
     | R (qp, qs) ->
       Only_st ((add Datatypes.O qp),
         (add Datatypes.O (S
           (let rec add0 n m =
              match n with
              | Datatypes.O -> m
              | S p0 -> S (add0 p0 m)
            in add0 Datatypes.O (add Datatypes.O qs)))), (Mix (NoGreen,
         NoYellow, NoOrange, SomeRed)), (R (qp, (S
         (let rec add0 n m =
            match n with
            | Datatypes.O -> m
            | S p0 -> S (add0 p0 m)
          in add0 Datatypes.O (add Datatypes.O qs))))), p,
         (inject (add (S (S (S (S (S Datatypes.O))))) (add Datatypes.O qs)) s
           a1)))
  | _ -> assert false (* absurd case *)

(** val push_left_packet :
    nat -> nat -> ending -> color -> 'a1 stored_triple -> 'a1 packet -> 'a1
    packet **)

let push_left_packet _ _ _ _ a1 = function
| Packet (_, _, _, _, e, g, r, b, s) ->
  (match b with
   | Hole (lvl, _) ->
     Packet (lvl, lvl, Left, Left, e, g, r, (Hole (lvl, Left)),
       (push_left_storage lvl e (Mix (g, NoYellow, NoOrange, r)) a1 s))
   | Only_yellow (hlvl, tlvl, _, tk, s0, b0) ->
     Packet (hlvl, tlvl, Left, tk, e, g, r, (Only_yellow (hlvl, tlvl, Left,
       tk,
       (push_left_storage hlvl Not_end (Mix (NoGreen, SomeYellow, NoOrange,
         NoRed)) a1 s0), b0)), s)
   | Only_orange (hlvl, tlvl, _, tk, s0, b0) ->
     Packet (hlvl, tlvl, Left, tk, e, g, r, (Only_orange (hlvl, tlvl, Left,
       tk,
       (push_left_storage hlvl Not_end (Mix (NoGreen, NoYellow, SomeOrange,
         NoRed)) a1 s0), b0)), s)
   | Pair_yellow (hlvl, tlvl, _, tk, c, s0, b0, c0) ->
     Packet (hlvl, tlvl, Left, tk, e, g, r, (Pair_yellow (hlvl, tlvl, Left,
       tk, c,
       (push_left_storage hlvl Not_end (Mix (NoGreen, SomeYellow, NoOrange,
         NoRed)) a1 s0), b0, c0)), s)
   | Pair_orange (hlvl, tlvl, _, tk, s0, c, b0) ->
     Packet (hlvl, tlvl, Left, tk, e, g, r, (Pair_orange (hlvl, tlvl, Left,
       tk,
       (push_left_storage hlvl Not_end (Mix (NoGreen, NoYellow, SomeOrange,
         NoRed)) a1 s0), c, b0)), s))

(** val inject_right_packet :
    nat -> nat -> ending -> color -> 'a1 packet -> 'a1 stored_triple -> 'a1
    packet **)

let inject_right_packet _ _ _ _ pkt a1 =
  let Packet (_, _, _, _, e, g, r, b, s) = pkt in
  (match b with
   | Hole (lvl, _) ->
     Packet (lvl, lvl, Right, Right, e, g, r, (Hole (lvl, Right)),
       (inject_right_storage lvl e (Mix (g, NoYellow, NoOrange, r)) s a1))
   | Only_yellow (hlvl, tlvl, _, tk, s0, b0) ->
     Packet (hlvl, tlvl, Right, tk, e, g, r, (Only_yellow (hlvl, tlvl, Right,
       tk,
       (inject_right_storage hlvl Not_end (Mix (NoGreen, SomeYellow,
         NoOrange, NoRed)) s0 a1), b0)), s)
   | Only_orange (hlvl, tlvl, _, tk, s0, b0) ->
     Packet (hlvl, tlvl, Right, tk, e, g, r, (Only_orange (hlvl, tlvl, Right,
       tk,
       (inject_right_storage hlvl Not_end (Mix (NoGreen, NoYellow,
         SomeOrange, NoRed)) s0 a1), b0)), s)
   | Pair_yellow (hlvl, tlvl, _, tk, c, s0, b0, c0) ->
     Packet (hlvl, tlvl, Right, tk, e, g, r, (Pair_yellow (hlvl, tlvl, Right,
       tk, c,
       (inject_right_storage hlvl Not_end (Mix (NoGreen, SomeYellow,
         NoOrange, NoRed)) s0 a1), b0, c0)), s)
   | Pair_orange (hlvl, tlvl, _, tk, s0, c, b0) ->
     Packet (hlvl, tlvl, Right, tk, e, g, r, (Pair_orange (hlvl, tlvl, Right,
       tk,
       (inject_right_storage hlvl Not_end (Mix (NoGreen, NoYellow,
         SomeOrange, NoRed)) s0 a1), c, b0)), s))

(** val push_only_packet :
    nat -> nat -> ending -> color -> 'a1 stored_triple -> 'a1 packet -> 'a1
    packet **)

let push_only_packet _ _ _ _ a1 = function
| Packet (_, _, _, _, e, g, r, b, s) ->
  (match b with
   | Hole (lvl, _) ->
     Packet (lvl, lvl, Only, Only, e, g, r, (Hole (lvl, Only)),
       (push_only_storage lvl e (Mix (g, NoYellow, NoOrange, r)) a1 s))
   | Only_yellow (hlvl, tlvl, _, tk, s0, b0) ->
     Packet (hlvl, tlvl, Only, tk, e, g, r, (Only_yellow (hlvl, tlvl, Only,
       tk,
       (push_only_storage hlvl Not_end (Mix (NoGreen, SomeYellow, NoOrange,
         NoRed)) a1 s0), b0)), s)
   | Only_orange (hlvl, tlvl, _, tk, s0, b0) ->
     Packet (hlvl, tlvl, Only, tk, e, g, r, (Only_orange (hlvl, tlvl, Only,
       tk,
       (push_only_storage hlvl Not_end (Mix (NoGreen, NoYellow, SomeOrange,
         NoRed)) a1 s0), b0)), s)
   | Pair_yellow (hlvl, tlvl, _, tk, c, s0, b0, c0) ->
     Packet (hlvl, tlvl, Only, tk, e, g, r, (Pair_yellow (hlvl, tlvl, Only,
       tk, c,
       (push_only_storage hlvl Not_end (Mix (NoGreen, SomeYellow, NoOrange,
         NoRed)) a1 s0), b0, c0)), s)
   | Pair_orange (hlvl, tlvl, _, tk, s0, c, b0) ->
     Packet (hlvl, tlvl, Only, tk, e, g, r, (Pair_orange (hlvl, tlvl, Only,
       tk,
       (push_only_storage hlvl Not_end (Mix (NoGreen, NoYellow, SomeOrange,
         NoRed)) a1 s0), c, b0)), s))

(** val inject_only_packet :
    nat -> nat -> ending -> color -> 'a1 packet -> 'a1 stored_triple -> 'a1
    packet **)

let inject_only_packet _ _ _ _ pkt a1 =
  let Packet (_, _, _, _, e, g, r, b, s) = pkt in
  (match b with
   | Hole (lvl, _) ->
     Packet (lvl, lvl, Only, Only, e, g, r, (Hole (lvl, Only)),
       (inject_only_storage lvl e (Mix (g, NoYellow, NoOrange, r)) s a1))
   | Only_yellow (hlvl, tlvl, _, tk, s0, b0) ->
     Packet (hlvl, tlvl, Only, tk, e, g, r, (Only_yellow (hlvl, tlvl, Only,
       tk,
       (inject_only_storage hlvl Not_end (Mix (NoGreen, SomeYellow, NoOrange,
         NoRed)) s0 a1), b0)), s)
   | Only_orange (hlvl, tlvl, _, tk, s0, b0) ->
     Packet (hlvl, tlvl, Only, tk, e, g, r, (Only_orange (hlvl, tlvl, Only,
       tk,
       (inject_only_storage hlvl Not_end (Mix (NoGreen, NoYellow, SomeOrange,
         NoRed)) s0 a1), b0)), s)
   | Pair_yellow (hlvl, tlvl, _, tk, c, s0, b0, c0) ->
     Packet (hlvl, tlvl, Only, tk, e, g, r, (Pair_yellow (hlvl, tlvl, Only,
       tk, c,
       (inject_only_storage hlvl Not_end (Mix (NoGreen, SomeYellow, NoOrange,
         NoRed)) s0 a1), b0, c0)), s)
   | Pair_orange (hlvl, tlvl, _, tk, s0, c, b0) ->
     Packet (hlvl, tlvl, Only, tk, e, g, r, (Pair_orange (hlvl, tlvl, Only,
       tk,
       (inject_only_storage hlvl Not_end (Mix (NoGreen, NoYellow, SomeOrange,
         NoRed)) s0 a1), c, b0)), s))

(** val single_storage : nat -> 'a1 stored_triple -> 'a1 storage **)

let single_storage _ a1 =
  Only_end (Datatypes.O, (single a1))

(** val single_packet : nat -> 'a1 stored_triple -> 'a1 packet **)

let single_packet lvl a1 =
  Packet (lvl, lvl, Only, Only, Is_end, SomeGreen, NoRed, (Hole (lvl, Only)),
    (single_storage lvl a1))

(** val single_chain : nat -> 'a1 stored_triple -> 'a1 chain **)

let single_chain lvl a1 =
  Only_chain (lvl, lvl, Only, Only, Is_end, (Mix (SomeGreen, NoYellow,
    NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
    (SomeGreen, NoYellow, NoOrange, NoRed)), (Green_chain ((Mix (SomeGreen,
    NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
    NoRed)))), (single_packet lvl a1), (Empty (S lvl)))

(** val push_left_chain :
    nat -> color -> 'a1 stored_triple -> 'a1 chain -> 'a1 chain **)

let push_left_chain _ _ a1 = function
| Only_chain (hlvl, tlvl, _, pk, e, c0, cl, cr, c1, p, c2) ->
  coq_UIP_K c0 (fun _ -> Only_chain (hlvl, tlvl, Left, pk, e, c0, cl, cr, c1,
    (push_left_packet hlvl tlvl e c0 a1 p), c2)) __
| _ -> assert false (* absurd case *)

(** val inject_right_chain :
    nat -> color -> 'a1 chain -> 'a1 stored_triple -> 'a1 chain **)

let inject_right_chain _ _ c a1 =
  match c with
  | Only_chain (hlvl, tlvl, _, pk, e, c0, cl, cr, c1, p, c2) ->
    coq_UIP_K c0 (fun _ -> Only_chain (hlvl, tlvl, Right, pk, e, c0, cl, cr,
      c1, (inject_right_packet hlvl tlvl e c0 p a1), c2)) __
  | _ -> assert false (* absurd case *)

(** val push_chain :
    nat -> kind -> ending -> color -> color -> 'a1 stored_triple -> 'a1 chain
    -> 'a1 chain **)

let push_chain _ _ _ _ _ a1 = function
| Empty lvl -> single_chain lvl a1
| Only_chain (hlvl, tlvl, _, pk, e, c0, cl, cr, c1, p, c2) ->
  Only_chain (hlvl, tlvl, Only, pk, e, c0, cl, cr, c1,
    (push_only_packet hlvl tlvl e c0 a1 p), c2)
| Pair_chain (lvl, cl, cr, c0, c1) ->
  Pair_chain (lvl, cl, cr, (push_left_chain lvl cl a1 c0), c1)

(** val inject_chain :
    nat -> kind -> ending -> color -> color -> 'a1 chain -> 'a1 stored_triple
    -> 'a1 chain **)

let inject_chain _ _ _ _ _ c a1 =
  match c with
  | Empty lvl -> single_chain lvl a1
  | Only_chain (hlvl, tlvl, _, pk, e, c0, cl, cr, c1, p, c2) ->
    Only_chain (hlvl, tlvl, Only, pk, e, c0, cl, cr, c1,
      (inject_only_packet hlvl tlvl e c0 p a1), c2)
  | Pair_chain (lvl, cl, cr, c0, c1) ->
    Pair_chain (lvl, cl, cr, c0, (inject_right_chain lvl cr c1 a1))

(** val push_ne_chain :
    nat -> kind -> color -> color -> 'a1 stored_triple -> 'a1
    non_ending_chain -> 'a1 non_ending_chain **)

let push_ne_chain _ _ _ _ a1 = function
| NE_chain (lvl, pk, _, e, cl, cr, c0) ->
  NE_chain (lvl, pk, Only, Not_end, cl, cr, (push_chain lvl pk e cl cr a1 c0))

(** val inject_ne_chain :
    nat -> kind -> color -> color -> 'a1 non_ending_chain -> 'a1
    stored_triple -> 'a1 non_ending_chain **)

let inject_ne_chain _ _ _ _ c a1 =
  let NE_chain (lvl, pk, _, e, cl, cr, c0) = c in
  NE_chain (lvl, pk, Only, Not_end, cl, cr,
  (inject_chain lvl pk e cl cr c0 a1))

(** val push_vector :
    nat -> nat -> kind -> color -> color -> 'a1 stored_triple vector -> 'a1
    non_ending_chain -> 'a1 non_ending_chain **)

let push_vector lvl _ pk cl cr v c =
  match v with
  | V0 _ -> c
  | V1 (_, s) -> push_ne_chain lvl pk cl cr s c
  | V2 (_, s, s0) ->
    push_ne_chain lvl pk cl cr s (push_ne_chain lvl pk cl cr s0 c)
  | V3 (_, s, s0, s1) ->
    push_ne_chain lvl pk cl cr s
      (push_ne_chain lvl pk cl cr s0 (push_ne_chain lvl pk cl cr s1 c))
  | V4 (_, s, s0, s1, s2) ->
    push_ne_chain lvl pk cl cr s
      (push_ne_chain lvl pk cl cr s0
        (push_ne_chain lvl pk cl cr s1 (push_ne_chain lvl pk cl cr s2 c)))
  | V5 (_, s, s0, s1, s2, s3) ->
    push_ne_chain lvl pk cl cr s
      (push_ne_chain lvl pk cl cr s0
        (push_ne_chain lvl pk cl cr s1
          (push_ne_chain lvl pk cl cr s2 (push_ne_chain lvl pk cl cr s3 c))))
  | V6 (_, s, s0, s1, s2, s3, s4) ->
    push_ne_chain lvl pk cl cr s
      (push_ne_chain lvl pk cl cr s0
        (push_ne_chain lvl pk cl cr s1
          (push_ne_chain lvl pk cl cr s2
            (push_ne_chain lvl pk cl cr s3 (push_ne_chain lvl pk cl cr s4 c)))))

(** val inject_vector :
    nat -> nat -> kind -> color -> color -> 'a1 non_ending_chain -> 'a1
    stored_triple vector -> 'a1 non_ending_chain **)

let inject_vector lvl _ pk cl cr c = function
| V0 _ -> c
| V1 (_, s) -> inject_ne_chain lvl pk cl cr c s
| V2 (_, s, s0) ->
  inject_ne_chain lvl pk cl cr (inject_ne_chain lvl pk cl cr c s) s0
| V3 (_, s, s0, s1) ->
  inject_ne_chain lvl pk cl cr
    (inject_ne_chain lvl pk cl cr (inject_ne_chain lvl pk cl cr c s) s0) s1
| V4 (_, s, s0, s1, s2) ->
  inject_ne_chain lvl pk cl cr
    (inject_ne_chain lvl pk cl cr
      (inject_ne_chain lvl pk cl cr (inject_ne_chain lvl pk cl cr c s) s0) s1)
    s2
| V5 (_, s, s0, s1, s2, s3) ->
  inject_ne_chain lvl pk cl cr
    (inject_ne_chain lvl pk cl cr
      (inject_ne_chain lvl pk cl cr
        (inject_ne_chain lvl pk cl cr (inject_ne_chain lvl pk cl cr c s) s0)
        s1) s2) s3
| V6 (_, s, s0, s1, s2, s3, s4) ->
  inject_ne_chain lvl pk cl cr
    (inject_ne_chain lvl pk cl cr
      (inject_ne_chain lvl pk cl cr
        (inject_ne_chain lvl pk cl cr
          (inject_ne_chain lvl pk cl cr (inject_ne_chain lvl pk cl cr c s) s0)
          s1) s2) s3) s4

(** val push_semi :
    nat -> 'a1 stored_triple -> 'a1 semi_deque -> 'a1 semi_deque **)

let push_semi _ a1 = function
| Semi (lvl, pk, e, cl, cr, c) ->
  Semi (lvl, pk, Not_end, cl, cr, (push_chain lvl pk e cl cr a1 c))

(** val inject_semi :
    nat -> 'a1 semi_deque -> 'a1 stored_triple -> 'a1 semi_deque **)

let inject_semi _ sd a1 =
  let Semi (lvl, pk, e, cl, cr, c) = sd in
  Semi (lvl, pk, Not_end, cl, cr, (inject_chain lvl pk e cl cr c a1))

(** val triple_of_chain : nat -> kind -> color -> 'a1 chain -> 'a1 triple **)

let triple_of_chain _ _ _ = function
| Only_chain (_, _, _, pk, _, c0, _, _, c1, p, c2) ->
  coq_UIP_K c0 (fun _ ->
    match c1 with
    | Green_chain (cl, cr) ->
      let Packet (_, _, _, _, e, _, _, b, s) = p in
      (match b with
       | Hole (lvl, k) ->
         Triple (lvl, pk, k, e, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
           cl, cr, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Green (pk,
           e, cl, cr)), s, c2)
       | Only_yellow (hlvl, tlvl, hk, tk, s0, b0) ->
         Triple (hlvl, Only, hk, Not_end, (Mix (NoGreen, SomeYellow,
           NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
           (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Yellow (Only, (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)))), s0, (Only_chain ((S hlvl), tlvl, Only, pk, e, (Mix
           (SomeGreen, NoYellow, NoOrange, NoRed)), cl, cr, (Green_chain (cl,
           cr)), (Packet ((S hlvl), tlvl, Only, tk, e, SomeGreen, NoRed, b0,
           s)), c2)))
       | Only_orange (hlvl, tlvl, hk, tk, s0, b0) ->
         Triple (hlvl, Only, hk, Not_end, (Mix (NoGreen, NoYellow,
           SomeOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
           (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (OrangeO (Mix (SomeGreen, NoYellow,
           NoOrange, NoRed))), s0, (Only_chain ((S hlvl), tlvl, Only, pk, e,
           (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), cl, cr, (Green_chain
           (cl, cr)), (Packet ((S hlvl), tlvl, Only, tk, e, SomeGreen, NoRed,
           b0, s)), c2)))
       | Pair_yellow (hlvl, tlvl, hk, tk, c3, s0, b0, c4) ->
         Triple (hlvl, Pair, hk, Not_end, (Mix (NoGreen, SomeYellow,
           NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
           c3, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Yellow (Pair,
           (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), c3)), s0,
           (Pair_chain ((S hlvl), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), c3, (Only_chain ((S hlvl), tlvl, Left, pk, e, (Mix
           (SomeGreen, NoYellow, NoOrange, NoRed)), cl, cr, (Green_chain (cl,
           cr)), (Packet ((S hlvl), tlvl, Left, tk, e, SomeGreen, NoRed, b0,
           s)), c2)), c4)))
       | Pair_orange (hlvl, tlvl, hk, tk, s0, c3, b0) ->
         Triple (hlvl, Pair, hk, Not_end, (Mix (NoGreen, NoYellow,
           SomeOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
           (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (OrangeP (Mix (SomeGreen, NoYellow,
           NoOrange, NoRed))), s0, (Pair_chain ((S hlvl), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), c3, (Only_chain ((S hlvl), tlvl, Right, pk, e, (Mix
           (SomeGreen, NoYellow, NoOrange, NoRed)), cl, cr, (Green_chain (cl,
           cr)), (Packet ((S hlvl), tlvl, Right, tk, e, SomeGreen, NoRed, b0,
           s)), c2))))))
    | Red_chain ->
      let Packet (_, _, _, _, e, _, _, b, s) = p in
      (match b with
       | Hole (lvl, k) ->
         Triple (lvl, pk, k, e, (Mix (NoGreen, NoYellow, NoOrange, SomeRed)),
           (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (NoGreen, NoYellow, NoOrange,
           SomeRed)), (Red (pk, e)), s, c2)
       | Only_yellow (hlvl, tlvl, hk, tk, s0, b0) ->
         Triple (hlvl, Only, hk, Not_end, (Mix (NoGreen, SomeYellow,
           NoOrange, NoRed)), (Mix (NoGreen, NoYellow, NoOrange, SomeRed)),
           (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (NoGreen,
           NoYellow, NoOrange, SomeRed)), (Yellow (Only, (Mix (NoGreen,
           NoYellow, NoOrange, SomeRed)), (Mix (NoGreen, NoYellow, NoOrange,
           SomeRed)))), s0, (Only_chain ((S hlvl), tlvl, Only, pk, e, (Mix
           (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), Red_chain, (Packet ((S hlvl), tlvl, Only, tk, e, NoGreen,
           SomeRed, b0, s)), c2)))
       | Only_orange (hlvl, tlvl, hk, tk, s0, b0) ->
         Triple (hlvl, Only, hk, Not_end, (Mix (NoGreen, NoYellow,
           SomeOrange, NoRed)), (Mix (NoGreen, NoYellow, NoOrange, SomeRed)),
           (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (NoGreen,
           NoYellow, NoOrange, SomeRed)), (OrangeO (Mix (NoGreen, NoYellow,
           NoOrange, SomeRed))), s0, (Only_chain ((S hlvl), tlvl, Only, pk,
           e, (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), Red_chain, (Packet ((S hlvl), tlvl, Only, tk, e, NoGreen,
           SomeRed, b0, s)), c2)))
       | Pair_yellow (hlvl, tlvl, hk, tk, c3, s0, b0, c4) ->
         Triple (hlvl, Pair, hk, Not_end, (Mix (NoGreen, SomeYellow,
           NoOrange, NoRed)), (Mix (NoGreen, NoYellow, NoOrange, SomeRed)),
           c3, (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Yellow (Pair,
           (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), c3)), s0,
           (Pair_chain ((S hlvl), (Mix (NoGreen, NoYellow, NoOrange,
           SomeRed)), c3, (Only_chain ((S hlvl), tlvl, Left, pk, e, (Mix
           (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), Red_chain, (Packet ((S hlvl), tlvl, Left, tk, e, NoGreen,
           SomeRed, b0, s)), c2)), c4)))
       | Pair_orange (hlvl, tlvl, hk, tk, s0, c3, b0) ->
         Triple (hlvl, Pair, hk, Not_end, (Mix (NoGreen, NoYellow,
           SomeOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
           (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (NoGreen,
           NoYellow, NoOrange, SomeRed)), (OrangeP (Mix (NoGreen, NoYellow,
           NoOrange, SomeRed))), s0, (Pair_chain ((S hlvl), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (NoGreen, NoYellow, NoOrange,
           SomeRed)), c3, (Only_chain ((S hlvl), tlvl, Right, pk, e, (Mix
           (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), Red_chain, (Packet ((S hlvl), tlvl, Right, tk, e,
           NoGreen, SomeRed, b0, s)), c2))))))) __
| _ -> assert false (* absurd case *)

(** val chain_of_triple : nat -> kind -> color -> 'a1 triple -> 'a1 chain **)

let chain_of_triple _ _ _ = function
| Triple (lvl, _, k, _, _, _, _, _, r, s, c) ->
  (match r with
   | Green (pk, e, cl, cr) ->
     Only_chain (lvl, lvl, k, pk, e, (Mix (SomeGreen, NoYellow, NoOrange,
       NoRed)), cl, cr, (Green_chain (cl, cr)), (Packet (lvl, lvl, k, k, e,
       SomeGreen, NoRed, (Hole (lvl, k)), s)), c)
   | Yellow (_, _, _) ->
     (match c with
      | Empty _ -> assert false (* absurd case *)
      | Only_chain (_, _, _, pk, _, _, cl, cr, c0, p, c1) ->
        let Packet (_, tlvl, _, tk, e, g, r0, b, s0) = p in
        Only_chain (lvl, tlvl, k, pk, e, (Mix (g, NoYellow, NoOrange, r0)),
        cl, cr, c0, (Packet (lvl, tlvl, k, tk, e, g, r0, (Only_yellow (lvl,
        tlvl, k, tk, s, b)), s0)), c1)
      | Pair_chain (_, _, cr, c0, c1) ->
        (match c0 with
         | Only_chain (_, _, _, pk, _, c2, cl, cr0, c3, p, c4) ->
           coq_UIP_K c2 (fun _ ->
             let Packet (_, tlvl, _, tk, e, g, r0, b, s0) = p in
             Only_chain (lvl, tlvl, k, pk, e, (Mix (g, NoYellow, NoOrange,
             r0)), cl, cr0, c3, (Packet (lvl, tlvl, k, tk, e, g, r0,
             (Pair_yellow (lvl, tlvl, k, tk, cr, s, b, c1)), s0)), c4)) __
         | _ -> assert false (* absurd case *)))
   | OrangeO _ ->
     (match c with
      | Only_chain (_, _, _, pk, _, c0, cl, cr, c1, p, c2) ->
        coq_UIP_K c0 (fun _ ->
          let Packet (_, tlvl, _, tk, e, g, r0, b, s0) = p in
          Only_chain (lvl, tlvl, k, pk, e, (Mix (g, NoYellow, NoOrange, r0)),
          cl, cr, c1, (Packet (lvl, tlvl, k, tk, e, g, r0, (Only_orange (lvl,
          tlvl, k, tk, s, b)), s0)), c2)) __
      | _ -> assert false (* absurd case *))
   | OrangeP _ ->
     (match c with
      | Pair_chain (_, _, _, c0, c1) ->
        (match c1 with
         | Only_chain (_, _, _, pk, _, c2, cl, cr, c3, p, c4) ->
           coq_UIP_K c2 (fun _ ->
             let Packet (_, tlvl, _, tk, e, g, r0, b, s0) = p in
             Only_chain (lvl, tlvl, k, pk, e, (Mix (g, NoYellow, NoOrange,
             r0)), cl, cr, c3, (Packet (lvl, tlvl, k, tk, e, g, r0,
             (Pair_orange (lvl, tlvl, k, tk, s, c0, b)), s0)), c4)) __
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Red (pk, e) ->
     Only_chain (lvl, lvl, k, pk, e, (Mix (NoGreen, NoYellow, NoOrange,
       SomeRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
       (SomeGreen, NoYellow, NoOrange, NoRed)), Red_chain, (Packet (lvl, lvl,
       k, k, e, NoGreen, SomeRed, (Hole (lvl, k)), s)), c))

(** val left_of_only : nat -> color -> 'a1 triple -> 'a1 left_right_triple **)

let left_of_only _ _ = function
| Triple (lvl, _, _, _, _, _, _, _, r, s, c) ->
  (match r with
   | Green (pk, _, cl, cr) ->
     (match s with
      | Only_end (q, p) ->
        (match c with
         | Empty _ ->
           (match has7 q p with
            | Coq_inl v -> Not_enough (lvl, Left, v)
            | Coq_inr p0 ->
              let Coq_pair (p1, s0) =
                eject2 (S
                  (let rec add0 n m =
                     match n with
                     | Datatypes.O -> m
                     | S p1 -> S (add0 p1 m)
                   in add0 (S (S (S (S Datatypes.O))))
                        (PeanoNat.Nat.iter (S (S (S (S (S (S (S
                          Datatypes.O))))))) PeanoNat.Nat.pred (S q)))) p0
              in
              let Coq_pair (t0, s1) = p1 in
              Ok_lrt (lvl, Left, (Mix (SomeGreen, NoYellow, NoOrange,
              NoRed)), (Triple (lvl, Only, Left, Is_end, (Mix (SomeGreen,
              NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
              NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
              NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Green
              (Only, Is_end, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
              (Mix (SomeGreen, NoYellow, NoOrange, NoRed)))), (Left_end
              ((PeanoNat.Nat.iter (S (S (S (S (S (S (S Datatypes.O)))))))
                 PeanoNat.Nat.pred (S q)), t0, (pair s1 s0))), (Empty (S
              lvl))))))
         | _ -> assert false (* absurd case *))
      | Only_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (p0, s1) =
          eject2 (S
            (let rec add0 n m =
               match n with
               | Datatypes.O -> m
               | S p0 -> S (add0 p0 m)
             in add0 (S (S Datatypes.O)) qs)) s0
        in
        let Coq_pair (t0, s2) = p0 in
        Ok_lrt (lvl, Left, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
        (Triple (lvl, pk, Left, Not_end, (Mix (SomeGreen, NoYellow, NoOrange,
        NoRed)), cl, cr, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Green
        (pk, Not_end, cl, cr)), (Left_st (qp, qs, (Mix (SomeGreen, NoYellow,
        NoOrange, NoRed)), c0, p, (pair s2 s1))),
        (inject_chain (S lvl) pk Not_end cl cr c (Small (lvl, qs, t0))))))
      | _ -> assert false (* absurd case *))
   | Yellow (pk, cl, cr) ->
     (match s with
      | Only_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (p0, s1) =
          eject2 (S
            (let rec add0 n m =
               match n with
               | Datatypes.O -> m
               | S p0 -> S (add0 p0 m)
             in add0 (S (S Datatypes.O)) qs)) s0
        in
        let Coq_pair (t0, s2) = p0 in
        Ok_lrt (lvl, Left, cl, (Triple (lvl, pk, Left, Not_end, (Mix
        (NoGreen, SomeYellow, NoOrange, NoRed)), cl, cr, cl, (Yellow (pk, cl,
        cr)), (Left_st (qp, qs, (Mix (NoGreen, SomeYellow, NoOrange, NoRed)),
        c0, p, (pair s2 s1))),
        (inject_chain (S lvl) pk Not_end cl cr c (Small (lvl, qs, t0))))))
      | _ -> assert false (* absurd case *))
   | OrangeO c0 ->
     (match s with
      | Only_st (qp, qs, _, c1, p, s0) ->
        let Coq_pair (p0, s1) =
          eject2 (S
            (let rec add0 n m =
               match n with
               | Datatypes.O -> m
               | S p0 -> S (add0 p0 m)
             in add0 (S (S Datatypes.O)) qs)) s0
        in
        let Coq_pair (t0, s2) = p0 in
        Ok_lrt (lvl, Left, c0, (Triple (lvl, Only, Left, Not_end, (Mix
        (NoGreen, NoYellow, SomeOrange, NoRed)), c0, c0, c0, (OrangeO c0),
        (Left_st (qp, qs, (Mix (NoGreen, NoYellow, SomeOrange, NoRed)), c1,
        p, (pair s2 s1))),
        (inject_chain (S lvl) Only Not_end c0 c0 c (Small (lvl, qs, t0))))))
      | _ -> assert false (* absurd case *))
   | OrangeP cr ->
     (match s with
      | Only_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (p0, s1) =
          eject2 (S
            (let rec add0 n m =
               match n with
               | Datatypes.O -> m
               | S p0 -> S (add0 p0 m)
             in add0 (S (S Datatypes.O)) qs)) s0
        in
        let Coq_pair (t0, s2) = p0 in
        Ok_lrt (lvl, Left, cr, (Triple (lvl, Pair, Left, Not_end, (Mix
        (NoGreen, NoYellow, SomeOrange, NoRed)), (Mix (SomeGreen, NoYellow,
        NoOrange, NoRed)), cr, cr, (OrangeP cr), (Left_st (qp, qs, (Mix
        (NoGreen, NoYellow, SomeOrange, NoRed)), c0, p, (pair s2 s1))),
        (inject_chain (S lvl) Pair Not_end (Mix (SomeGreen, NoYellow,
          NoOrange, NoRed)) cr c (Small (lvl, qs, t0))))))
      | _ -> assert false (* absurd case *))
   | Red (pk, _) ->
     (match s with
      | Only_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (p0, s1) =
          eject2 (S
            (let rec add0 n m =
               match n with
               | Datatypes.O -> m
               | S p0 -> S (add0 p0 m)
             in add0 (S (S Datatypes.O)) qs)) s0
        in
        let Coq_pair (t0, s2) = p0 in
        Ok_lrt (lvl, Left, (Mix (NoGreen, NoYellow, NoOrange, SomeRed)),
        (Triple (lvl, pk, Left, Not_end, (Mix (NoGreen, NoYellow, NoOrange,
        SomeRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
        (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (NoGreen, NoYellow,
        NoOrange, SomeRed)), (Red (pk, Not_end)), (Left_st (qp, qs, (Mix
        (NoGreen, NoYellow, NoOrange, SomeRed)), c0, p, (pair s2 s1))),
        (inject_chain (S lvl) pk Not_end (Mix (SomeGreen, NoYellow, NoOrange,
          NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c (Small (lvl,
          qs, t0))))))
      | _ -> assert false (* absurd case *)))

(** val right_of_only :
    nat -> color -> 'a1 triple -> 'a1 left_right_triple **)

let right_of_only _ _ = function
| Triple (lvl, _, _, _, _, _, _, _, r, s, c) ->
  (match r with
   | Green (pk, _, cl, cr) ->
     (match s with
      | Only_end (q, p) ->
        (match c with
         | Empty _ ->
           (match has7 q p with
            | Coq_inl v -> Not_enough (lvl, Right, v)
            | Coq_inr p0 ->
              let Coq_pair (p1, t0) =
                pop2 (S
                  (let rec add0 n m =
                     match n with
                     | Datatypes.O -> m
                     | S p1 -> S (add0 p1 m)
                   in add0 (S (S (S (S Datatypes.O))))
                        (PeanoNat.Nat.iter (S (S (S (S (S (S (S
                          Datatypes.O))))))) PeanoNat.Nat.pred (S q)))) p0
              in
              let Coq_pair (s0, s1) = p1 in
              Ok_lrt (lvl, Right, (Mix (SomeGreen, NoYellow, NoOrange,
              NoRed)), (Triple (lvl, Only, Right, Is_end, (Mix (SomeGreen,
              NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
              NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
              NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Green
              (Only, Is_end, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
              (Mix (SomeGreen, NoYellow, NoOrange, NoRed)))), (Right_end
              ((PeanoNat.Nat.iter (S (S (S (S (S (S (S Datatypes.O)))))))
                 PeanoNat.Nat.pred (S q)), (pair s0 s1), t0)), (Empty (S
              lvl))))))
         | _ -> assert false (* absurd case *))
      | Only_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (p0, t0) =
          pop2 (S
            (let rec add0 n m =
               match n with
               | Datatypes.O -> m
               | S p0 -> S (add0 p0 m)
             in add0 (S (S Datatypes.O)) qp)) p
        in
        let Coq_pair (s1, s2) = p0 in
        Ok_lrt (lvl, Right, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
        (Triple (lvl, pk, Right, Not_end, (Mix (SomeGreen, NoYellow,
        NoOrange, NoRed)), cl, cr, (Mix (SomeGreen, NoYellow, NoOrange,
        NoRed)), (Green (pk, Not_end, cl, cr)), (Right_st (qp, qs, (Mix
        (SomeGreen, NoYellow, NoOrange, NoRed)), c0, (pair s1 s2), s0)),
        (push_chain (S lvl) pk Not_end cl cr (Small (lvl, qp, t0)) c))))
      | _ -> assert false (* absurd case *))
   | Yellow (pk, cl, cr) ->
     (match s with
      | Only_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (p0, t0) =
          pop2 (S
            (let rec add0 n m =
               match n with
               | Datatypes.O -> m
               | S p0 -> S (add0 p0 m)
             in add0 (S (S Datatypes.O)) qp)) p
        in
        let Coq_pair (s1, s2) = p0 in
        Ok_lrt (lvl, Right, cl, (Triple (lvl, pk, Right, Not_end, (Mix
        (NoGreen, SomeYellow, NoOrange, NoRed)), cl, cr, cl, (Yellow (pk, cl,
        cr)), (Right_st (qp, qs, (Mix (NoGreen, SomeYellow, NoOrange,
        NoRed)), c0, (pair s1 s2), s0)),
        (push_chain (S lvl) pk Not_end cl cr (Small (lvl, qp, t0)) c))))
      | _ -> assert false (* absurd case *))
   | OrangeO c0 ->
     (match s with
      | Only_st (qp, qs, _, c1, p, s0) ->
        let Coq_pair (p0, t0) =
          pop2 (S
            (let rec add0 n m =
               match n with
               | Datatypes.O -> m
               | S p0 -> S (add0 p0 m)
             in add0 (S (S Datatypes.O)) qp)) p
        in
        let Coq_pair (s1, s2) = p0 in
        Ok_lrt (lvl, Right, c0, (Triple (lvl, Only, Right, Not_end, (Mix
        (NoGreen, NoYellow, SomeOrange, NoRed)), c0, c0, c0, (OrangeO c0),
        (Right_st (qp, qs, (Mix (NoGreen, NoYellow, SomeOrange, NoRed)), c1,
        (pair s1 s2), s0)),
        (push_chain (S lvl) Only Not_end c0 c0 (Small (lvl, qp, t0)) c))))
      | _ -> assert false (* absurd case *))
   | OrangeP cr ->
     (match s with
      | Only_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (p0, t0) =
          pop2 (S
            (let rec add0 n m =
               match n with
               | Datatypes.O -> m
               | S p0 -> S (add0 p0 m)
             in add0 (S (S Datatypes.O)) qp)) p
        in
        let Coq_pair (s1, s2) = p0 in
        Ok_lrt (lvl, Right, cr, (Triple (lvl, Pair, Right, Not_end, (Mix
        (NoGreen, NoYellow, SomeOrange, NoRed)), (Mix (SomeGreen, NoYellow,
        NoOrange, NoRed)), cr, cr, (OrangeP cr), (Right_st (qp, qs, (Mix
        (NoGreen, NoYellow, SomeOrange, NoRed)), c0, (pair s1 s2), s0)),
        (push_chain (S lvl) Pair Not_end (Mix (SomeGreen, NoYellow, NoOrange,
          NoRed)) cr (Small (lvl, qp, t0)) c))))
      | _ -> assert false (* absurd case *))
   | Red (pk, _) ->
     (match s with
      | Only_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (p0, t0) =
          pop2 (S
            (let rec add0 n m =
               match n with
               | Datatypes.O -> m
               | S p0 -> S (add0 p0 m)
             in add0 (S (S Datatypes.O)) qp)) p
        in
        let Coq_pair (s1, s2) = p0 in
        Ok_lrt (lvl, Right, (Mix (NoGreen, NoYellow, NoOrange, SomeRed)),
        (Triple (lvl, pk, Right, Not_end, (Mix (NoGreen, NoYellow, NoOrange,
        SomeRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
        (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (NoGreen, NoYellow,
        NoOrange, SomeRed)), (Red (pk, Not_end)), (Right_st (qp, qs, (Mix
        (NoGreen, NoYellow, NoOrange, SomeRed)), c0, (pair s1 s2), s0)),
        (push_chain (S lvl) pk Not_end (Mix (SomeGreen, NoYellow, NoOrange,
          NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Small (lvl,
          qp, t0)) c))))
      | _ -> assert false (* absurd case *)))

(** val make_stored_suffix :
    nat -> nat -> nat -> kind -> ending -> color -> color -> 'a1 suffix ->
    'a1 prefix -> 'a1 chain -> 'a1 suffix -> ('a1 stored_triple, 'a1 suffix)
    prod **)

let make_stored_suffix lvl ql q pk e cl cr sl p child s =
  let Coq_pair (s0, s1) = two p in
  let Coq_pair (p0, s2) =
    eject2 (S
      (let rec add0 n m =
         match n with
         | Datatypes.O -> m
         | S p0 -> S (add0 p0 m)
       in add0 (S (S Datatypes.O)) q)) s
  in
  let Coq_pair (t, s3) = p0 in
  Coq_pair ((Big (lvl, ql, q, pk, e, cl, cr,
  (inject2 (add (S Datatypes.O) ql) sl s0 s1), child, t)), (pair s3 s2))

(** val make_prefix_stored :
    nat -> nat -> nat -> kind -> ending -> color -> color -> 'a1 prefix ->
    'a1 chain -> 'a1 suffix -> 'a1 prefix -> ('a1 prefix, 'a1 stored_triple)
    prod **)

let make_prefix_stored lvl q qr pk e cl cr p child s pr =
  let Coq_pair (p0, t) =
    pop2 (S
      (let rec add0 n m =
         match n with
         | Datatypes.O -> m
         | S p0 -> S (add0 p0 m)
       in add0 (S (S Datatypes.O)) q)) p
  in
  let Coq_pair (s0, s1) = p0 in
  let Coq_pair (s2, s3) = two s in
  Coq_pair ((pair s0 s1), (Big (lvl, q, qr, pk, e, cl, cr, t, child,
  (push2 (add (S Datatypes.O) qr) s2 s3 pr))))

(** val stored_of_right :
    nat -> nat -> color -> 'a1 suffix -> 'a1 triple -> ('a1 stored_triple,
    'a1 suffix) prod **)

let stored_of_right _ ql _ sl = function
| Triple (lvl, _, _, _, _, _, _, _, r, s, c) ->
  (match r with
   | Green (pk, _, cl, cr) ->
     (match s with
      | Right_end (qs, p, s0) ->
        (match c with
         | Empty _ ->
           make_stored_suffix lvl ql qs Only Is_end (Mix (SomeGreen,
             NoYellow, NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
             NoRed)) sl p (Empty (S lvl)) s0
         | _ -> assert false (* absurd case *))
      | Right_st (_, qs, _, _, p, s0) ->
        make_stored_suffix lvl ql qs pk Not_end cl cr sl p c s0
      | _ -> assert false (* absurd case *))
   | Yellow (pk, cl, cr) ->
     (match s with
      | Right_st (_, qs, _, _, p, s0) ->
        make_stored_suffix lvl ql qs pk Not_end cl cr sl p c s0
      | _ -> assert false (* absurd case *))
   | OrangeO c0 ->
     (match s with
      | Right_st (_, qs, _, _, p, s0) ->
        make_stored_suffix lvl ql qs Only Not_end c0 c0 sl p c s0
      | _ -> assert false (* absurd case *))
   | OrangeP cr ->
     (match s with
      | Right_st (_, qs, _, _, p, s0) ->
        make_stored_suffix lvl ql qs Pair Not_end (Mix (SomeGreen, NoYellow,
          NoOrange, NoRed)) cr sl p c s0
      | _ -> assert false (* absurd case *))
   | Red (pk, _) ->
     (match s with
      | Right_st (_, qs, _, _, p, s0) ->
        make_stored_suffix lvl ql qs pk Not_end (Mix (SomeGreen, NoYellow,
          NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) sl p
          c s0
      | _ -> assert false (* absurd case *)))

(** val stored_of_left :
    nat -> nat -> color -> 'a1 triple -> 'a1 prefix -> ('a1 prefix, 'a1
    stored_triple) prod **)

let stored_of_left _ qr _ tl pr =
  let Triple (lvl, _, _, _, _, _, _, _, r, s, c) = tl in
  (match r with
   | Green (pk, _, cl, cr) ->
     (match s with
      | Left_end (qp, p, s0) ->
        (match c with
         | Empty _ ->
           make_prefix_stored lvl qp qr Only Is_end (Mix (SomeGreen,
             NoYellow, NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
             NoRed)) p (Empty (S lvl)) s0 pr
         | _ -> assert false (* absurd case *))
      | Left_st (qp, _, _, _, p, s0) ->
        make_prefix_stored lvl qp qr pk Not_end cl cr p c s0 pr
      | _ -> assert false (* absurd case *))
   | Yellow (pk, cl, cr) ->
     (match s with
      | Left_st (qp, _, _, _, p, s0) ->
        make_prefix_stored lvl qp qr pk Not_end cl cr p c s0 pr
      | _ -> assert false (* absurd case *))
   | OrangeO c0 ->
     (match s with
      | Left_st (qp, _, _, _, p, s0) ->
        make_prefix_stored lvl qp qr Only Not_end c0 c0 p c s0 pr
      | _ -> assert false (* absurd case *))
   | OrangeP cr ->
     (match s with
      | Left_st (qp, _, _, _, p, s0) ->
        make_prefix_stored lvl qp qr Pair Not_end (Mix (SomeGreen, NoYellow,
          NoOrange, NoRed)) cr p c s0 pr
      | _ -> assert false (* absurd case *))
   | Red (pk, _) ->
     (match s with
      | Left_st (qp, _, _, _, p, s0) ->
        make_prefix_stored lvl qp qr pk Not_end (Mix (SomeGreen, NoYellow,
          NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) p c
          s0 pr
      | _ -> assert false (* absurd case *)))

(** val left_of_pair_obligations_obligation_1 : nat -> nat **)

let left_of_pair_obligations_obligation_1 qp =
  qp

(** val left_of_pair :
    nat -> color -> color -> 'a1 triple -> 'a1 triple -> 'a1 triple **)

let left_of_pair _ _ cr tl tr =
  let Triple (lvl, _, _, _, _, _, _, _, r, s, c) = tl in
  (match r with
   | Green (pk, _, cl, cr0) ->
     (match s with
      | Left_end (qp, p, s0) ->
        (match c with
         | Empty _ ->
           let Coq_pair (s1, t) = pop (S Datatypes.O) s0 in
           let Coq_pair (s2, s3) = stored_of_right lvl Datatypes.O cr t tr in
           Triple (lvl, Only, Left, Not_end, (Mix (NoGreen, NoYellow,
           SomeOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
           (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (OrangeO (Mix (SomeGreen, NoYellow,
           NoOrange, NoRed))), (Left_st ((add (S Datatypes.O) qp),
           (add (S Datatypes.O) (left_of_pair_obligations_obligation_1 qp)),
           (Mix (NoGreen, NoYellow, SomeOrange, NoRed)), (O (qp,
           (left_of_pair_obligations_obligation_1 qp))),
           (inject (add (S (S (S (S (S Datatypes.O))))) qp) p s1), s3)),
           (single_chain (S lvl) s2))
         | _ -> assert false (* absurd case *))
      | Left_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (s1, s2) = stored_of_right lvl (S Datatypes.O) cr s0 tr
        in
        Triple (lvl, pk, Left, Not_end, (Mix (SomeGreen, NoYellow, NoOrange,
        NoRed)), cl, cr0, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
        (Green (pk, Not_end, cl, cr0)), (Left_st (qp, qs, (Mix (SomeGreen,
        NoYellow, NoOrange, NoRed)), c0, p, s2)),
        (inject_chain (S lvl) pk Not_end cl cr0 c s1))
      | _ -> assert false (* absurd case *))
   | Yellow (pk, cl, cr0) ->
     (match s with
      | Left_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (s1, s2) = stored_of_right lvl (S Datatypes.O) cr s0 tr
        in
        Triple (lvl, pk, Left, Not_end, (Mix (NoGreen, SomeYellow, NoOrange,
        NoRed)), cl, cr0, cl, (Yellow (pk, cl, cr0)), (Left_st (qp, qs, (Mix
        (NoGreen, SomeYellow, NoOrange, NoRed)), c0, p, s2)),
        (inject_chain (S lvl) pk Not_end cl cr0 c s1))
      | _ -> assert false (* absurd case *))
   | OrangeO c0 ->
     (match s with
      | Left_st (qp, qs, _, c1, p, s0) ->
        let Coq_pair (s1, s2) = stored_of_right lvl (S Datatypes.O) cr s0 tr
        in
        Triple (lvl, Only, Left, Not_end, (Mix (NoGreen, NoYellow,
        SomeOrange, NoRed)), c0, c0, c0, (OrangeO c0), (Left_st (qp, qs, (Mix
        (NoGreen, NoYellow, SomeOrange, NoRed)), c1, p, s2)),
        (inject_chain (S lvl) Only Not_end c0 c0 c s1))
      | _ -> assert false (* absurd case *))
   | OrangeP cr0 ->
     (match s with
      | Left_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (s1, s2) = stored_of_right lvl (S Datatypes.O) cr s0 tr
        in
        Triple (lvl, Pair, Left, Not_end, (Mix (NoGreen, NoYellow,
        SomeOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
        cr0, cr0, (OrangeP cr0), (Left_st (qp, qs, (Mix (NoGreen, NoYellow,
        SomeOrange, NoRed)), c0, p, s2)),
        (inject_chain (S lvl) Pair Not_end (Mix (SomeGreen, NoYellow,
          NoOrange, NoRed)) cr0 c s1))
      | _ -> assert false (* absurd case *))
   | Red (pk, _) ->
     (match s with
      | Left_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (s1, s2) = stored_of_right lvl (S Datatypes.O) cr s0 tr
        in
        Triple (lvl, pk, Left, Not_end, (Mix (NoGreen, NoYellow, NoOrange,
        SomeRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
        (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (NoGreen, NoYellow,
        NoOrange, SomeRed)), (Red (pk, Not_end)), (Left_st (qp, qs, (Mix
        (NoGreen, NoYellow, NoOrange, SomeRed)), c0, p, s2)),
        (inject_chain (S lvl) pk Not_end (Mix (SomeGreen, NoYellow, NoOrange,
          NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c s1))
      | _ -> assert false (* absurd case *)))

(** val right_of_pair_obligations_obligation_1 : nat -> nat **)

let right_of_pair_obligations_obligation_1 qs =
  qs

(** val right_of_pair :
    nat -> color -> color -> 'a1 triple -> 'a1 triple -> 'a1 triple **)

let right_of_pair _ cl _ tl = function
| Triple (lvl, _, _, _, _, _, _, _, r, s, c) ->
  (match r with
   | Green (pk, _, cl0, cr) ->
     (match s with
      | Right_end (qs, p, s0) ->
        (match c with
         | Empty _ ->
           let Coq_pair (t, s1) = eject (S Datatypes.O) p in
           let Coq_pair (p0, s2) = stored_of_left lvl Datatypes.O cl tl t in
           Triple (lvl, Only, Right, Not_end, (Mix (NoGreen, NoYellow,
           SomeOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
           (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (OrangeO (Mix (SomeGreen, NoYellow,
           NoOrange, NoRed))), (Right_st
           ((add (S Datatypes.O) (right_of_pair_obligations_obligation_1 qs)),
           (add (S Datatypes.O) qs), (Mix (NoGreen, NoYellow, SomeOrange,
           NoRed)), (O ((right_of_pair_obligations_obligation_1 qs), qs)),
           p0, (push (add (S (S (S (S (S Datatypes.O))))) qs) s1 s0))),
           (single_chain (S lvl) s2))
         | _ -> assert false (* absurd case *))
      | Right_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (p0, s1) = stored_of_left lvl (S Datatypes.O) cl tl p in
        Triple (lvl, pk, Right, Not_end, (Mix (SomeGreen, NoYellow, NoOrange,
        NoRed)), cl0, cr, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
        (Green (pk, Not_end, cl0, cr)), (Right_st (qp, qs, (Mix (SomeGreen,
        NoYellow, NoOrange, NoRed)), c0, p0, s0)),
        (push_chain (S lvl) pk Not_end cl0 cr s1 c))
      | _ -> assert false (* absurd case *))
   | Yellow (pk, cl0, cr) ->
     (match s with
      | Right_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (p0, s1) = stored_of_left lvl (S Datatypes.O) cl tl p in
        Triple (lvl, pk, Right, Not_end, (Mix (NoGreen, SomeYellow, NoOrange,
        NoRed)), cl0, cr, cl0, (Yellow (pk, cl0, cr)), (Right_st (qp, qs,
        (Mix (NoGreen, SomeYellow, NoOrange, NoRed)), c0, p0, s0)),
        (push_chain (S lvl) pk Not_end cl0 cr s1 c))
      | _ -> assert false (* absurd case *))
   | OrangeO c0 ->
     (match s with
      | Right_st (qp, qs, _, c1, p, s0) ->
        let Coq_pair (p0, s1) = stored_of_left lvl (S Datatypes.O) cl tl p in
        Triple (lvl, Only, Right, Not_end, (Mix (NoGreen, NoYellow,
        SomeOrange, NoRed)), c0, c0, c0, (OrangeO c0), (Right_st (qp, qs,
        (Mix (NoGreen, NoYellow, SomeOrange, NoRed)), c1, p0, s0)),
        (push_chain (S lvl) Only Not_end c0 c0 s1 c))
      | _ -> assert false (* absurd case *))
   | OrangeP cr ->
     (match s with
      | Right_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (p0, s1) = stored_of_left lvl (S Datatypes.O) cl tl p in
        Triple (lvl, Pair, Right, Not_end, (Mix (NoGreen, NoYellow,
        SomeOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
        cr, cr, (OrangeP cr), (Right_st (qp, qs, (Mix (NoGreen, NoYellow,
        SomeOrange, NoRed)), c0, p0, s0)),
        (push_chain (S lvl) Pair Not_end (Mix (SomeGreen, NoYellow, NoOrange,
          NoRed)) cr s1 c))
      | _ -> assert false (* absurd case *))
   | Red (pk, _) ->
     (match s with
      | Right_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (p0, s1) = stored_of_left lvl (S Datatypes.O) cl tl p in
        Triple (lvl, pk, Right, Not_end, (Mix (NoGreen, NoYellow, NoOrange,
        SomeRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
        (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (NoGreen, NoYellow,
        NoOrange, SomeRed)), (Red (pk, Not_end)), (Right_st (qp, qs, (Mix
        (NoGreen, NoYellow, NoOrange, SomeRed)), c0, p0, s0)),
        (push_chain (S lvl) pk Not_end (Mix (SomeGreen, NoYellow, NoOrange,
          NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) s1 c))
      | _ -> assert false (* absurd case *)))

(** val make_left :
    nat -> kind -> ending -> color -> color -> 'a1 chain -> 'a1
    left_right_triple **)

let make_left _ _ _ _ _ = function
| Empty lvl ->
  Not_enough (lvl, Left, (V0 (S (S (S (S (S (S Datatypes.O))))))))
| Only_chain (hlvl, tlvl, _, pk, e, c0, cl, cr, c1, p, c2) ->
  left_of_only hlvl c0
    (triple_of_chain hlvl Only c0 (Only_chain (hlvl, tlvl, Only, pk, e, c0,
      cl, cr, c1, p, c2)))
| Pair_chain (lvl, cl, cr, c0, c1) ->
  Ok_lrt (lvl, Left, cl,
    (left_of_pair lvl cl cr (triple_of_chain lvl Left cl c0)
      (triple_of_chain lvl Right cr c1)))

(** val make_right :
    nat -> kind -> ending -> color -> color -> 'a1 chain -> 'a1
    left_right_triple **)

let make_right _ _ _ _ _ = function
| Empty lvl ->
  Not_enough (lvl, Right, (V0 (S (S (S (S (S (S Datatypes.O))))))))
| Only_chain (hlvl, tlvl, _, pk, e, c0, cl, cr, c1, p, c2) ->
  right_of_only hlvl c0
    (triple_of_chain hlvl Only c0 (Only_chain (hlvl, tlvl, Only, pk, e, c0,
      cl, cr, c1, p, c2)))
| Pair_chain (lvl, cl, cr, c0, c1) ->
  Ok_lrt (lvl, Right, cr,
    (right_of_pair lvl cl cr (triple_of_chain lvl Left cl c0)
      (triple_of_chain lvl Right cr c1)))

(** val concat_semi :
    nat -> 'a1 semi_deque -> 'a1 semi_deque -> 'a1 semi_deque **)

let concat_semi _ s1 s2 =
  let Semi (_, pk, e, cl, cr, c) = s1 in
  let Semi (lvl, pk0, e0, cl0, cr0, c0) = s2 in
  (match make_left lvl pk e cl cr c with
   | Not_enough (lvl0, _, v) ->
     let NE_chain (lvl1, pk1, _, e1, cl1, cr1, c1) =
       push_vector lvl0 (S (S (S (S (S (S Datatypes.O)))))) pk0 cl0 cr0 v
         (NE_chain (lvl0, pk0, Only, e0, cl0, cr0, c0))
     in
     Semi (lvl1, pk1, e1, cl1, cr1, c1)
   | Ok_lrt (lvl0, _, cpkt, t) ->
     (match make_right lvl0 pk0 e0 cl0 cr0 c0 with
      | Not_enough (lvl1, _, v) ->
        let NE_chain (lvl2, pk1, _, e1, cl1, cr1, c1) =
          inject_vector lvl1 (S (S (S (S (S (S Datatypes.O)))))) pk cpkt cr
            (NE_chain (lvl1, pk, Only, e, cpkt, cr, c)) v
        in
        Semi (lvl2, pk1, e1, cl1, cr1, c1)
      | Ok_lrt (lvl1, _, cpkt0, t0) ->
        Semi (lvl1, Pair, Not_end, cpkt, cpkt0, (Pair_chain (lvl1, cpkt,
          cpkt0, (chain_of_triple lvl1 Left cpkt t),
          (chain_of_triple lvl1 Right cpkt0 t0))))))

(** val orange_reg : nat -> kind -> color -> 'a1 chain -> regularity **)

let orange_reg _ _ _ = function
| Empty _ -> assert false (* absurd case *)
| Only_chain (_, _, _, _, _, _, _, _, _, _, _) ->
  OrangeO (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
| Pair_chain (_, _, cr, _, _) -> OrangeP cr

(** val pop_left_green_obligations_obligation_3 : nat -> nat **)

let pop_left_green_obligations_obligation_3 qs =
  qs

(** val pop_left_green_obligations_obligation_5 : nat -> nat **)

let pop_left_green_obligations_obligation_5 qs0 =
  qs0

(** val pop_left_green_obligations_obligation_7 : nat -> nat **)

let pop_left_green_obligations_obligation_7 qs2 =
  qs2

(** val pop_left_green_obligations_obligation_9 : nat -> nat **)

let pop_left_green_obligations_obligation_9 qs2 =
  qs2

(** val pop_left_green :
    nat -> 'a1 triple -> ('a1 stored_triple, 'a1 partial_triple) prod **)

let pop_left_green _ = function
| Triple (lvl, _, _, _, _, _, _, _, r, s, c) ->
  (match r with
   | Green (pk, _, cl, cr) ->
     (match s with
      | Left_end (qp, p, s0) ->
        (match c with
         | Empty _ ->
           let Coq_pair (s1, t) =
             pop (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) qp)) p
           in
           (match has5 qp t with
            | Coq_inl p0 ->
              let Coq_pair (s2, s3) = two s0 in
              Coq_pair (s1, (Six_elements (lvl, Left, (Coq_pair ((Coq_pair
              (p0, s2)), s3)))))
            | Coq_inr p0 ->
              Coq_pair (s1, (Ok_pt (lvl, Pair, Left, (Mix (SomeGreen,
                NoYellow, NoOrange, NoRed)), (Triple (lvl, Only, Left,
                Is_end, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
                (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
                NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
                NoOrange, NoRed)), (Green (Only, Is_end, (Mix (SomeGreen,
                NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
                NoOrange, NoRed)))), (Left_end
                ((PeanoNat.Nat.iter (S (S (S (S (S Datatypes.O)))))
                   PeanoNat.Nat.pred (add (S (S (S (S Datatypes.O)))) qp)),
                p0, s0)), (Empty (S lvl))))))))
         | _ -> assert false (* absurd case *))
      | Left_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | G (qp, qs) ->
           let Coq_pair (s1, t) =
             pop (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O)))
                     (add (S (S (S Datatypes.O))) qp))) p
           in
           Coq_pair (s1, (Ok_pt (lvl, Pair, Left, cl, (Triple (lvl, pk, Left,
           Not_end, (Mix (NoGreen, SomeYellow, NoOrange, NoRed)), cl, cr, cl,
           (Yellow (pk, cl, cr)), (Left_st ((add (S (S Datatypes.O)) qp),
           (add (S (S Datatypes.O))
             (pop_left_green_obligations_obligation_3 qs)), (Mix (NoGreen,
           SomeYellow, NoOrange, NoRed)), (Y (qp,
           (pop_left_green_obligations_obligation_3 qs))), t, s0)), c)))))
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (pk, _, cr) ->
     (match s with
      | Left_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | Y (qp, qs) ->
           let Coq_pair (s1, t) =
             pop (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S (S Datatypes.O)) qp)))
               p
           in
           Coq_pair (s1, (Ok_pt (lvl, Pair, Left, cr, (Triple (lvl, pk, Left,
           Not_end, (Mix (NoGreen, NoYellow, SomeOrange, NoRed)), (Mix
           (SomeGreen, NoYellow, NoOrange, NoRed)), cr, cr,
           (orange_reg (S lvl) pk cr c), (Left_st ((add (S Datatypes.O) qp),
           (add (S Datatypes.O) (pop_left_green_obligations_obligation_5 qs)),
           (Mix (NoGreen, NoYellow, SomeOrange, NoRed)), (O (qp,
           (pop_left_green_obligations_obligation_5 qs))), t, s0)), c)))))
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | OrangeO _ ->
     (match s with
      | Left_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | O (qp, qs) ->
           let Coq_pair (s1, t) =
             pop (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S Datatypes.O) qp))) p
           in
           Coq_pair (s1, (Ok_pt (lvl, Pair, Left, (Mix (NoGreen, NoYellow,
           NoOrange, SomeRed)), (Triple (lvl, Only, Left, Not_end, (Mix
           (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Red (Only,
           Not_end)), (Left_st ((add Datatypes.O qp),
           (add Datatypes.O (pop_left_green_obligations_obligation_7 qs)),
           (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (R (qp,
           (pop_left_green_obligations_obligation_7 qs))), t, s0)), c)))))
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | OrangeP _ ->
     (match s with
      | Left_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | O (qp, qs) ->
           let Coq_pair (s1, t) =
             pop (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S Datatypes.O) qp))) p
           in
           Coq_pair (s1, (Ok_pt (lvl, Pair, Left, (Mix (NoGreen, NoYellow,
           NoOrange, SomeRed)), (Triple (lvl, Pair, Left, Not_end, (Mix
           (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Red (Pair,
           Not_end)), (Left_st ((add Datatypes.O qp),
           (add Datatypes.O (pop_left_green_obligations_obligation_9 qs)),
           (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (R (qp,
           (pop_left_green_obligations_obligation_9 qs))), t, s0)), c)))))
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Red (_, _) -> assert false (* absurd case *))

(** val eject_right_green_obligations_obligation_3 : nat -> nat **)

let eject_right_green_obligations_obligation_3 qs =
  qs

(** val eject_right_green_obligations_obligation_5 : nat -> nat **)

let eject_right_green_obligations_obligation_5 qs0 =
  qs0

(** val eject_right_green_obligations_obligation_7 : nat -> nat **)

let eject_right_green_obligations_obligation_7 qs1 =
  qs1

(** val eject_right_green_obligations_obligation_9 : nat -> nat **)

let eject_right_green_obligations_obligation_9 qs1 =
  qs1

(** val eject_right_green :
    nat -> 'a1 triple -> ('a1 partial_triple, 'a1 stored_triple) prod **)

let eject_right_green _ = function
| Triple (lvl, _, _, _, _, _, _, _, r, s, c) ->
  (match r with
   | Green (pk, _, cl, cr) ->
     (match s with
      | Right_end (qs, p, s0) ->
        (match c with
         | Empty _ ->
           let Coq_pair (t, s1) =
             eject (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) qs)) s0
           in
           (match has5 qs t with
            | Coq_inl p0 ->
              let Coq_pair (p1, s2) = p0 in
              let Coq_pair (p2, s3) = p1 in
              let Coq_pair (s4, s5) = p2 in
              Coq_pair ((Six_elements (lvl, Right, (Coq_pair ((Coq_pair
              ((Coq_pair ((Coq_pair ((two p), s4)), s5)), s3)), s2)))), s1)
            | Coq_inr p0 ->
              Coq_pair ((Ok_pt (lvl, Pair, Right, (Mix (SomeGreen, NoYellow,
                NoOrange, NoRed)), (Triple (lvl, Only, Right, Is_end, (Mix
                (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
                NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
                NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
                NoRed)), (Green (Only, Is_end, (Mix (SomeGreen, NoYellow,
                NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
                NoRed)))), (Right_end
                ((PeanoNat.Nat.iter (S (S (S (S (S Datatypes.O)))))
                   PeanoNat.Nat.pred (add (S (S (S (S Datatypes.O)))) qs)),
                p, p0)), (Empty (S lvl)))))), s1))
         | _ -> assert false (* absurd case *))
      | Right_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | G (_, qs) ->
           let Coq_pair (t, s1) =
             eject (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O)))
                     (add (S (S (S Datatypes.O))) qs))) s0
           in
           Coq_pair ((Ok_pt (lvl, Pair, Right, cl, (Triple (lvl, pk, Right,
           Not_end, (Mix (NoGreen, SomeYellow, NoOrange, NoRed)), cl, cr, cl,
           (Yellow (pk, cl, cr)), (Right_st
           ((add (S (S Datatypes.O))
              (eject_right_green_obligations_obligation_3 qs)),
           (add (S (S Datatypes.O)) qs), (Mix (NoGreen, SomeYellow, NoOrange,
           NoRed)), (Y ((eject_right_green_obligations_obligation_3 qs),
           qs)), p, t)), c)))), s1)
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (pk, _, cr) ->
     (match s with
      | Right_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | Y (_, qs) ->
           let Coq_pair (t, s1) =
             eject (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S (S Datatypes.O)) qs)))
               s0
           in
           Coq_pair ((Ok_pt (lvl, Pair, Right, cr, (Triple (lvl, pk, Right,
           Not_end, (Mix (NoGreen, NoYellow, SomeOrange, NoRed)), (Mix
           (SomeGreen, NoYellow, NoOrange, NoRed)), cr, cr,
           (orange_reg (S lvl) pk cr c), (Right_st
           ((add (S Datatypes.O)
              (eject_right_green_obligations_obligation_5 qs)),
           (add (S Datatypes.O) qs), (Mix (NoGreen, NoYellow, SomeOrange,
           NoRed)), (O ((eject_right_green_obligations_obligation_5 qs),
           qs)), p, t)), c)))), s1)
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | OrangeO _ ->
     (match s with
      | Right_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | O (_, qs) ->
           let Coq_pair (t, s1) =
             eject (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S Datatypes.O) qs))) s0
           in
           Coq_pair ((Ok_pt (lvl, Pair, Right, (Mix (NoGreen, NoYellow,
           NoOrange, SomeRed)), (Triple (lvl, Only, Right, Not_end, (Mix
           (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Red (Only,
           Not_end)), (Right_st
           ((add Datatypes.O (eject_right_green_obligations_obligation_7 qs)),
           (add Datatypes.O qs), (Mix (NoGreen, NoYellow, NoOrange,
           SomeRed)), (R ((eject_right_green_obligations_obligation_7 qs),
           qs)), p, t)), c)))), s1)
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | OrangeP _ ->
     (match s with
      | Right_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | O (_, qs) ->
           let Coq_pair (t, s1) =
             eject (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S Datatypes.O) qs))) s0
           in
           Coq_pair ((Ok_pt (lvl, Pair, Right, (Mix (NoGreen, NoYellow,
           NoOrange, SomeRed)), (Triple (lvl, Pair, Right, Not_end, (Mix
           (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Red (Pair,
           Not_end)), (Right_st
           ((add Datatypes.O (eject_right_green_obligations_obligation_9 qs)),
           (add Datatypes.O qs), (Mix (NoGreen, NoYellow, NoOrange,
           SomeRed)), (R ((eject_right_green_obligations_obligation_9 qs),
           qs)), p, t)), c)))), s1)
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Red (_, _) -> assert false (* absurd case *))

(** val pop_only_green :
    nat -> 'a1 triple -> ('a1 stored_triple, 'a1 partial_triple) prod **)

let pop_only_green _ = function
| Triple (lvl, _, _, _, _, _, _, _, r, s, c) ->
  (match r with
   | Green (pk, _, cl, cr) ->
     (match s with
      | Only_end (q, p) ->
        (match c with
         | Empty _ ->
           let Coq_pair (s0, t0) = pop q p in
           (match has1 q t0 with
            | Some p0 ->
              Coq_pair (s0, (Ok_pt (lvl, Only, Only, (Mix (SomeGreen,
                NoYellow, NoOrange, NoRed)), (Triple (lvl, Only, Only,
                Is_end, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
                (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
                NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
                NoOrange, NoRed)), (Green (Only, Is_end, (Mix (SomeGreen,
                NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
                NoOrange, NoRed)))), (Only_end
                ((PeanoNat.Nat.iter (S Datatypes.O) PeanoNat.Nat.pred q),
                p0)), (Empty (S lvl)))))))
            | None -> Coq_pair (s0, (Zero_element (lvl, Only))))
         | _ -> assert false (* absurd case *))
      | Only_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | G (qp, qs) ->
           let Coq_pair (s1, t0) =
             pop (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O)))
                     (add (S (S (S Datatypes.O))) qp))) p
           in
           Coq_pair (s1, (Ok_pt (lvl, Only, Only, cl, (Triple (lvl, pk, Only,
           Not_end, (Mix (NoGreen, SomeYellow, NoOrange, NoRed)), cl, cr, cl,
           (Yellow (pk, cl, cr)), (Only_st ((add (S (S Datatypes.O)) qp),
           (add (S (S Datatypes.O)) (S
             (let rec add0 n m =
                match n with
                | Datatypes.O -> m
                | S p0 -> S (add0 p0 m)
              in add0 Datatypes.O qs))), (Mix (NoGreen, SomeYellow, NoOrange,
           NoRed)), (Y (qp, (S
           (let rec add0 n m =
              match n with
              | Datatypes.O -> m
              | S p0 -> S (add0 p0 m)
            in add0 Datatypes.O qs)))), t0, s0)), c)))))
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (pk, _, cr) ->
     (match s with
      | Only_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | Y (qp, qs) ->
           let Coq_pair (s1, t0) =
             pop (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S (S Datatypes.O)) qp)))
               p
           in
           Coq_pair (s1, (Ok_pt (lvl, Only, Only, cr, (Triple (lvl, pk, Only,
           Not_end, (Mix (NoGreen, NoYellow, SomeOrange, NoRed)), (Mix
           (SomeGreen, NoYellow, NoOrange, NoRed)), cr, cr,
           (orange_reg (S lvl) pk cr c), (Only_st ((add (S Datatypes.O) qp),
           (add (S Datatypes.O) (S
             (let rec add0 n m =
                match n with
                | Datatypes.O -> m
                | S p0 -> S (add0 p0 m)
              in add0 Datatypes.O qs))), (Mix (NoGreen, NoYellow, SomeOrange,
           NoRed)), (O (qp, (S
           (let rec add0 n m =
              match n with
              | Datatypes.O -> m
              | S p0 -> S (add0 p0 m)
            in add0 Datatypes.O qs)))), t0, s0)), c)))))
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | OrangeO _ ->
     (match s with
      | Only_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | O (qp, qs) ->
           let Coq_pair (s1, t0) =
             pop (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S Datatypes.O) qp))) p
           in
           Coq_pair (s1, (Ok_pt (lvl, Only, Only, (Mix (NoGreen, NoYellow,
           NoOrange, SomeRed)), (Triple (lvl, Only, Only, Not_end, (Mix
           (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Red (Only,
           Not_end)), (Only_st ((add Datatypes.O qp),
           (add Datatypes.O (add (S Datatypes.O) qs)), (Mix (NoGreen,
           NoYellow, NoOrange, SomeRed)), (R (qp, (add (S Datatypes.O) qs))),
           t0, s0)), c)))))
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | OrangeP _ ->
     (match s with
      | Only_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | O (qp, qs) ->
           let Coq_pair (s1, t0) =
             pop (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S Datatypes.O) qp))) p
           in
           Coq_pair (s1, (Ok_pt (lvl, Only, Only, (Mix (NoGreen, NoYellow,
           NoOrange, SomeRed)), (Triple (lvl, Pair, Only, Not_end, (Mix
           (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Red (Pair,
           Not_end)), (Only_st ((add Datatypes.O qp),
           (add Datatypes.O (add (S Datatypes.O) qs)), (Mix (NoGreen,
           NoYellow, NoOrange, SomeRed)), (R (qp, (add (S Datatypes.O) qs))),
           t0, s0)), c)))))
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Red (_, _) -> assert false (* absurd case *))

(** val eject_only_green :
    nat -> 'a1 triple -> ('a1 partial_triple, 'a1 stored_triple) prod **)

let eject_only_green _ = function
| Triple (lvl, _, _, _, _, _, _, _, r, s, c) ->
  (match r with
   | Green (pk, _, cl, cr) ->
     (match s with
      | Only_end (q, p) ->
        (match c with
         | Empty _ ->
           let Coq_pair (t0, s0) = eject q p in
           (match has1 q t0 with
            | Some p0 ->
              Coq_pair ((Ok_pt (lvl, Only, Only, (Mix (SomeGreen, NoYellow,
                NoOrange, NoRed)), (Triple (lvl, Only, Only, Is_end, (Mix
                (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
                NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
                NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
                NoRed)), (Green (Only, Is_end, (Mix (SomeGreen, NoYellow,
                NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
                NoRed)))), (Only_end
                ((PeanoNat.Nat.iter (S Datatypes.O) PeanoNat.Nat.pred q),
                p0)), (Empty (S lvl)))))), s0)
            | None -> Coq_pair ((Zero_element (lvl, Only)), s0))
         | _ -> assert false (* absurd case *))
      | Only_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | G (qp, qs) ->
           let Coq_pair (t0, s1) =
             eject (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O)))
                     (add (S (S (S Datatypes.O))) qs))) s0
           in
           Coq_pair ((Ok_pt (lvl, Only, Only, cl, (Triple (lvl, pk, Only,
           Not_end, (Mix (NoGreen, SomeYellow, NoOrange, NoRed)), cl, cr, cl,
           (Yellow (pk, cl, cr)), (Only_st
           ((add (S (S Datatypes.O)) (S
              (let rec add0 n m =
                 match n with
                 | Datatypes.O -> m
                 | S p0 -> S (add0 p0 m)
               in add0 Datatypes.O qp))), (add (S (S Datatypes.O)) qs), (Mix
           (NoGreen, SomeYellow, NoOrange, NoRed)), (Y ((S
           (let rec add0 n m =
              match n with
              | Datatypes.O -> m
              | S p0 -> S (add0 p0 m)
            in add0 Datatypes.O qp)), qs)), p, t0)), c)))), s1)
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (pk, _, cr) ->
     (match s with
      | Only_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | Y (qp, qs) ->
           let Coq_pair (t0, s1) =
             eject (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S (S Datatypes.O)) qs)))
               s0
           in
           Coq_pair ((Ok_pt (lvl, Only, Only, cr, (Triple (lvl, pk, Only,
           Not_end, (Mix (NoGreen, NoYellow, SomeOrange, NoRed)), (Mix
           (SomeGreen, NoYellow, NoOrange, NoRed)), cr, cr,
           (orange_reg (S lvl) pk cr c), (Only_st
           ((add (S Datatypes.O) (S
              (let rec add0 n m =
                 match n with
                 | Datatypes.O -> m
                 | S p0 -> S (add0 p0 m)
               in add0 Datatypes.O qp))), (add (S Datatypes.O) qs), (Mix
           (NoGreen, NoYellow, SomeOrange, NoRed)), (O ((S
           (let rec add0 n m =
              match n with
              | Datatypes.O -> m
              | S p0 -> S (add0 p0 m)
            in add0 Datatypes.O qp)), qs)), p, t0)), c)))), s1)
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | OrangeO _ ->
     (match s with
      | Only_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | O (qp, qs) ->
           let Coq_pair (t0, s1) =
             eject (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S Datatypes.O) qs))) s0
           in
           Coq_pair ((Ok_pt (lvl, Only, Only, (Mix (NoGreen, NoYellow,
           NoOrange, SomeRed)), (Triple (lvl, Only, Only, Not_end, (Mix
           (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Red (Only,
           Not_end)), (Only_st ((add Datatypes.O (add (S Datatypes.O) qp)),
           (add Datatypes.O qs), (Mix (NoGreen, NoYellow, NoOrange,
           SomeRed)), (R ((add (S Datatypes.O) qp), qs)), p, t0)), c)))), s1)
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | OrangeP _ ->
     (match s with
      | Only_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | O (qp, qs) ->
           let Coq_pair (t0, s1) =
             eject (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S Datatypes.O) qs))) s0
           in
           Coq_pair ((Ok_pt (lvl, Only, Only, (Mix (NoGreen, NoYellow,
           NoOrange, SomeRed)), (Triple (lvl, Pair, Only, Not_end, (Mix
           (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Red (Pair,
           Not_end)), (Only_st ((add Datatypes.O (add (S Datatypes.O) qp)),
           (add Datatypes.O qs), (Mix (NoGreen, NoYellow, NoOrange,
           SomeRed)), (R ((add (S Datatypes.O) qp), qs)), p, t0)), c)))), s1)
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Red (_, _) -> assert false (* absurd case *))

(** val sandwich_only_green :
    nat -> 'a1 triple -> ('a1 stored_triple, 'a1 partial_triple) sandwich **)

let sandwich_only_green _ = function
| Triple (lvl, _, _, _, _, _, _, _, r, s, c) ->
  (match r with
   | Green (pk, _, cl, cr) ->
     (match s with
      | Only_end (q, p) ->
        (match c with
         | Empty _ ->
           let Coq_pair (s0, t0) = pop q p in
           (match has1 q t0 with
            | Some p0 ->
              let Coq_pair (t1, s1) =
                eject (PeanoNat.Nat.iter (S Datatypes.O) PeanoNat.Nat.pred q)
                  p0
              in
              (match has1
                       (PeanoNat.Nat.iter (S Datatypes.O) PeanoNat.Nat.pred q)
                       t1 with
               | Some p1 ->
                 Sandwich (s0, (Ok_pt (lvl, Only, Only, (Mix (SomeGreen,
                   NoYellow, NoOrange, NoRed)), (Triple (lvl, Only, Only,
                   Is_end, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
                   (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
                   NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
                   NoOrange, NoRed)), (Green (Only, Is_end, (Mix (SomeGreen,
                   NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
                   NoOrange, NoRed)))), (Only_end
                   ((PeanoNat.Nat.iter (S Datatypes.O) PeanoNat.Nat.pred
                      (PeanoNat.Nat.iter (S Datatypes.O) PeanoNat.Nat.pred q)),
                   p1)), (Empty (S lvl)))))), s1)
               | None -> Sandwich (s0, (Zero_element (lvl, Only)), s1))
            | None -> Alone s0)
         | _ -> assert false (* absurd case *))
      | Only_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | G (qp, qs) ->
           let Coq_pair (s1, t0) =
             pop (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O)))
                     (add (S (S (S Datatypes.O))) qp))) p
           in
           let Coq_pair (t1, s2) =
             eject (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O)))
                     (add (S (S (S Datatypes.O))) qs))) s0
           in
           Sandwich (s1, (Ok_pt (lvl, Only, Only, cl, (Triple (lvl, pk, Only,
           Not_end, (Mix (NoGreen, SomeYellow, NoOrange, NoRed)), cl, cr, cl,
           (Yellow (pk, cl, cr)), (Only_st ((add (S (S Datatypes.O)) qp),
           (add (S (S Datatypes.O)) qs), (Mix (NoGreen, SomeYellow, NoOrange,
           NoRed)), (Y (qp, qs)), t0, t1)), c)))), s2)
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (pk, _, cr) ->
     (match s with
      | Only_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | Y (qp, qs) ->
           let Coq_pair (s1, t0) =
             pop (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S (S Datatypes.O)) qp)))
               p
           in
           let Coq_pair (t1, s2) =
             eject (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S (S Datatypes.O)) qs)))
               s0
           in
           Sandwich (s1, (Ok_pt (lvl, Only, Only, cr, (Triple (lvl, pk, Only,
           Not_end, (Mix (NoGreen, NoYellow, SomeOrange, NoRed)), (Mix
           (SomeGreen, NoYellow, NoOrange, NoRed)), cr, cr,
           (orange_reg (S lvl) pk cr c), (Only_st ((add (S Datatypes.O) qp),
           (add (S Datatypes.O) qs), (Mix (NoGreen, NoYellow, SomeOrange,
           NoRed)), (O (qp, qs)), t0, t1)), c)))), s2)
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | OrangeO _ ->
     (match s with
      | Only_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | O (qp, qs) ->
           let Coq_pair (s1, t0) =
             pop (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S Datatypes.O) qp))) p
           in
           let Coq_pair (t1, s2) =
             eject (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S Datatypes.O) qs))) s0
           in
           Sandwich (s1, (Ok_pt (lvl, Only, Only, (Mix (NoGreen, NoYellow,
           NoOrange, SomeRed)), (Triple (lvl, Only, Only, Not_end, (Mix
           (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Red (Only,
           Not_end)), (Only_st ((add Datatypes.O qp), (add Datatypes.O qs),
           (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (R (qp, qs)), t0,
           t1)), c)))), s2)
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | OrangeP _ ->
     (match s with
      | Only_st (_, _, _, c0, p, s0) ->
        (match c0 with
         | O (qp, qs) ->
           let Coq_pair (s1, t0) =
             pop (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S Datatypes.O) qp))) p
           in
           let Coq_pair (t1, s2) =
             eject (S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S (S Datatypes.O))) (add (S Datatypes.O) qs))) s0
           in
           Sandwich (s1, (Ok_pt (lvl, Only, Only, (Mix (NoGreen, NoYellow,
           NoOrange, SomeRed)), (Triple (lvl, Pair, Only, Not_end, (Mix
           (NoGreen, NoYellow, NoOrange, SomeRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Red (Pair,
           Not_end)), (Only_st ((add Datatypes.O qp), (add Datatypes.O qs),
           (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (R (qp, qs)), t0,
           t1)), c)))), s2)
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Red (_, _) -> assert false (* absurd case *))

(** val adapt_to_prefix :
    nat -> nat -> nat -> color -> coloring -> coloring **)

let adapt_to_prefix _ _ q _ = function
| G (_, qs) -> G (q, qs)
| Y (_, qs) ->
  Y ((S
    (let rec add0 n m =
       match n with
       | Datatypes.O -> m
       | S p -> S (add0 p m)
     in add0 Datatypes.O q)), qs)
| O (_, qs) ->
  O ((S
    (let rec add0 n m =
       match n with
       | Datatypes.O -> m
       | S p -> S (add0 p m)
     in add0 (S Datatypes.O) q)), qs)
| R (_, qs) ->
  R ((S
    (let rec add0 n m =
       match n with
       | Datatypes.O -> m
       | S p -> S (add0 p m)
     in add0 (S (S Datatypes.O)) q)), qs)

(** val only_of_right :
    nat -> color -> 'a1 six_stored_triple -> 'a1 triple -> 'a1 triple **)

let only_of_right _ _ six tr =
  let Coq_pair (p, s) = six in
  let Coq_pair (p0, s0) = p in
  let Coq_pair (p1, s1) = p0 in
  let Coq_pair (p2, s2) = p1 in
  let Coq_pair (s3, s4) = p2 in
  let Triple (lvl, _, _, _, _, _, _, _, r, s5, c) = tr in
  (match r with
   | Green (pk, _, cl, cr) ->
     (match s5 with
      | Right_end (qs, p3, s6) ->
        (match c with
         | Empty _ ->
           let Coq_pair (s7, s8) = two p3 in
           Triple (lvl, Only, Only, Is_end, (Mix (SomeGreen, NoYellow,
           NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
           (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Green (Only, Is_end, (Mix
           (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)))), (Only_end ((S
           (let rec add0 n m =
              match n with
              | Datatypes.O -> m
              | S p4 -> S (add0 p4 m)
            in add0 (S (S (S (S Datatypes.O)))) (S (S
                 (add (S (S (S (S (S Datatypes.O))))) qs))))),
           (push6 (S (S (add (S (S (S (S (S Datatypes.O))))) qs))) s3 s4 s2
             s1 s0 s
             (push2 (add (S (S (S (S (S Datatypes.O))))) qs) s7 s8 s6)))),
           (Empty (S lvl)))
         | _ -> assert false (* absurd case *))
      | Right_st (qp, qs, _, c0, p3, s6) ->
        Triple (lvl, pk, Only, Not_end, (Mix (SomeGreen, NoYellow, NoOrange,
          NoRed)), cl, cr, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
          (Green (pk, Not_end, cl, cr)), (Only_st
          ((add (S (S (S Datatypes.O))) Datatypes.O), qs, (Mix (SomeGreen,
          NoYellow, NoOrange, NoRed)),
          (adapt_to_prefix qp qs Datatypes.O (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) c0),
          (push6 (S (S Datatypes.O)) s3 s4 s2 s1 s0 s p3), s6)), c)
      | _ -> assert false (* absurd case *))
   | Yellow (pk, cl, cr) ->
     (match s5 with
      | Right_st (qp, qs, _, c0, p3, s6) ->
        Triple (lvl, pk, Only, Not_end, (Mix (NoGreen, SomeYellow, NoOrange,
          NoRed)), cl, cr, cl, (Yellow (pk, cl, cr)), (Only_st
          ((add (S (S (S Datatypes.O))) Datatypes.O), qs, (Mix (NoGreen,
          SomeYellow, NoOrange, NoRed)),
          (adapt_to_prefix qp qs Datatypes.O (Mix (NoGreen, SomeYellow,
            NoOrange, NoRed)) c0),
          (push6 (S (S Datatypes.O)) s3 s4 s2 s1 s0 s p3), s6)), c)
      | _ -> assert false (* absurd case *))
   | OrangeO c0 ->
     (match s5 with
      | Right_st (qp, qs, _, c1, p3, s6) ->
        Triple (lvl, Only, Only, Not_end, (Mix (NoGreen, NoYellow,
          SomeOrange, NoRed)), c0, c0, c0, (OrangeO c0), (Only_st
          ((add (S (S (S Datatypes.O))) Datatypes.O), qs, (Mix (NoGreen,
          NoYellow, SomeOrange, NoRed)),
          (adapt_to_prefix qp qs Datatypes.O (Mix (NoGreen, NoYellow,
            SomeOrange, NoRed)) c1),
          (push6 (S (S Datatypes.O)) s3 s4 s2 s1 s0 s p3), s6)), c)
      | _ -> assert false (* absurd case *))
   | OrangeP cr ->
     (match s5 with
      | Right_st (qp, qs, _, c0, p3, s6) ->
        Triple (lvl, Pair, Only, Not_end, (Mix (NoGreen, NoYellow,
          SomeOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
          cr, cr, (OrangeP cr), (Only_st
          ((add (S (S (S Datatypes.O))) Datatypes.O), qs, (Mix (NoGreen,
          NoYellow, SomeOrange, NoRed)),
          (adapt_to_prefix qp qs Datatypes.O (Mix (NoGreen, NoYellow,
            SomeOrange, NoRed)) c0),
          (push6 (S (S Datatypes.O)) s3 s4 s2 s1 s0 s p3), s6)), c)
      | _ -> assert false (* absurd case *))
   | Red (pk, _) ->
     (match s5 with
      | Right_st (qp, qs, _, c0, p3, s6) ->
        Triple (lvl, pk, Only, Not_end, (Mix (NoGreen, NoYellow, NoOrange,
          SomeRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
          (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (NoGreen, NoYellow,
          NoOrange, SomeRed)), (Red (pk, Not_end)), (Only_st
          ((add (S (S (S Datatypes.O))) Datatypes.O), qs, (Mix (NoGreen,
          NoYellow, NoOrange, SomeRed)),
          (adapt_to_prefix qp qs Datatypes.O (Mix (NoGreen, NoYellow,
            NoOrange, SomeRed)) c0),
          (push6 (S (S Datatypes.O)) s3 s4 s2 s1 s0 s p3), s6)), c)
      | _ -> assert false (* absurd case *)))

(** val adapt_to_suffix :
    nat -> nat -> nat -> color -> coloring -> coloring **)

let adapt_to_suffix _ _ q _ = function
| G (qp, _) -> G (qp, q)
| Y (qp, _) ->
  Y (qp, (S
    (let rec add0 n m =
       match n with
       | Datatypes.O -> m
       | S p -> S (add0 p m)
     in add0 Datatypes.O q)))
| O (qp, _) ->
  O (qp, (S
    (let rec add0 n m =
       match n with
       | Datatypes.O -> m
       | S p -> S (add0 p m)
     in add0 (S Datatypes.O) q)))
| R (qp, _) ->
  R (qp, (S
    (let rec add0 n m =
       match n with
       | Datatypes.O -> m
       | S p -> S (add0 p m)
     in add0 (S (S Datatypes.O)) q)))

(** val only_of_left :
    nat -> color -> 'a1 triple -> 'a1 six_stored_triple -> 'a1 triple **)

let only_of_left _ _ tl six =
  let Triple (lvl, _, _, _, _, _, _, _, r, s, c) = tl in
  (match r with
   | Green (pk, _, cl, cr) ->
     (match s with
      | Left_end (qp, p, s0) ->
        (match c with
         | Empty _ ->
           let Coq_pair (p0, s1) = six in
           let Coq_pair (p1, s2) = p0 in
           let Coq_pair (p2, s3) = p1 in
           let Coq_pair (p3, s4) = p2 in
           let Coq_pair (s5, s6) = p3 in
           let Coq_pair (s7, s8) = two s0 in
           Triple (lvl, Only, Only, Is_end, (Mix (SomeGreen, NoYellow,
           NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
           (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Green (Only, Is_end, (Mix
           (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)))), (Only_end ((S
           (let rec add0 n m =
              match n with
              | Datatypes.O -> m
              | S p4 -> S (add0 p4 m)
            in add0 (S (S (S (S Datatypes.O)))) (S (S
                 (add (S (S (S (S (S Datatypes.O))))) qp))))),
           (inject6 (S (S (add (S (S (S (S (S Datatypes.O))))) qp)))
             (inject2 (add (S (S (S (S (S Datatypes.O))))) qp) p s7 s8) s5 s6
             s4 s3 s2 s1))), (Empty (S lvl)))
         | _ -> assert false (* absurd case *))
      | Left_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (p0, s1) = six in
        let Coq_pair (p1, s2) = p0 in
        let Coq_pair (p2, s3) = p1 in
        let Coq_pair (p3, s4) = p2 in
        let Coq_pair (s5, s6) = p3 in
        Triple (lvl, pk, Only, Not_end, (Mix (SomeGreen, NoYellow, NoOrange,
        NoRed)), cl, cr, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Green
        (pk, Not_end, cl, cr)), (Only_st (qp,
        (add (S (S (S Datatypes.O))) Datatypes.O), (Mix (SomeGreen, NoYellow,
        NoOrange, NoRed)),
        (adapt_to_suffix qp qs Datatypes.O (Mix (SomeGreen, NoYellow,
          NoOrange, NoRed)) c0), p,
        (inject6 (S (S Datatypes.O)) s0 s5 s6 s4 s3 s2 s1))), c)
      | _ -> assert false (* absurd case *))
   | Yellow (pk, cl, cr) ->
     (match s with
      | Left_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (p0, s1) = six in
        let Coq_pair (p1, s2) = p0 in
        let Coq_pair (p2, s3) = p1 in
        let Coq_pair (p3, s4) = p2 in
        let Coq_pair (s5, s6) = p3 in
        Triple (lvl, pk, Only, Not_end, (Mix (NoGreen, SomeYellow, NoOrange,
        NoRed)), cl, cr, cl, (Yellow (pk, cl, cr)), (Only_st (qp,
        (add (S (S (S Datatypes.O))) Datatypes.O), (Mix (NoGreen, SomeYellow,
        NoOrange, NoRed)),
        (adapt_to_suffix qp qs Datatypes.O (Mix (NoGreen, SomeYellow,
          NoOrange, NoRed)) c0), p,
        (inject6 (S (S Datatypes.O)) s0 s5 s6 s4 s3 s2 s1))), c)
      | _ -> assert false (* absurd case *))
   | OrangeO c0 ->
     (match s with
      | Left_st (qp, qs, _, c1, p, s0) ->
        let Coq_pair (p0, s1) = six in
        let Coq_pair (p1, s2) = p0 in
        let Coq_pair (p2, s3) = p1 in
        let Coq_pair (p3, s4) = p2 in
        let Coq_pair (s5, s6) = p3 in
        Triple (lvl, Only, Only, Not_end, (Mix (NoGreen, NoYellow,
        SomeOrange, NoRed)), c0, c0, c0, (OrangeO c0), (Only_st (qp,
        (add (S (S (S Datatypes.O))) Datatypes.O), (Mix (NoGreen, NoYellow,
        SomeOrange, NoRed)),
        (adapt_to_suffix qp qs Datatypes.O (Mix (NoGreen, NoYellow,
          SomeOrange, NoRed)) c1), p,
        (inject6 (S (S Datatypes.O)) s0 s5 s6 s4 s3 s2 s1))), c)
      | _ -> assert false (* absurd case *))
   | OrangeP cr ->
     (match s with
      | Left_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (p0, s1) = six in
        let Coq_pair (p1, s2) = p0 in
        let Coq_pair (p2, s3) = p1 in
        let Coq_pair (p3, s4) = p2 in
        let Coq_pair (s5, s6) = p3 in
        Triple (lvl, Pair, Only, Not_end, (Mix (NoGreen, NoYellow,
        SomeOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
        cr, cr, (OrangeP cr), (Only_st (qp,
        (add (S (S (S Datatypes.O))) Datatypes.O), (Mix (NoGreen, NoYellow,
        SomeOrange, NoRed)),
        (adapt_to_suffix qp qs Datatypes.O (Mix (NoGreen, NoYellow,
          SomeOrange, NoRed)) c0), p,
        (inject6 (S (S Datatypes.O)) s0 s5 s6 s4 s3 s2 s1))), c)
      | _ -> assert false (* absurd case *))
   | Red (pk, _) ->
     (match s with
      | Left_st (qp, qs, _, c0, p, s0) ->
        let Coq_pair (p0, s1) = six in
        let Coq_pair (p1, s2) = p0 in
        let Coq_pair (p2, s3) = p1 in
        let Coq_pair (p3, s4) = p2 in
        let Coq_pair (s5, s6) = p3 in
        Triple (lvl, pk, Only, Not_end, (Mix (NoGreen, NoYellow, NoOrange,
        SomeRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
        (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (NoGreen, NoYellow,
        NoOrange, SomeRed)), (Red (pk, Not_end)), (Only_st (qp,
        (add (S (S (S Datatypes.O))) Datatypes.O), (Mix (NoGreen, NoYellow,
        NoOrange, SomeRed)),
        (adapt_to_suffix qp qs Datatypes.O (Mix (NoGreen, NoYellow, NoOrange,
          SomeRed)) c0), p,
        (inject6 (S (S Datatypes.O)) s0 s5 s6 s4 s3 s2 s1))), c)
      | _ -> assert false (* absurd case *)))

(** val pop_pair_green :
    nat -> 'a1 chain -> ('a1 stored_triple, 'a1 semi_deque) prod **)

let pop_pair_green _ = function
| Pair_chain (lvl, _, _, c0, c1) ->
  let Coq_pair (s, p) =
    pop_left_green lvl
      (triple_of_chain lvl Left (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
        c0)
  in
  (match p with
   | Zero_element (_, _) -> assert false (* absurd case *)
   | Six_elements (lvl0, _, s0) ->
     Coq_pair (s, (Semi (lvl0, Only, Not_end, (Mix (SomeGreen, NoYellow,
       NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
       (chain_of_triple lvl0 Only (Mix (SomeGreen, NoYellow, NoOrange,
         NoRed))
         (only_of_right lvl0 (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) s0
           (triple_of_chain lvl0 Right (Mix (SomeGreen, NoYellow, NoOrange,
             NoRed)) c1))))))
   | Ok_pt (lvl0, _, _, c2, t) ->
     Coq_pair (s, (Semi (lvl0, Pair, Not_end, c2, (Mix (SomeGreen, NoYellow,
       NoOrange, NoRed)), (Pair_chain (lvl0, c2, (Mix (SomeGreen, NoYellow,
       NoOrange, NoRed)), (chain_of_triple lvl0 Left c2 t), c1))))))
| _ -> assert false (* absurd case *)

(** val eject_pair_green :
    nat -> 'a1 chain -> ('a1 semi_deque, 'a1 stored_triple) prod **)

let eject_pair_green _ = function
| Pair_chain (lvl, _, _, c0, c1) ->
  let Coq_pair (p, s) =
    eject_right_green lvl
      (triple_of_chain lvl Right (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
        c1)
  in
  (match p with
   | Zero_element (_, _) -> assert false (* absurd case *)
   | Six_elements (lvl0, _, s0) ->
     Coq_pair ((Semi (lvl0, Only, Not_end, (Mix (SomeGreen, NoYellow,
       NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
       (chain_of_triple lvl0 Only (Mix (SomeGreen, NoYellow, NoOrange,
         NoRed))
         (only_of_left lvl0 (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
           (triple_of_chain lvl0 Left (Mix (SomeGreen, NoYellow, NoOrange,
             NoRed)) c0) s0)))), s)
   | Ok_pt (lvl0, _, _, c2, t) ->
     Coq_pair ((Semi (lvl0, Pair, Not_end, (Mix (SomeGreen, NoYellow,
       NoOrange, NoRed)), c2, (Pair_chain (lvl0, (Mix (SomeGreen, NoYellow,
       NoOrange, NoRed)), c2, c0, (chain_of_triple lvl0 Right c2 t))))), s))
| _ -> assert false (* absurd case *)

(** val sandwich_pair_green :
    nat -> 'a1 chain -> ('a1 stored_triple, 'a1 semi_deque) sandwich **)

let sandwich_pair_green _ = function
| Pair_chain (lvl, _, _, c0, c1) ->
  let Coq_pair (s, p) =
    pop_left_green lvl
      (triple_of_chain lvl Left (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
        c0)
  in
  (match p with
   | Zero_element (_, _) -> assert false (* absurd case *)
   | Six_elements (_, _, s0) ->
     let Coq_pair (p0, s1) = s0 in
     let Coq_pair (p1, s2) = p0 in
     let Coq_pair (p2, s3) = p1 in
     let Coq_pair (p3, s4) = p2 in
     let Coq_pair (s5, s6) = p3 in
     let Coq_pair (p4, s7) =
       eject_right_green lvl
         (triple_of_chain lvl Right (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)) c1)
     in
     (match p4 with
      | Zero_element (_, _) -> assert false (* absurd case *)
      | Six_elements (lvl0, _, s8) ->
        let Coq_pair (p5, s9) = s8 in
        let Coq_pair (p6, s10) = p5 in
        let Coq_pair (p7, s11) = p6 in
        let Coq_pair (p8, s12) = p7 in
        let Coq_pair (s13, s14) = p8 in
        Sandwich (s, (Semi (lvl0, Only, Not_end, (Mix (SomeGreen, NoYellow,
        NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
        (Only_chain (lvl0, lvl0, Only, Only, Is_end, (Mix (SomeGreen,
        NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
        NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Green_chain
        ((Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
        NoYellow, NoOrange, NoRed)))), (Packet (lvl0, lvl0, Only, Only,
        Is_end, SomeGreen, NoRed, (Hole (lvl0, Only)), (Only_end ((S
        (let rec add0 n m =
           match n with
           | Datatypes.O -> m
           | S p9 -> S (add0 p9 m)
         in add0 (S (S (S (S Datatypes.O))))
              (add (S (S (S (S (S (S Datatypes.O)))))) Datatypes.O))),
        (inject6 (add (S (S (S (S (S (S Datatypes.O)))))) Datatypes.O)
          (push6 Datatypes.O s5 s6 s4 s3 s2 s1 empty) s13 s14 s12 s11 s10 s9))))),
        (Empty (S lvl0)))))), s7)
      | Ok_pt (lvl0, _, _, c2, t) ->
        Sandwich (s, (Semi (lvl0, Only, Not_end, c2, c2,
          (chain_of_triple lvl0 Only c2
            (only_of_right lvl0 c2 (Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair
              ((Coq_pair (s5, s6)), s4)), s3)), s2)), s1)) t)))), s7))
   | Ok_pt (_, _, _, c2, t) ->
     let Coq_pair (p0, s0) =
       eject_right_green lvl
         (triple_of_chain lvl Right (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)) c1)
     in
     (match p0 with
      | Zero_element (_, _) -> assert false (* absurd case *)
      | Six_elements (lvl0, _, s1) ->
        Sandwich (s, (Semi (lvl0, Only, Not_end, c2, c2,
          (chain_of_triple lvl0 Only c2 (only_of_left lvl0 c2 t s1)))), s0)
      | Ok_pt (lvl0, _, _, c3, t0) ->
        Sandwich (s, (Semi (lvl0, Pair, Not_end, c2, c3, (Pair_chain (lvl0,
          c2, c3, (chain_of_triple lvl0 Left c2 t),
          (chain_of_triple lvl0 Right c3 t0))))), s0)))
| _ -> assert false (* absurd case *)

(** val pop_green :
    nat -> kind -> 'a1 chain -> ('a1 stored_triple, 'a1 semi_deque) prod **)

let pop_green lvl pk c =
  match pk with
  | Pair -> pop_pair_green lvl c
  | Only ->
    let Coq_pair (s, p) =
      pop_only_green lvl
        (triple_of_chain lvl Only (Mix (SomeGreen, NoYellow, NoOrange,
          NoRed)) c)
    in
    (match p with
     | Zero_element (lvl0, _) ->
       Coq_pair (s, (Semi (lvl0, Only, Is_end, (Mix (SomeGreen, NoYellow,
         NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
         (Empty lvl0))))
     | Six_elements (_, _, _) -> assert false (* absurd case *)
     | Ok_pt (lvl0, _, _, c0, t) ->
       Coq_pair (s, (Semi (lvl0, Only, Not_end, c0, c0,
         (chain_of_triple lvl0 Only c0 t)))))
  | _ -> assert false (* absurd case *)

(** val eject_green :
    nat -> kind -> 'a1 chain -> ('a1 semi_deque, 'a1 stored_triple) prod **)

let eject_green lvl pk c =
  match pk with
  | Pair -> eject_pair_green lvl c
  | Only ->
    let Coq_pair (p, s) =
      eject_only_green lvl
        (triple_of_chain lvl Only (Mix (SomeGreen, NoYellow, NoOrange,
          NoRed)) c)
    in
    (match p with
     | Zero_element (lvl0, _) ->
       Coq_pair ((Semi (lvl0, Only, Is_end, (Mix (SomeGreen, NoYellow,
         NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
         (Empty lvl0))), s)
     | Six_elements (_, _, _) -> assert false (* absurd case *)
     | Ok_pt (lvl0, _, _, c0, t) ->
       Coq_pair ((Semi (lvl0, Only, Not_end, c0, c0,
         (chain_of_triple lvl0 Only c0 t))), s))
  | _ -> assert false (* absurd case *)

(** val sandwich_green :
    nat -> kind -> 'a1 chain -> ('a1 stored_triple, 'a1 semi_deque) sandwich **)

let sandwich_green lvl pk c =
  match pk with
  | Pair -> sandwich_pair_green lvl c
  | Only ->
    (match sandwich_only_green lvl
             (triple_of_chain lvl Only (Mix (SomeGreen, NoYellow, NoOrange,
               NoRed)) c) with
     | Alone a -> Alone a
     | Sandwich (a, b, a0) ->
       (match b with
        | Zero_element (lvl0, _) ->
          Sandwich (a, (Semi (lvl0, Only, Is_end, (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
            (Empty lvl0))), a0)
        | Six_elements (_, _, _) -> assert false (* absurd case *)
        | Ok_pt (lvl0, _, _, c0, t) ->
          Sandwich (a, (Semi (lvl0, Only, Not_end, c0, c0,
            (chain_of_triple lvl0 Only c0 t))), a0)))
  | _ -> assert false (* absurd case *)

(** val make_green_prefix :
    nat -> nat -> nat -> 'a1 prefix -> 'a1 prefix -> 'a1 semi_deque -> ('a1
    green_buffer, 'a1 semi_deque) prod **)

let make_green_prefix lvl q qstored p pstored child =
  let Coq_pair (p0, s) = has3p qstored pstored in
  let Coq_pair (p1, s0) = p0 in
  let Coq_pair (s1, s2) = p1 in
  (match s with
   | Coq_inl v ->
     Coq_pair ((Gbuf
       ((let rec add0 n m =
           match n with
           | Datatypes.O -> m
           | S p2 -> S (add0 p2 m)
         in add0 q (vector_length (S (S Datatypes.O)) v)),
       (Buffer.inject_vector (S (S Datatypes.O))
         (add (S (S (S Datatypes.O))) (add (S (S (S (S (S Datatypes.O))))) q))
         (inject3 (add (S (S (S (S (S Datatypes.O))))) q) p s1 s2 s0) v))),
       child)
   | Coq_inr p2 ->
     Coq_pair ((Gbuf (q,
       (inject3 (add (S (S (S (S (S Datatypes.O))))) q) p s1 s2 s0))),
       (push_semi (S lvl) (Small (lvl,
         (PeanoNat.Nat.iter (S (S (S Datatypes.O))) PeanoNat.Nat.pred qstored),
         p2)) child)))

(** val make_green_suffix :
    nat -> nat -> nat -> 'a1 semi_deque -> 'a1 suffix -> 'a1 suffix -> ('a1
    semi_deque, 'a1 green_buffer) prod **)

let make_green_suffix lvl q qstored child sstored s =
  let Coq_pair (s0, p) = has3s qstored sstored in
  (match s0 with
   | Coq_inl v ->
     let Coq_pair (p0, s1) = p in
     let Coq_pair (s2, s3) = p0 in
     Coq_pair (child, (Gbuf
     ((let rec add0 n m =
         match n with
         | Datatypes.O -> m
         | S p1 -> S (add0 p1 m)
       in add0 q (vector_length (S (S Datatypes.O)) v)),
     (Buffer.push_vector (S (S Datatypes.O))
       (add (S (S (S Datatypes.O))) (add (S (S (S (S (S Datatypes.O))))) q))
       v (push3 (add (S (S (S (S (S Datatypes.O))))) q) s2 s3 s1 s)))))
   | Coq_inr p0 ->
     let Coq_pair (p1, s1) = p in
     let Coq_pair (s2, s3) = p1 in
     Coq_pair
     ((inject_semi (S lvl) child (Small (lvl,
        (PeanoNat.Nat.iter (S (S (S Datatypes.O))) PeanoNat.Nat.pred qstored),
        p0))), (Gbuf (q,
     (push3 (add (S (S (S (S (S Datatypes.O))))) q) s2 s3 s1 s)))))

(** val extract_prefix :
    nat -> 'a1 stored_triple -> 'a1 semi_deque -> ('a1 stored_buffer, 'a1
    semi_deque) prod **)

let extract_prefix lvl stored child =
  match stored with
  | Ground _ -> assert false (* absurd case *)
  | Small (_, q, s) -> Coq_pair ((Sbuf (q, s)), child)
  | Big (_, qp, qs, pk, e, cl, cr, p, c, s) ->
    Coq_pair ((Sbuf (qp, p)),
      (concat_semi (S lvl) (Semi ((S lvl), pk, e, cl, cr, c))
        (push_semi (S lvl) (Small (lvl, qs, s)) child)))

(** val extract_suffix :
    nat -> 'a1 semi_deque -> 'a1 stored_triple -> ('a1 semi_deque, 'a1
    stored_buffer) prod **)

let extract_suffix lvl child = function
| Ground _ -> assert false (* absurd case *)
| Small (_, q, s) -> Coq_pair (child, (Sbuf (q, s)))
| Big (_, qp, qs, pk, e, cl, cr, p, c, s) ->
  Coq_pair
    ((concat_semi (S lvl) (inject_semi (S lvl) child (Small (lvl, qp, p)))
       (Semi ((S lvl), pk, e, cl, cr, c))), (Sbuf (qs, s)))

(** val ensure_green_prefix :
    nat -> nat -> kind -> 'a1 prefix -> 'a1 chain -> ('a1 green_buffer, 'a1
    semi_deque) prod **)

let ensure_green_prefix lvl q pk p child =
  let Coq_pair (s, s0) = pop_green (S lvl) pk child in
  let Coq_pair (s1, s2) = extract_prefix lvl s s0 in
  let Sbuf (q0, t) = s1 in make_green_prefix lvl q q0 p t s2

(** val ensure_green_suffix :
    nat -> nat -> kind -> 'a1 chain -> 'a1 suffix -> ('a1 semi_deque, 'a1
    green_buffer) prod **)

let ensure_green_suffix lvl q pk child s =
  let Coq_pair (s0, s1) = eject_green (S lvl) pk child in
  let Coq_pair (s2, s3) = extract_suffix lvl s0 s1 in
  let Sbuf (q0, t) = s3 in make_green_suffix lvl q q0 s2 t s

(** val ensure_green_left_obligations_obligation_2 : nat -> nat **)

let ensure_green_left_obligations_obligation_2 q =
  q

(** val ensure_green_left :
    nat -> nat -> kind -> kind -> 'a1 body -> 'a1 storage -> 'a1 chain -> 'a1
    chain **)

let ensure_green_left hlvl tlvl hk pk bd red child =
  match red with
  | Left_st (_, _, _, c, p, s) ->
    (match c with
     | R (qp, _) ->
       let Coq_pair (g, s0) =
         ensure_green_prefix tlvl (add Datatypes.O qp) pk p child
       in
       let Gbuf (q, t) = g in
       let Semi (_, pk0, e, cl, cr, c0) = s0 in
       (match e with
        | Is_end ->
          (match c0 with
           | Empty _ ->
             Only_chain (hlvl, tlvl, hk, Only, Is_end, (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
               NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
               NoRed)), (Green_chain ((Mix (SomeGreen, NoYellow, NoOrange,
               NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)))),
               (Packet (hlvl, tlvl, hk, Left, Is_end, SomeGreen, NoRed, bd,
               (Left_end ((S
               (let rec add0 n m =
                  match n with
                  | Datatypes.O -> m
                  | S p0 -> S (add0 p0 m)
                in add0 (S (S Datatypes.O)) q)), t, s)))), (Empty (S tlvl)))
           | _ -> assert false (* absurd case *))
        | Not_end ->
          Only_chain (hlvl, tlvl, hk, pk0, Not_end, (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)), cl, cr, (Green_chain (cl, cr)),
            (Packet (hlvl, tlvl, hk, Left, Not_end, SomeGreen, NoRed, bd,
            (Left_st ((add (S (S (S Datatypes.O))) q),
            (add (S (S (S Datatypes.O)))
              (ensure_green_left_obligations_obligation_2 q)), (Mix
            (SomeGreen, NoYellow, NoOrange, NoRed)), (G (q,
            (ensure_green_left_obligations_obligation_2 q))), t, s)))), c0))
     | _ -> assert false (* absurd case *))
  | _ -> assert false (* absurd case *)

(** val ensure_green_right_obligations_obligation_2 : nat -> nat **)

let ensure_green_right_obligations_obligation_2 q =
  q

(** val ensure_green_right :
    nat -> nat -> kind -> kind -> 'a1 body -> 'a1 storage -> 'a1 chain -> 'a1
    chain **)

let ensure_green_right hlvl tlvl hk pk bd red child =
  match red with
  | Right_st (_, _, _, c, p, s) ->
    (match c with
     | R (_, qs) ->
       let Coq_pair (s0, g) =
         ensure_green_suffix tlvl (add Datatypes.O qs) pk child s
       in
       let Semi (_, pk0, e, cl, cr, c0) = s0 in
       (match e with
        | Is_end ->
          (match c0 with
           | Empty _ ->
             let Gbuf (q, t) = g in
             Only_chain (hlvl, tlvl, hk, Only, Is_end, (Mix (SomeGreen,
             NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
             NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
             (Green_chain ((Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
             (SomeGreen, NoYellow, NoOrange, NoRed)))), (Packet (hlvl, tlvl,
             hk, Right, Is_end, SomeGreen, NoRed, bd, (Right_end ((S
             (let rec add0 n m =
                match n with
                | Datatypes.O -> m
                | S p0 -> S (add0 p0 m)
              in add0 (S (S Datatypes.O)) q)), p, t)))), (Empty (S tlvl)))
           | _ -> assert false (* absurd case *))
        | Not_end ->
          let Gbuf (q, t) = g in
          Only_chain (hlvl, tlvl, hk, pk0, Not_end, (Mix (SomeGreen,
          NoYellow, NoOrange, NoRed)), cl, cr, (Green_chain (cl, cr)),
          (Packet (hlvl, tlvl, hk, Right, Not_end, SomeGreen, NoRed, bd,
          (Right_st
          ((add (S (S (S Datatypes.O)))
             (ensure_green_right_obligations_obligation_2 q)),
          (add (S (S (S Datatypes.O))) q), (Mix (SomeGreen, NoYellow,
          NoOrange, NoRed)), (G
          ((ensure_green_right_obligations_obligation_2 q), q)), p, t)))), c0))
     | _ -> assert false (* absurd case *))
  | _ -> assert false (* absurd case *)

(** val make_green_only :
    nat -> nat -> kind -> nat -> nat -> 'a1 body -> 'a1 prefix -> 'a1
    semi_deque -> 'a1 prefix -> 'a1 chain **)

let make_green_only hlvl tlvl hk qp qs bd p child s =
  let Semi (_, pk, e, cl, cr, c) = child in
  (match e with
   | Is_end ->
     (match c with
      | Empty _ ->
        (match has3p8 qs s with
         | Coq_inl p0 ->
           let Coq_pair (p1, v) = p0 in
           let Coq_pair (p2, s0) = p1 in
           let Coq_pair (p3, s1) = p2 in
           let Coq_pair (p4, s2) = p3 in
           let Coq_pair (p5, s3) = p4 in
           let Coq_pair (p6, s4) = p5 in
           let Coq_pair (p7, s5) = p6 in
           let Coq_pair (s6, s7) = p7 in
           Only_chain (hlvl, tlvl, hk, Only, Is_end, (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
           (Green_chain ((Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
           (SomeGreen, NoYellow, NoOrange, NoRed)))), (Packet (hlvl, tlvl,
           hk, Only, Is_end, SomeGreen, NoRed, bd, (Only_end ((S
           (let rec add0 n m =
              match n with
              | Datatypes.O -> m
              | S p8 -> S (add0 p8 m)
            in add0
                 (let rec add0 n m =
                    match n with
                    | Datatypes.O -> m
                    | S p8 -> S (add0 p8 m)
                  in add0 (S (S (S (S (S (S Datatypes.O))))))
                       (add (S (S (S (S (S (S (S (S Datatypes.O)))))))) qp))
                 (vector_length (S (S Datatypes.O)) v))),
           (Buffer.inject_vector (S (S Datatypes.O))
             (add (S (S (S (S (S (S (S (S Datatypes.O))))))))
               (add (S (S (S (S (S (S (S (S Datatypes.O)))))))) qp))
             (inject8 (add (S (S (S (S (S (S (S (S Datatypes.O)))))))) qp) p
               s6 s7 s5 s4 s3 s2 s1 s0) v))))), (Empty (S tlvl)))
         | Coq_inr p0 ->
           let Coq_pair (t, p1) = p0 in
           Only_chain (hlvl, tlvl, hk, Only, Not_end, (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
           (Green_chain ((Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
           (SomeGreen, NoYellow, NoOrange, NoRed)))), (Packet (hlvl, tlvl,
           hk, Only, Not_end, SomeGreen, NoRed, bd, (Only_st
           ((add (S (S (S Datatypes.O))) qp),
           (add (S (S (S Datatypes.O)))
             (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S Datatypes.O))))))))
               PeanoNat.Nat.pred (add (S (S (S (S (S Datatypes.O))))) qs))),
           (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (G (qp,
           (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S Datatypes.O))))))))
             PeanoNat.Nat.pred (add (S (S (S (S (S Datatypes.O))))) qs)))),
           p, p1)))), (single_chain (S tlvl) (Small (tlvl, Datatypes.O, t)))))
      | _ -> assert false (* absurd case *))
   | Not_end ->
     Only_chain (hlvl, tlvl, hk, pk, Not_end, (Mix (SomeGreen, NoYellow,
       NoOrange, NoRed)), cl, cr, (Green_chain (cl, cr)), (Packet (hlvl,
       tlvl, hk, Only, Not_end, SomeGreen, NoRed, bd, (Only_st
       ((add (S (S (S Datatypes.O))) qp), (add (S (S (S Datatypes.O))) qs),
       (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (G (qp, qs)), p, s)))),
       c))

(** val ensure_green_only :
    nat -> nat -> kind -> kind -> 'a1 body -> 'a1 storage -> 'a1 chain -> 'a1
    chain **)

let ensure_green_only hlvl tlvl hk pk bd red child =
  match red with
  | Only_st (_, _, _, c, p, s) ->
    (match c with
     | R (qp, qs) ->
       (match has8 (add Datatypes.O qp) p with
        | Coq_inl p0 ->
          let Coq_pair (p1, v) = p0 in
          let Coq_pair (p2, s0) = p1 in
          let Coq_pair (p3, s1) = p2 in
          let Coq_pair (p4, s2) = p3 in
          let Coq_pair (s3, s4) = p4 in
          (match has8 (add Datatypes.O qs) s with
           | Coq_inl p5 ->
             let Coq_pair (p6, v0) = p5 in
             let Coq_pair (p7, s5) = p6 in
             let Coq_pair (p8, s6) = p7 in
             let Coq_pair (p9, s7) = p8 in
             let Coq_pair (s8, s9) = p9 in
             (match sandwich_green (S tlvl) pk child with
              | Alone a ->
                (match a with
                 | Ground _ -> assert false (* absurd case *)
                 | Small (_, q, s10) ->
                   Only_chain (hlvl, tlvl, hk, Only, Is_end, (Mix (SomeGreen,
                     NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
                     NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
                     NoRed)), (Green_chain ((Mix (SomeGreen, NoYellow,
                     NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
                     NoRed)))), (Packet (hlvl, tlvl, hk, Only, Is_end,
                     SomeGreen, NoRed, bd, (Only_end ((S
                     (let rec add0 n m =
                        match n with
                        | Datatypes.O -> m
                        | S p10 -> S (add0 p10 m)
                      in add0
                           (let rec add0 n m =
                              match n with
                              | Datatypes.O -> m
                              | S p10 -> S (add0 p10 m)
                            in add0 (S (S (S Datatypes.O)))
                                 (add
                                   (add (S (S (S (S (S Datatypes.O)))))
                                     (add (S (S (S Datatypes.O))) q))
                                   (vector_length (S (S Datatypes.O)) v)))
                           (vector_length (S (S Datatypes.O)) v0))),
                     (inject_5vector (S (S Datatypes.O))
                       (add
                         (add (S (S (S (S (S Datatypes.O)))))
                           (add (S (S (S Datatypes.O))) q))
                         (vector_length (S (S Datatypes.O)) v))
                       (push_5vector (S (S Datatypes.O))
                         (add (S (S (S Datatypes.O))) q) s3 s4 s2 s1 s0 v s10)
                       s8 s9 s7 s6 s5 v0))))), (Empty (S tlvl)))
                 | Big (_, qp0, qs0, pk0, e, cl, cr, p10, c0, s10) ->
                   make_green_only hlvl tlvl hk
                     (let rec add0 n m =
                        match n with
                        | Datatypes.O -> m
                        | S p11 -> S (add0 p11 m)
                      in add0 qp0 (vector_length (S (S Datatypes.O)) v))
                     (let rec add0 n m =
                        match n with
                        | Datatypes.O -> m
                        | S p11 -> S (add0 p11 m)
                      in add0 qs0 (vector_length (S (S Datatypes.O)) v0)) bd
                     (push_5vector (S (S Datatypes.O))
                       (add (S (S (S Datatypes.O))) qp0) s3 s4 s2 s1 s0 v p10)
                     (Semi ((S tlvl), pk0, e, cl, cr, c0))
                     (inject_5vector (S (S Datatypes.O))
                       (add (S (S (S Datatypes.O))) qs0) s10 s8 s9 s7 s6 s5
                       v0))
              | Sandwich (a, b, a0) ->
                let Coq_pair (s10, s11) = extract_prefix tlvl a b in
                let Sbuf (q, t) = s10 in
                let Coq_pair (s12, s13) = extract_suffix tlvl s11 a0 in
                let Sbuf (q0, t0) = s13 in
                make_green_only hlvl tlvl hk
                  (let rec add0 n m =
                     match n with
                     | Datatypes.O -> m
                     | S p10 -> S (add0 p10 m)
                   in add0 q (vector_length (S (S Datatypes.O)) v))
                  (let rec add0 n m =
                     match n with
                     | Datatypes.O -> m
                     | S p10 -> S (add0 p10 m)
                   in add0 q0 (vector_length (S (S Datatypes.O)) v0)) bd
                  (push_5vector (S (S Datatypes.O))
                    (add (S (S (S Datatypes.O))) q) s3 s4 s2 s1 s0 v t) s12
                  (inject_5vector (S (S Datatypes.O))
                    (add (S (S (S Datatypes.O))) q0) t0 s8 s9 s7 s6 s5 v0))
           | Coq_inr p5 ->
             let Coq_pair (g, s5) =
               ensure_green_prefix tlvl (add Datatypes.O qp) pk p child
             in
             let Gbuf (q, t) = g in
             make_green_only hlvl tlvl hk q
               (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S Datatypes.O))))))))
                 PeanoNat.Nat.pred
                 (add (S (S (S (S (S Datatypes.O))))) (add Datatypes.O qs)))
               bd t s5 p5)
        | Coq_inr p0 ->
          (match has8 (add Datatypes.O qs) s with
           | Coq_inl _ ->
             let Coq_pair (s0, g) =
               ensure_green_suffix tlvl (add Datatypes.O qs) pk child s
             in
             let Gbuf (q, t) = g in
             make_green_only hlvl tlvl hk
               (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S Datatypes.O))))))))
                 PeanoNat.Nat.pred
                 (add (S (S (S (S (S Datatypes.O))))) (add Datatypes.O qp)))
               q bd p0 s0 t
           | Coq_inr p1 ->
             Only_chain (hlvl, tlvl, hk, pk, Not_end, (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
               NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
               NoRed)), (Green_chain ((Mix (SomeGreen, NoYellow, NoOrange,
               NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)))),
               (Packet (hlvl, tlvl, hk, Only, Not_end, SomeGreen, NoRed, bd,
               (Only_st
               ((add (S (S (S Datatypes.O)))
                  (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S
                    Datatypes.O)))))))) PeanoNat.Nat.pred
                    (add (S (S (S (S (S Datatypes.O))))) (add Datatypes.O qp)))),
               (add (S (S (S Datatypes.O)))
                 (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S
                   Datatypes.O)))))))) PeanoNat.Nat.pred
                   (add (S (S (S (S (S Datatypes.O))))) (add Datatypes.O qs)))),
               (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (G
               ((PeanoNat.Nat.iter (S (S (S (S (S (S (S (S
                  Datatypes.O)))))))) PeanoNat.Nat.pred
                  (add (S (S (S (S (S Datatypes.O))))) (add Datatypes.O qp))),
               (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S Datatypes.O))))))))
                 PeanoNat.Nat.pred
                 (add (S (S (S (S (S Datatypes.O))))) (add Datatypes.O qs))))),
               p0, p1)))), child)))
     | _ -> assert false (* absurd case *))
  | _ -> assert false (* absurd case *)

(** val ensure_green_obligations_obligation_4 : nat -> nat **)

let ensure_green_obligations_obligation_4 qs3 =
  qs3

(** val ensure_green_obligations_obligation_6 : nat -> nat **)

let ensure_green_obligations_obligation_6 qs3 =
  qs3

(** val ensure_green :
    nat -> kind -> kind -> ending -> color -> color -> 'a1 chain -> 'a1 chain **)

let rec ensure_green _ _ _ _ _ _ = function
| Empty lvl -> Empty lvl
| Only_chain (hlvl, tlvl, k, pk, e, _, _, _, c0, p, c1) ->
  (match c0 with
   | Green_chain (cl, cr) ->
     Only_chain (hlvl, tlvl, k, pk, e, (Mix (SomeGreen, NoYellow, NoOrange,
       NoRed)), cl, cr, (Green_chain (cl, cr)), p, c1)
   | Red_chain ->
     let Packet (hlvl0, tlvl0, hk, _, _, _, _, b, s) = p in
     (match s with
      | Only_st (_, _, _, c2, p0, s0) ->
        (match c2 with
         | R (qp, qs) ->
           ensure_green_only hlvl0 tlvl0 hk pk b (Only_st
             ((add Datatypes.O qp), (add Datatypes.O qs), (Mix (NoGreen,
             NoYellow, NoOrange, SomeRed)), (R (qp, qs)), p0, s0)) c1
         | _ -> assert false (* absurd case *))
      | Left_st (_, _, _, c2, p0, s0) ->
        (match c2 with
         | R (qp, qs) ->
           ensure_green_left hlvl0 tlvl0 hk pk b (Left_st
             ((add Datatypes.O qp),
             (add Datatypes.O (ensure_green_obligations_obligation_4 qs)),
             (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (R (qp,
             (ensure_green_obligations_obligation_4 qs))), p0, s0)) c1
         | _ -> assert false (* absurd case *))
      | Right_st (_, _, _, c2, p0, s0) ->
        (match c2 with
         | R (_, qs) ->
           ensure_green_right hlvl0 tlvl0 hk pk b (Right_st
             ((add Datatypes.O (ensure_green_obligations_obligation_6 qs)),
             (add Datatypes.O qs), (Mix (NoGreen, NoYellow, NoOrange,
             SomeRed)), (R ((ensure_green_obligations_obligation_6 qs), qs)),
             p0, s0)) c1
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *)))
| Pair_chain (lvl, cl, cr, c0, c1) ->
  Pair_chain (lvl, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
    (SomeGreen, NoYellow, NoOrange, NoRed)),
    (ensure_green lvl Only Left Not_end cl cl c0),
    (Obj.magic ensure_green lvl Only Right Not_end cr cr c1))
