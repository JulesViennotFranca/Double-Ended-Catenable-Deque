open Datatypes
open Nat
open Buffer
open Types

(** val push_only_triple :
    nat -> nat -> kind -> color -> 'a1 stored_triple -> 'a1 only_triple ->
    'a1 only_triple **)

let push_only_triple _ _ _ _ x = function
| Hole (_, _) -> assert false (* absurd case *)
| Small (lvl, _, _, _, p, s, s0) ->
  (match s0 with
   | Only_small_sizes q ->
     Small (lvl, (S (S q)), O, Only, (push (S q) x p), s, (Only_small_sizes
       (S q)))
   | _ -> assert false (* absurd case *))
| Green (lvl, _, _, _, g, r, p, n, s, b) ->
  (match b with
   | Only_big_sizes (qp, qs) ->
     Green (lvl, (S (add (S (S (S (S (S (S (S (S O)))))))) qp)),
       (add (S (S (S (S (S (S (S (S O)))))))) qs), Only, g, r,
       (push (add (S (S (S (S (S (S (S (S O)))))))) qp) x p), n, s,
       (Only_big_sizes ((S
       (let rec add0 n0 m =
          match n0 with
          | O -> m
          | S p0 -> S (add0 p0 m)
        in add0 O qp)), qs)))
   | _ -> assert false (* absurd case *))
| Yellow (lvl, len, _, _, _, k2, p, p0, s, b) ->
  (match b with
   | Only_big_sizes (qp, qs) ->
     Yellow (lvl, len, (S (add (S (S (S (S (S (S (S O))))))) qp)),
       (add (S (S (S (S (S (S (S O))))))) qs), Only, k2,
       (push (add (S (S (S (S (S (S (S O))))))) qp) x p), p0, s,
       (Only_big_sizes ((S
       (let rec add0 n m =
          match n with
          | O -> m
          | S p1 -> S (add0 p1 m)
        in add0 O qp)), qs)))
   | _ -> assert false (* absurd case *))
| Orange (lvl, len, _, _, _, k2, p, p0, s, b) ->
  (match b with
   | Only_big_sizes (qp, qs) ->
     Orange (lvl, len, (S (add (S (S (S (S (S (S O)))))) qp)),
       (add (S (S (S (S (S (S O)))))) qs), Only, k2,
       (push (add (S (S (S (S (S (S O)))))) qp) x p), p0, s, (Only_big_sizes
       ((S
       (let rec add0 n m =
          match n with
          | O -> m
          | S p1 -> S (add0 p1 m)
        in add0 O qp)), qs)))
   | _ -> assert false (* absurd case *))
| Red (lvl, _, _, _, p, n, s, b) ->
  (match b with
   | Only_big_sizes (qp, qs) ->
     Red (lvl, (S (add (S (S (S (S (S O))))) qp)),
       (add (S (S (S (S (S O))))) qs), Only,
       (push (add (S (S (S (S (S O))))) qp) x p), n, s, (Only_big_sizes ((S
       (let rec add0 n0 m =
          match n0 with
          | O -> m
          | S p0 -> S (add0 p0 m)
        in add0 O qp)), qs)))
   | _ -> assert false (* absurd case *))

(** val inject_only_triple :
    nat -> nat -> kind -> color -> 'a1 only_triple -> 'a1 stored_triple ->
    'a1 only_triple **)

let inject_only_triple _ _ _ _ t x =
  match t with
  | Hole (_, _) -> assert false (* absurd case *)
  | Small (lvl, _, _, _, p, s, s0) ->
    (match s0 with
     | Only_small_sizes q ->
       Small (lvl, (S (S q)), O, Only, (inject (S q) p x), s,
         (Only_small_sizes (S q)))
     | _ -> assert false (* absurd case *))
  | Green (lvl, _, _, _, g, r, p, n, s, b) ->
    (match b with
     | Only_big_sizes (qp, qs) ->
       Green (lvl, (add (S (S (S (S (S (S (S (S O)))))))) qp), (S
         (add (S (S (S (S (S (S (S (S O)))))))) qs)), Only, g, r, p, n,
         (inject (add (S (S (S (S (S (S (S (S O)))))))) qs) s x),
         (Only_big_sizes (qp, (S
         (let rec add0 n0 m =
            match n0 with
            | O -> m
            | S p0 -> S (add0 p0 m)
          in add0 O qs)))))
     | _ -> assert false (* absurd case *))
  | Yellow (lvl, len, _, _, _, k2, p, p0, s, b) ->
    (match b with
     | Only_big_sizes (qp, qs) ->
       Yellow (lvl, len, (add (S (S (S (S (S (S (S O))))))) qp), (S
         (add (S (S (S (S (S (S (S O))))))) qs)), Only, k2, p, p0,
         (inject (add (S (S (S (S (S (S (S O))))))) qs) s x), (Only_big_sizes
         (qp, (S
         (let rec add0 n m =
            match n with
            | O -> m
            | S p1 -> S (add0 p1 m)
          in add0 O qs)))))
     | _ -> assert false (* absurd case *))
  | Orange (lvl, len, _, _, _, k2, p, p0, s, b) ->
    (match b with
     | Only_big_sizes (qp, qs) ->
       Orange (lvl, len, (add (S (S (S (S (S (S O)))))) qp), (S
         (add (S (S (S (S (S (S O)))))) qs)), Only, k2, p, p0,
         (inject (add (S (S (S (S (S (S O)))))) qs) s x), (Only_big_sizes
         (qp, (S
         (let rec add0 n m =
            match n with
            | O -> m
            | S p1 -> S (add0 p1 m)
          in add0 O qs)))))
     | _ -> assert false (* absurd case *))
  | Red (lvl, _, _, _, p, n, s, b) ->
    (match b with
     | Only_big_sizes (qp, qs) ->
       Red (lvl, (add (S (S (S (S (S O))))) qp), (S
         (add (S (S (S (S (S O))))) qs)), Only, p, n,
         (inject (add (S (S (S (S (S O))))) qs) s x), (Only_big_sizes (qp, (S
         (let rec add0 n0 m =
            match n0 with
            | O -> m
            | S p0 -> S (add0 p0 m)
          in add0 O qs)))))
     | _ -> assert false (* absurd case *))

(** val push_only_path :
    nat -> color -> 'a1 stored_triple -> 'a1 path -> 'a1 path **)

let push_only_path _ _ x = function
| Children (_, _, nlvl, _, _, _, g, _, _, r, t, t0) ->
  (match t with
   | Hole (_, _) ->
     Children (nlvl, O, nlvl, Coq_true, Only, Only, g, SomeYellow,
       SomeOrange, r, (Hole (nlvl, Only)),
       (push_only_triple nlvl O Only (Mix (g, NoYellow, NoOrange, r)) x t0))
   | Yellow (lvl, len, qp, qs, _, k2, p0, p1, s, b) ->
     Children (lvl, (S len), (S (add len lvl)), Coq_false, Only, k2, g,
       SomeYellow, NoOrange, r,
       (push_only_triple lvl (S len) k2 (Mix (NoGreen, SomeYellow, NoOrange,
         NoRed)) x (Yellow (lvl, len, qp, qs, Only, k2, p0, p1, s, b))), t0)
   | Orange (lvl, len, qp, qs, _, k2, p0, p1, s, b) ->
     Children (lvl, (S len), (S (add len lvl)), Coq_false, Only, k2, g,
       NoYellow, SomeOrange, r,
       (push_only_triple lvl (S len) k2 (Mix (NoGreen, NoYellow, SomeOrange,
         NoRed)) x (Orange (lvl, len, qp, qs, Only, k2, p0, p1, s, b))), t0)
   | _ -> assert false (* absurd case *))

(** val inject_only_path :
    nat -> color -> 'a1 path -> 'a1 stored_triple -> 'a1 path **)

let inject_only_path _ _ p x =
  let Children (_, _, nlvl, _, _, _, g, _, _, r, t, t0) = p in
  (match t with
   | Hole (_, _) ->
     Children (nlvl, O, nlvl, Coq_true, Only, Only, g, SomeYellow,
       SomeOrange, r, (Hole (nlvl, Only)),
       (inject_only_triple nlvl O Only (Mix (g, NoYellow, NoOrange, r)) t0 x))
   | Yellow (lvl, len, qp, qs, _, k2, p0, p1, s, b) ->
     Children (lvl, (S len), (S (add len lvl)), Coq_false, Only, k2, g,
       SomeYellow, NoOrange, r,
       (inject_only_triple lvl (S len) k2 (Mix (NoGreen, SomeYellow,
         NoOrange, NoRed)) (Yellow (lvl, len, qp, qs, Only, k2, p0, p1, s,
         b)) x), t0)
   | Orange (lvl, len, qp, qs, _, k2, p0, p1, s, b) ->
     Children (lvl, (S len), (S (add len lvl)), Coq_false, Only, k2, g,
       NoYellow, SomeOrange, r,
       (inject_only_triple lvl (S len) k2 (Mix (NoGreen, NoYellow,
         SomeOrange, NoRed)) (Orange (lvl, len, qp, qs, Only, k2, p0, p1, s,
         b)) x), t0)
   | _ -> assert false (* absurd case *))

(** val push_left_triple :
    nat -> nat -> kind -> color -> 'a1 stored_triple -> 'a1 left_triple ->
    'a1 left_triple **)

let push_left_triple _ _ _ _ x = function
| Hole (_, _) -> assert false (* absurd case *)
| Small (lvl, _, _, _, p, s, s0) ->
  (match s0 with
   | Left_small_sizes q ->
     Small (lvl, (S (add (S (S (S (S (S O))))) q)), (S (S O)), Left,
       (push (add (S (S (S (S (S O))))) q) x p), s, (Left_small_sizes (S
       (let rec add0 n m =
          match n with
          | O -> m
          | S p0 -> S (add0 p0 m)
        in add0 O q))))
   | _ -> assert false (* absurd case *))
| Green (lvl, _, _, _, g, r, p, n, s, b) ->
  (match b with
   | Left_big_sizes q ->
     Green (lvl, (S (add (S (S (S (S (S (S (S (S O)))))))) q)), (S (S O)),
       Left, g, r, (push (add (S (S (S (S (S (S (S (S O)))))))) q) x p), n,
       s, (Left_big_sizes (S
       (let rec add0 n0 m =
          match n0 with
          | O -> m
          | S p0 -> S (add0 p0 m)
        in add0 O q))))
   | _ -> assert false (* absurd case *))
| Yellow (lvl, len, _, _, _, k2, p, p0, s, b) ->
  (match b with
   | Left_big_sizes q ->
     Yellow (lvl, len, (S (add (S (S (S (S (S (S (S O))))))) q)), (S (S O)),
       Left, k2, (push (add (S (S (S (S (S (S (S O))))))) q) x p), p0, s,
       (Left_big_sizes (S
       (let rec add0 n m =
          match n with
          | O -> m
          | S p1 -> S (add0 p1 m)
        in add0 O q))))
   | _ -> assert false (* absurd case *))
| Orange (lvl, len, _, _, _, k2, p, p0, s, b) ->
  (match b with
   | Left_big_sizes q ->
     Orange (lvl, len, (S (add (S (S (S (S (S (S O)))))) q)), (S (S O)),
       Left, k2, (push (add (S (S (S (S (S (S O)))))) q) x p), p0, s,
       (Left_big_sizes (S
       (let rec add0 n m =
          match n with
          | O -> m
          | S p1 -> S (add0 p1 m)
        in add0 O q))))
   | _ -> assert false (* absurd case *))
| Red (lvl, _, _, _, p, n, s, b) ->
  (match b with
   | Left_big_sizes q ->
     Red (lvl, (S (add (S (S (S (S (S O))))) q)), (S (S O)), Left,
       (push (add (S (S (S (S (S O))))) q) x p), n, s, (Left_big_sizes (S
       (let rec add0 n0 m =
          match n0 with
          | O -> m
          | S p0 -> S (add0 p0 m)
        in add0 O q))))
   | _ -> assert false (* absurd case *))

(** val inject_right_triple :
    nat -> nat -> kind -> color -> 'a1 right_triple -> 'a1 stored_triple ->
    'a1 right_triple **)

let inject_right_triple _ _ _ _ t x =
  match t with
  | Hole (_, _) -> assert false (* absurd case *)
  | Small (lvl, _, _, _, p, s, s0) ->
    (match s0 with
     | Right_small_sizes q ->
       Small (lvl, (S (S O)), (S (add (S (S (S (S (S O))))) q)), Right, p,
         (inject (add (S (S (S (S (S O))))) q) s x), (Right_small_sizes (S
         (let rec add0 n m =
            match n with
            | O -> m
            | S p0 -> S (add0 p0 m)
          in add0 O q))))
     | _ -> assert false (* absurd case *))
  | Green (lvl, _, _, _, g, r, p, n, s, b) ->
    (match b with
     | Right_big_sizes q ->
       Green (lvl, (S (S O)), (S (add (S (S (S (S (S (S (S (S O)))))))) q)),
         Right, g, r, p, n,
         (inject (add (S (S (S (S (S (S (S (S O)))))))) q) s x),
         (Right_big_sizes (S
         (let rec add0 n0 m =
            match n0 with
            | O -> m
            | S p0 -> S (add0 p0 m)
          in add0 O q))))
     | _ -> assert false (* absurd case *))
  | Yellow (lvl, len, _, _, _, k2, p, p0, s, b) ->
    (match b with
     | Right_big_sizes q ->
       Yellow (lvl, len, (S (S O)), (S
         (add (S (S (S (S (S (S (S O))))))) q)), Right, k2, p, p0,
         (inject (add (S (S (S (S (S (S (S O))))))) q) s x), (Right_big_sizes
         (S
         (let rec add0 n m =
            match n with
            | O -> m
            | S p1 -> S (add0 p1 m)
          in add0 O q))))
     | _ -> assert false (* absurd case *))
  | Orange (lvl, len, _, _, _, k2, p, p0, s, b) ->
    (match b with
     | Right_big_sizes q ->
       Orange (lvl, len, (S (S O)), (S (add (S (S (S (S (S (S O)))))) q)),
         Right, k2, p, p0, (inject (add (S (S (S (S (S (S O)))))) q) s x),
         (Right_big_sizes (S
         (let rec add0 n m =
            match n with
            | O -> m
            | S p1 -> S (add0 p1 m)
          in add0 O q))))
     | _ -> assert false (* absurd case *))
  | Red (lvl, _, _, _, p, n, s, b) ->
    (match b with
     | Right_big_sizes q ->
       Red (lvl, (S (S O)), (S (add (S (S (S (S (S O))))) q)), Right, p, n,
         (inject (add (S (S (S (S (S O))))) q) s x), (Right_big_sizes (S
         (let rec add0 n0 m =
            match n0 with
            | O -> m
            | S p0 -> S (add0 p0 m)
          in add0 O q))))
     | _ -> assert false (* absurd case *))

(** val push_left_path :
    nat -> color -> 'a1 stored_triple -> 'a1 path -> 'a1 path **)

let push_left_path _ _ x = function
| Children (_, _, nlvl, _, _, _, g, _, _, r, t, t0) ->
  (match t with
   | Hole (_, _) ->
     Children (nlvl, O, nlvl, Coq_true, Left, Left, g, SomeYellow,
       SomeOrange, r, (Hole (nlvl, Left)),
       (push_left_triple nlvl O Left (Mix (g, NoYellow, NoOrange, r)) x t0))
   | Yellow (lvl, len, qp, qs, _, k2, p0, p1, s, b) ->
     Children (lvl, (S len), (S (add len lvl)), Coq_false, Left, k2, g,
       SomeYellow, NoOrange, r,
       (push_left_triple lvl (S len) k2 (Mix (NoGreen, SomeYellow, NoOrange,
         NoRed)) x (Yellow (lvl, len, qp, qs, Left, k2, p0, p1, s, b))), t0)
   | Orange (lvl, len, qp, qs, _, k2, p0, p1, s, b) ->
     Children (lvl, (S len), (S (add len lvl)), Coq_false, Left, k2, g,
       NoYellow, SomeOrange, r,
       (push_left_triple lvl (S len) k2 (Mix (NoGreen, NoYellow, SomeOrange,
         NoRed)) x (Orange (lvl, len, qp, qs, Left, k2, p0, p1, s, b))), t0)
   | _ -> assert false (* absurd case *))

(** val inject_right_path :
    nat -> color -> 'a1 path -> 'a1 stored_triple -> 'a1 path **)

let inject_right_path _ _ p x =
  let Children (_, _, nlvl, _, _, _, g, _, _, r, t, t0) = p in
  (match t with
   | Hole (_, _) ->
     Children (nlvl, O, nlvl, Coq_true, Right, Right, g, SomeYellow,
       SomeOrange, r, (Hole (nlvl, Right)),
       (inject_right_triple nlvl O Right (Mix (g, NoYellow, NoOrange, r)) t0
         x))
   | Yellow (lvl, len, qp, qs, _, k2, p0, p1, s, b) ->
     Children (lvl, (S len), (S (add len lvl)), Coq_false, Right, k2, g,
       SomeYellow, NoOrange, r,
       (inject_right_triple lvl (S len) k2 (Mix (NoGreen, SomeYellow,
         NoOrange, NoRed)) (Yellow (lvl, len, qp, qs, Right, k2, p0, p1, s,
         b)) x), t0)
   | Orange (lvl, len, qp, qs, _, k2, p0, p1, s, b) ->
     Children (lvl, (S len), (S (add len lvl)), Coq_false, Right, k2, g,
       NoYellow, SomeOrange, r,
       (inject_right_triple lvl (S len) k2 (Mix (NoGreen, NoYellow,
         SomeOrange, NoRed)) (Orange (lvl, len, qp, qs, Right, k2, p0, p1, s,
         b)) x), t0)
   | _ -> assert false (* absurd case *))

(** val push_ne_cdeque :
    nat -> color -> 'a1 stored_triple -> 'a1 non_empty_cdeque -> 'a1
    non_empty_cdeque **)

let push_ne_cdeque _ _ x = function
| Only_path (lvl, g, r, p) ->
  Only_path (lvl, g, r,
    (push_only_path lvl (Mix (g, NoYellow, NoOrange, r)) x p))
| Pair_green (lvl, p, p0) ->
  Pair_green (lvl,
    (push_left_path lvl (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) x p), p0)
| Pair_red (lvl, cl, cr, p, p0) ->
  Pair_red (lvl, cl, cr, (push_left_path lvl cl x p), p0)

(** val inject_ne_cdeque :
    nat -> color -> 'a1 non_empty_cdeque -> 'a1 stored_triple -> 'a1
    non_empty_cdeque **)

let inject_ne_cdeque _ _ cd x =
  match cd with
  | Only_path (lvl, g, r, p) ->
    Only_path (lvl, g, r,
      (inject_only_path lvl (Mix (g, NoYellow, NoOrange, r)) p x))
  | Pair_green (lvl, p, p0) ->
    Pair_green (lvl, p,
      (inject_right_path lvl (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) p0
        x))
  | Pair_red (lvl, cl, cr, p, p0) ->
    Pair_red (lvl, cl, cr, p, (inject_right_path lvl cr p0 x))

(** val single_triple : nat -> 'a1 stored_triple -> 'a1 triple **)

let single_triple lvl x =
  Small (lvl, (S O), O, Only, (single x), empty, (Only_small_sizes O))

(** val only_single : nat -> 'a1 stored_triple -> 'a1 non_empty_cdeque **)

let only_single lvl x =
  Only_path (lvl, SomeGreen, NoRed, (Children (lvl, O, lvl, Coq_true, Only,
    Only, SomeGreen, SomeYellow, SomeOrange, NoRed, (Hole (lvl, Only)),
    (single_triple lvl x))))

(** val single : nat -> 'a1 stored_triple -> 'a1 cdeque **)

let single lvl x =
  NonEmpty (lvl, SomeGreen, NoRed, (only_single lvl x))

(** val push_cdeque :
    nat -> color -> 'a1 stored_triple -> 'a1 cdeque -> 'a1 cdeque **)

let push_cdeque _ _ x = function
| Empty lvl -> single lvl x
| NonEmpty (lvl, g, r, n) ->
  NonEmpty (lvl, g, r,
    (push_ne_cdeque lvl (Mix (g, NoYellow, NoOrange, r)) x n))

(** val inject_cdeque :
    nat -> color -> 'a1 cdeque -> 'a1 stored_triple -> 'a1 cdeque **)

let inject_cdeque _ _ cd x =
  match cd with
  | Empty lvl -> single lvl x
  | NonEmpty (lvl, g, r, n) ->
    NonEmpty (lvl, g, r,
      (inject_ne_cdeque lvl (Mix (g, NoYellow, NoOrange, r)) n x))

(** val push_semi : nat -> 'a1 stored_triple -> 'a1 sdeque -> 'a1 sdeque **)

let push_semi lvl x = function
| Sd (c, c0) -> Sd (c, (push_cdeque lvl c x c0))

(** val inject_semi : nat -> 'a1 sdeque -> 'a1 stored_triple -> 'a1 sdeque **)

let inject_semi lvl sd x =
  let Sd (c, c0) = sd in Sd (c, (inject_cdeque lvl c c0 x))

(** val push_vector :
    nat -> nat -> color -> 'a1 stored_triple vector -> 'a1 cdeque -> 'a1
    cdeque **)

let push_vector lvl _ c v cd =
  match v with
  | V0 _ -> cd
  | V1 (_, s) -> push_cdeque lvl c s cd
  | V2 (_, s, s0) -> push_cdeque lvl c s (push_cdeque lvl c s0 cd)
  | V3 (_, s, s0, s1) ->
    push_cdeque lvl c s (push_cdeque lvl c s0 (push_cdeque lvl c s1 cd))
  | V4 (_, s, s0, s1, s2) ->
    push_cdeque lvl c s
      (push_cdeque lvl c s0 (push_cdeque lvl c s1 (push_cdeque lvl c s2 cd)))
  | V5 (_, s, s0, s1, s2, s3) ->
    push_cdeque lvl c s
      (push_cdeque lvl c s0
        (push_cdeque lvl c s1
          (push_cdeque lvl c s2 (push_cdeque lvl c s3 cd))))
  | V6 (_, s, s0, s1, s2, s3, s4) ->
    push_cdeque lvl c s
      (push_cdeque lvl c s0
        (push_cdeque lvl c s1
          (push_cdeque lvl c s2
            (push_cdeque lvl c s3 (push_cdeque lvl c s4 cd)))))

(** val inject_vector :
    nat -> nat -> color -> 'a1 cdeque -> 'a1 stored_triple vector -> 'a1
    cdeque **)

let inject_vector lvl _ c cd = function
| V0 _ -> cd
| V1 (_, s) -> inject_cdeque lvl c cd s
| V2 (_, s, s0) -> inject_cdeque lvl c (inject_cdeque lvl c cd s) s0
| V3 (_, s, s0, s1) ->
  inject_cdeque lvl c (inject_cdeque lvl c (inject_cdeque lvl c cd s) s0) s1
| V4 (_, s, s0, s1, s2) ->
  inject_cdeque lvl c
    (inject_cdeque lvl c (inject_cdeque lvl c (inject_cdeque lvl c cd s) s0)
      s1) s2
| V5 (_, s, s0, s1, s2, s3) ->
  inject_cdeque lvl c
    (inject_cdeque lvl c
      (inject_cdeque lvl c
        (inject_cdeque lvl c (inject_cdeque lvl c cd s) s0) s1) s2) s3
| V6 (_, s, s0, s1, s2, s3, s4) ->
  inject_cdeque lvl c
    (inject_cdeque lvl c
      (inject_cdeque lvl c
        (inject_cdeque lvl c
          (inject_cdeque lvl c (inject_cdeque lvl c cd s) s0) s1) s2) s3) s4

(** val to_pref_left :
    nat -> color -> 'a1 non_empty_cdeque -> 'a1 pref_left **)

let to_pref_left _ _ = function
| Only_path (_, _, _, p) ->
  let Children (lvl, len, _, is_hole, _, k2, g, y, o, r, t, t0) = p in
  Pref_left (len, (add len lvl), k2, g, r, (Only_child (lvl, len, is_hole,
  k2, y, o, Preferred_left, t)), t0)
| Pair_green (_, p, p0) ->
  let Children (lvl, len, _, is_hole, _, k2, _, y, o, _, t, t0) = p in
  Pref_left (len, (add len lvl), k2, SomeGreen, NoRed, (Left_child (lvl, len,
  is_hole, k2, y, o, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), t, p0)),
  t0)
| Pair_red (_, _, cr, p, p0) ->
  let Children (lvl, len, _, is_hole, _, k2, g, y, o, r, t, t0) = p in
  Pref_left (len, (add len lvl), k2, g, r, (Left_child (lvl, len, is_hole,
  k2, y, o, cr, t, p0)), t0)

(** val to_pref_right :
    nat -> nat -> nat -> kind -> 'a1 packet -> 'a1 triple -> 'a1 pref_right **)

let to_pref_right _ _ _ _ pkt t =
  match pkt with
  | Only_child (lvl, len, is_hole, k, y, o, _, t0) ->
    Pref_right (len, (add len lvl), k, SomeGreen, NoRed, (Only_child (lvl,
      len, is_hole, k, y, o, Preferred_right, t0)), t)
  | Left_child (_, len, is_hole, k, y, o, _, t0, p) ->
    let Children (lvl, len0, _, is_hole0, _, k2, g, y0, o0, r, t1, t2) = p in
    Pref_right (len0, (add len0 lvl), k2, g, r, (Right_child (lvl, len0,
    is_hole0, k2, y0, o0, (Children (lvl, len, (add len lvl), is_hole, Left,
    k, SomeGreen, y, o, NoRed, t0, t)), t1)), t2)
  | Right_child (_, _, _, _, _, _, _, _) -> assert false (* absurd case *)

(** val no_pref :
    nat -> nat -> nat -> kind -> 'a1 packet -> 'a1 triple -> 'a1
    non_empty_cdeque **)

let no_pref _ _ _ _ pkt t =
  match pkt with
  | Only_child (lvl, len, is_hole, k, y, o, _, t0) ->
    Only_path (lvl, SomeGreen, NoRed, (Children (lvl, len, (add len lvl),
      is_hole, Only, k, SomeGreen, y, o, NoRed, t0, t)))
  | Left_child (_, _, _, _, _, _, _, _, _) -> assert false (* absurd case *)
  | Right_child (lvl, len, is_hole, k, y, o, p, t0) ->
    Pair_green (lvl, p, (Children (lvl, len, (add len lvl), is_hole, Right,
      k, SomeGreen, y, o, NoRed, t0, t)))

(** val make_child :
    nat -> nat -> nat -> preferred_child -> kind -> green_hue -> red_hue ->
    'a1 packet -> 'a1 triple -> 'a1 sdeque **)

let make_child _ _ _ _ _ g r pkt t =
  match pkt with
  | Only_child (lvl, len, is_hole, k, y, o, _, t0) ->
    Sd ((Mix (g, NoYellow, NoOrange, r)), (NonEmpty (lvl, g, r, (Only_path
      (lvl, g, r, (Children (lvl, len, (add len lvl), is_hole, Only, k, g, y,
      o, r, t0, t)))))))
  | Left_child (lvl, len, is_hole, k, y, o, c, t0, p) ->
    Sd ((Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (NonEmpty (lvl,
      NoGreen, SomeRed, (Pair_red (lvl, (Mix (g, NoYellow, NoOrange, r)), c,
      (Children (lvl, len, (add len lvl), is_hole, Left, k, g, y, o, r, t0,
      t)), p)))))
  | Right_child (lvl, len, is_hole, k, y, o, p, t0) ->
    (match g with
     | SomeGreen ->
       (match r with
        | SomeRed -> assert false (* absurd case *)
        | NoRed ->
          Sd ((Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (NonEmpty (lvl,
            SomeGreen, NoRed, (Pair_green (lvl, p, (Children (lvl, len,
            (add len lvl), is_hole, Right, k, SomeGreen, y, o, NoRed, t0,
            t))))))))
     | NoGreen ->
       (match r with
        | SomeRed ->
          Sd ((Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (NonEmpty (lvl,
            NoGreen, SomeRed, (Pair_red (lvl, (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)), (Mix (NoGreen, NoYellow, NoOrange, SomeRed)),
            p, (Children (lvl, len, (add len lvl), is_hole, Right, k,
            NoGreen, y, o, SomeRed, t0, t)))))))
        | NoRed -> assert false (* absurd case *)))

(** val push_child :
    nat -> nat -> nat -> preferred_child -> kind -> green_hue -> red_hue ->
    'a1 stored_triple -> 'a1 packet -> 'a1 triple -> ('a1 packet, 'a1 triple)
    prod **)

let push_child _ _ nlvl _ _ g r x pkt t =
  match pkt with
  | Only_child (_, _, _, _, _, _, pref, t0) ->
    (match t0 with
     | Hole (_, _) ->
       Coq_pair ((Only_child (nlvl, O, Coq_true, Only, SomeYellow,
         SomeOrange, pref, (Hole (nlvl, Only)))),
         (push_only_triple nlvl O Only (Mix (g, NoYellow, NoOrange, r)) x t))
     | Yellow (lvl, len, qp, qs, _, k2, p, p0, s, b) ->
       Coq_pair ((Only_child (lvl, (S len), Coq_false, k2, SomeYellow,
         NoOrange, pref,
         (push_only_triple lvl (S len) k2 (Mix (NoGreen, SomeYellow,
           NoOrange, NoRed)) x (Yellow (lvl, len, qp, qs, Only, k2, p, p0, s,
           b))))), t)
     | Orange (lvl, len, qp, qs, _, k2, p, p0, s, b) ->
       Coq_pair ((Only_child (lvl, (S len), Coq_false, k2, NoYellow,
         SomeOrange, pref,
         (push_only_triple lvl (S len) k2 (Mix (NoGreen, NoYellow,
           SomeOrange, NoRed)) x (Orange (lvl, len, qp, qs, Only, k2, p, p0,
           s, b))))), t)
     | _ -> assert false (* absurd case *))
  | Left_child (_, _, _, _, _, _, c, t0, p) ->
    (match t0 with
     | Hole (_, _) ->
       Coq_pair ((Left_child (nlvl, O, Coq_true, Left, SomeYellow,
         SomeOrange, c, (Hole (nlvl, Left)), p)),
         (push_left_triple nlvl O Left (Mix (g, NoYellow, NoOrange, r)) x t))
     | Yellow (lvl, len, qp, qs, _, k2, p0, p1, s, b) ->
       Coq_pair ((Left_child (lvl, (S len), Coq_false, k2, SomeYellow,
         NoOrange, c,
         (push_left_triple lvl (S len) k2 (Mix (NoGreen, SomeYellow,
           NoOrange, NoRed)) x (Yellow (lvl, len, qp, qs, Left, k2, p0, p1,
           s, b))), p)), t)
     | Orange (lvl, len, qp, qs, _, k2, p0, p1, s, b) ->
       Coq_pair ((Left_child (lvl, (S len), Coq_false, k2, NoYellow,
         SomeOrange, c,
         (push_left_triple lvl (S len) k2 (Mix (NoGreen, NoYellow,
           SomeOrange, NoRed)) x (Orange (lvl, len, qp, qs, Left, k2, p0, p1,
           s, b))), p)), t)
     | _ -> assert false (* absurd case *))
  | Right_child (lvl, len, is_hole, k, y, o, p, t0) ->
    Coq_pair ((Right_child (lvl, len, is_hole, k, y, o,
      (push_left_path lvl (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) x p),
      t0)), t)

(** val inject_child :
    nat -> nat -> nat -> preferred_child -> kind -> green_hue -> red_hue ->
    'a1 packet -> 'a1 triple -> 'a1 stored_triple -> ('a1 packet, 'a1 triple)
    prod **)

let inject_child _ _ nlvl _ _ g r pkt t x =
  match pkt with
  | Only_child (_, _, _, _, _, _, pref, t0) ->
    (match t0 with
     | Hole (_, _) ->
       Coq_pair ((Only_child (nlvl, O, Coq_true, Only, SomeYellow,
         SomeOrange, pref, (Hole (nlvl, Only)))),
         (inject_only_triple nlvl O Only (Mix (g, NoYellow, NoOrange, r)) t x))
     | Yellow (lvl, len, qp, qs, _, k2, p, p0, s, b) ->
       Coq_pair ((Only_child (lvl, (S len), Coq_false, k2, SomeYellow,
         NoOrange, pref,
         (inject_only_triple lvl (S len) k2 (Mix (NoGreen, SomeYellow,
           NoOrange, NoRed)) (Yellow (lvl, len, qp, qs, Only, k2, p, p0, s,
           b)) x))), t)
     | Orange (lvl, len, qp, qs, _, k2, p, p0, s, b) ->
       Coq_pair ((Only_child (lvl, (S len), Coq_false, k2, NoYellow,
         SomeOrange, pref,
         (inject_only_triple lvl (S len) k2 (Mix (NoGreen, NoYellow,
           SomeOrange, NoRed)) (Orange (lvl, len, qp, qs, Only, k2, p, p0, s,
           b)) x))), t)
     | _ -> assert false (* absurd case *))
  | Left_child (lvl, len, is_hole, k, y, o, c, t0, p) ->
    Coq_pair ((Left_child (lvl, len, is_hole, k, y, o, c, t0,
      (inject_right_path lvl c p x))), t)
  | Right_child (_, _, _, _, _, _, p, t0) ->
    (match t0 with
     | Hole (_, _) ->
       Coq_pair ((Right_child (nlvl, O, Coq_true, Right, SomeYellow,
         SomeOrange, p, (Hole (nlvl, Right)))),
         (inject_right_triple nlvl O Right (Mix (g, NoYellow, NoOrange, r)) t
           x))
     | Yellow (lvl, len, qp, qs, _, k2, p0, p1, s, b) ->
       Coq_pair ((Right_child (lvl, (S len), Coq_false, k2, SomeYellow,
         NoOrange, p,
         (inject_right_triple lvl (S len) k2 (Mix (NoGreen, SomeYellow,
           NoOrange, NoRed)) (Yellow (lvl, len, qp, qs, Right, k2, p0, p1, s,
           b)) x))), t)
     | Orange (lvl, len, qp, qs, _, k2, p0, p1, s, b) ->
       Coq_pair ((Right_child (lvl, (S len), Coq_false, k2, NoYellow,
         SomeOrange, p,
         (inject_right_triple lvl (S len) k2 (Mix (NoGreen, NoYellow,
           SomeOrange, NoRed)) (Orange (lvl, len, qp, qs, Right, k2, p0, p1,
           s, b)) x))), t)
     | _ -> assert false (* absurd case *))

(** val stored_left :
    nat -> nat -> color -> 'a1 prefix -> 'a1 cdeque -> 'a1 suffix -> 'a1
    buffer_12 -> ('a1 prefix, 'a1 stored_triple) prod **)

let stored_left lvl q c p cd s = function
| Coq_pair (s0, v) ->
  let Coq_pair (p0, t) =
    pop2 (S
      (let rec add0 n m =
         match n with
         | O -> m
         | S p0 -> S (add0 p0 m)
       in add0 (S (S O)) q)) p
  in
  let Coq_pair (s1, s2) = p0 in
  Coq_pair ((pair s1 s2), (ST_triple (lvl, q, (vector_length (S O) v), c, t,
  cd, (Buffer.inject_vector (S O) (S (S (S O))) (inject (S (S O)) s s0) v))))

(** val stored_right :
    nat -> nat -> color -> 'a1 buffer_12 -> 'a1 prefix -> 'a1 cdeque -> 'a1
    suffix -> ('a1 stored_triple, 'a1 suffix) prod **)

let stored_right lvl q c b p cd s =
  let Coq_pair (s0, v) = b in
  let Coq_pair (p0, s1) =
    eject2 (S
      (let rec add0 n m =
         match n with
         | O -> m
         | S p0 -> S (add0 p0 m)
       in add0 (S (S O)) q)) s
  in
  let Coq_pair (t, s2) = p0 in
  Coq_pair ((ST_triple (lvl, (vector_length (S O) v), q, c,
  (push (add (S (S O)) (vector_length (S O) v)) s0
    (Buffer.push_vector (S O) (S (S O)) v p)), cd, t)), (pair s2 s1))

(** val extract_stored_left :
    nat -> color -> 'a1 path -> 'a1 buffer_12 -> ('a1 suffix, 'a1
    stored_triple) prod **)

let extract_stored_left _ _ p b =
  let Children (_, _, _, _, _, _, g, _, _, r, t, t0) = p in
  (match t with
   | Hole (_, _) ->
     (match t0 with
      | Small (lvl, _, _, _, p0, s, s0) ->
        (match s0 with
         | Left_small_sizes q ->
           stored_left lvl q (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) p0
             (Empty (S lvl)) s b
         | _ -> assert false (* absurd case *))
      | Green (lvl, _, _, _, g0, r0, p0, n, s, b0) ->
        (match b0 with
         | Left_big_sizes q ->
           stored_left lvl (S
             (let rec add0 n0 m =
                match n0 with
                | O -> m
                | S p1 -> S (add0 p1 m)
              in add0 (S (S O)) q)) (Mix (g0, NoYellow, NoOrange, r0)) p0
             (NonEmpty ((S lvl), g0, r0, n)) s b
         | _ -> assert false (* absurd case *))
      | Red (lvl, _, _, _, p0, n, s, b0) ->
        (match b0 with
         | Left_big_sizes q ->
           stored_left lvl q (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) p0
             (NonEmpty ((S lvl), SomeGreen, NoRed, n)) s b
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (lvl, len, _, _, _, k2, p0, p1, s, b0) ->
     (match b0 with
      | Left_big_sizes q ->
        let Sd (c, c0) =
          make_child (S lvl) len (S (add len lvl)) Preferred_left k2 g r p1 t0
        in
        stored_left lvl (S
          (let rec add0 n m =
             match n with
             | O -> m
             | S p2 -> S (add0 p2 m)
           in add0 (S O) q)) c p0 c0 s b
      | _ -> assert false (* absurd case *))
   | Orange (lvl, len, _, _, _, k2, p0, p1, s, b0) ->
     (match b0 with
      | Left_big_sizes q ->
        let Sd (c, c0) =
          make_child (S lvl) len (S (add len lvl)) Preferred_right k2 g r p1
            t0
        in
        stored_left lvl (S
          (let rec add0 n m =
             match n with
             | O -> m
             | S p2 -> S (add0 p2 m)
           in add0 O q)) c p0 c0 s b
      | _ -> assert false (* absurd case *))
   | _ -> assert false (* absurd case *))

(** val extract_stored_right :
    nat -> color -> 'a1 buffer_12 -> 'a1 path -> ('a1 stored_triple, 'a1
    suffix) prod **)

let extract_stored_right _ _ b = function
| Children (_, _, _, _, _, _, g, _, _, r, t, t0) ->
  (match t with
   | Hole (_, _) ->
     (match t0 with
      | Small (lvl, _, _, _, p0, s, s0) ->
        (match s0 with
         | Right_small_sizes q ->
           stored_right lvl q (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) b
             p0 (Empty (S lvl)) s
         | _ -> assert false (* absurd case *))
      | Green (lvl, _, _, _, g0, r0, p0, n, s, b0) ->
        (match b0 with
         | Right_big_sizes q ->
           stored_right lvl (S
             (let rec add0 n0 m =
                match n0 with
                | O -> m
                | S p1 -> S (add0 p1 m)
              in add0 (S (S O)) q)) (Mix (g0, NoYellow, NoOrange, r0)) b p0
             (NonEmpty ((S lvl), g0, r0, n)) s
         | _ -> assert false (* absurd case *))
      | Red (lvl, _, _, _, p0, n, s, b0) ->
        (match b0 with
         | Right_big_sizes q ->
           stored_right lvl q (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) b
             p0 (NonEmpty ((S lvl), SomeGreen, NoRed, n)) s
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (lvl, len, _, _, _, k2, p0, p1, s, b0) ->
     (match b0 with
      | Right_big_sizes q ->
        let Sd (c, c0) =
          make_child (S lvl) len (S (add len lvl)) Preferred_left k2 g r p1 t0
        in
        stored_right lvl (S
          (let rec add0 n m =
             match n with
             | O -> m
             | S p2 -> S (add0 p2 m)
           in add0 (S O) q)) c b p0 c0 s
      | _ -> assert false (* absurd case *))
   | Orange (lvl, len, _, _, _, k2, p0, p1, s, b0) ->
     (match b0 with
      | Right_big_sizes q ->
        let Sd (c, c0) =
          make_child (S lvl) len (S (add len lvl)) Preferred_right k2 g r p1
            t0
        in
        stored_right lvl (S
          (let rec add0 n m =
             match n with
             | O -> m
             | S p2 -> S (add0 p2 m)
           in add0 O q)) c b p0 c0 s
      | _ -> assert false (* absurd case *))
   | _ -> assert false (* absurd case *))

(** val left_of_pair :
    nat -> color -> color -> 'a1 path -> 'a1 path -> 'a1 path **)

let left_of_pair _ _ c2 pl pr =
  let Children (_, _, _, _, _, _, g, _, _, r, t, t0) = pl in
  (match t with
   | Hole (_, _) ->
     (match t0 with
      | Small (lvl, _, _, _, p, s, s0) ->
        (match s0 with
         | Left_small_sizes q ->
           let Coq_pair (s1, s2) = two s in
           let Coq_pair (s3, s4) =
             extract_stored_right lvl c2 (Coq_pair (s2, (V0 (S O)))) pr
           in
           Children (lvl, (S O), (S lvl), Coq_false, Left, Only, SomeGreen,
           NoYellow, SomeOrange, NoRed, (Orange (lvl, O, (S
           (add (S (S (S (S (S O))))) q)), (S (S O)), Left, Only,
           (inject (add (S (S (S (S (S O))))) q) p s1), (Only_child ((S lvl),
           O, Coq_true, Only, SomeYellow, SomeOrange, Preferred_right, (Hole
           ((S lvl), Only)))), s4, (Left_big_sizes q))),
           (single_triple (S lvl) s3))
         | _ -> assert false (* absurd case *))
      | Green (lvl, _, _, _, g0, r0, p, n, s, b) ->
        (match b with
         | Left_big_sizes q ->
           let Coq_pair (s0, s1) = two s in
           let Coq_pair (s2, s3) =
             extract_stored_right lvl c2 (Coq_pair (s0, (V1 (O, s1)))) pr
           in
           Children (lvl, O, lvl, Coq_true, Left, Left, SomeGreen,
           SomeYellow, SomeOrange, NoRed, (Hole (lvl, Left)), (Green (lvl,
           (add (S (S (S (S (S (S (S (S O)))))))) q), (S (S O)), Left, g0,
           r0, p,
           (inject_ne_cdeque (S lvl) (Mix (g0, NoYellow, NoOrange, r0)) n s2),
           s3, (Left_big_sizes q))))
         | _ -> assert false (* absurd case *))
      | Red (lvl, _, _, _, p, n, s, b) ->
        (match b with
         | Left_big_sizes q ->
           let Coq_pair (s0, s1) = two s in
           let Coq_pair (s2, s3) =
             extract_stored_right lvl c2 (Coq_pair (s0, (V1 (O, s1)))) pr
           in
           Children (lvl, O, lvl, Coq_true, Left, Left, NoGreen, SomeYellow,
           SomeOrange, SomeRed, (Hole (lvl, Left)), (Red (lvl,
           (add (S (S (S (S (S O))))) q), (S (S O)), Left, p,
           (inject_ne_cdeque (S lvl) (Mix (SomeGreen, NoYellow, NoOrange,
             NoRed)) n s2), s3, (Left_big_sizes q))))
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (lvl, len, _, _, _, k2, p, p0, s, b) ->
     (match b with
      | Left_big_sizes q ->
        let Coq_pair (s0, s1) = two s in
        let Coq_pair (s2, s3) =
          extract_stored_right lvl c2 (Coq_pair (s0, (V1 (O, s1)))) pr
        in
        let Coq_pair (p1, t1) =
          inject_child (S lvl) len (S (add len lvl)) Preferred_left k2 g r p0
            t0 s2
        in
        Children (lvl, (S len), (S (add len lvl)), Coq_false, Left, k2, g,
        SomeYellow, NoOrange, r, (Yellow (lvl, len,
        (add (S (S (S (S (S (S (S O))))))) q), (S (S O)), Left, k2, p, p1,
        s3, (Left_big_sizes q))), t1)
      | _ -> assert false (* absurd case *))
   | Orange (lvl, len, _, _, _, k2, p, p0, s, b) ->
     (match b with
      | Left_big_sizes q ->
        let Coq_pair (s0, s1) = two s in
        let Coq_pair (s2, s3) =
          extract_stored_right lvl c2 (Coq_pair (s0, (V1 (O, s1)))) pr
        in
        let Coq_pair (p1, t1) =
          inject_child (S lvl) len (S (add len lvl)) Preferred_right k2 g r
            p0 t0 s2
        in
        Children (lvl, (S len), (S (add len lvl)), Coq_false, Left, k2, g,
        NoYellow, SomeOrange, r, (Orange (lvl, len,
        (add (S (S (S (S (S (S O)))))) q), (S (S O)), Left, k2, p, p1, s3,
        (Left_big_sizes q))), t1)
      | _ -> assert false (* absurd case *))
   | _ -> assert false (* absurd case *))

(** val right_of_pair :
    nat -> color -> color -> 'a1 path -> 'a1 path -> 'a1 path **)

let right_of_pair _ c1 _ pl = function
| Children (_, _, _, _, _, _, g, _, _, r, t, t0) ->
  (match t with
   | Hole (_, _) ->
     (match t0 with
      | Small (lvl, _, _, _, p, s, s0) ->
        (match s0 with
         | Right_small_sizes q ->
           let Coq_pair (s1, s2) = two p in
           let Coq_pair (s3, s4) =
             extract_stored_left lvl c1 pl (Coq_pair (s1, (V0 (S O))))
           in
           Children (lvl, (S O), (S lvl), Coq_false, Right, Only, SomeGreen,
           NoYellow, SomeOrange, NoRed, (Orange (lvl, O, (S (S O)), (S
           (add (S (S (S (S (S O))))) q)), Right, Only, s3, (Only_child ((S
           lvl), O, Coq_true, Only, SomeYellow, SomeOrange, Preferred_right,
           (Hole ((S lvl), Only)))),
           (push (add (S (S (S (S (S O))))) q) s2 s), (Right_big_sizes q))),
           (single_triple (S lvl) s4))
         | _ -> assert false (* absurd case *))
      | Green (lvl, _, _, _, g0, r0, p, n, s, b) ->
        (match b with
         | Right_big_sizes q ->
           let Coq_pair (s0, s1) = two p in
           let Coq_pair (s2, s3) =
             extract_stored_left lvl c1 pl (Coq_pair (s0, (V1 (O, s1))))
           in
           Children (lvl, O, lvl, Coq_true, Right, Right, SomeGreen,
           SomeYellow, SomeOrange, NoRed, (Hole (lvl, Right)), (Green (lvl,
           (S (S O)), (add (S (S (S (S (S (S (S (S O)))))))) q), Right, g0,
           r0, s2,
           (push_ne_cdeque (S lvl) (Mix (g0, NoYellow, NoOrange, r0)) s3 n),
           s, (Right_big_sizes q))))
         | _ -> assert false (* absurd case *))
      | Red (lvl, _, _, _, p, n, s, b) ->
        (match b with
         | Right_big_sizes q ->
           let Coq_pair (s0, s1) = two p in
           let Coq_pair (s2, s3) =
             extract_stored_left lvl c1 pl (Coq_pair (s0, (V1 (O, s1))))
           in
           Children (lvl, O, lvl, Coq_true, Right, Right, NoGreen,
           SomeYellow, SomeOrange, SomeRed, (Hole (lvl, Right)), (Red (lvl,
           (S (S O)), (add (S (S (S (S (S O))))) q), Right, s2,
           (push_ne_cdeque (S lvl) (Mix (SomeGreen, NoYellow, NoOrange,
             NoRed)) s3 n), s, (Right_big_sizes q))))
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (lvl, len, _, _, _, k2, p, p0, s, b) ->
     (match b with
      | Right_big_sizes q ->
        let Coq_pair (s0, s1) = two p in
        let Coq_pair (s2, s3) =
          extract_stored_left lvl c1 pl (Coq_pair (s0, (V1 (O, s1))))
        in
        let Coq_pair (p1, t1) =
          push_child (S lvl) len (S (add len lvl)) Preferred_left k2 g r s3
            p0 t0
        in
        Children (lvl, (S len), (S (add len lvl)), Coq_false, Right, k2, g,
        SomeYellow, NoOrange, r, (Yellow (lvl, len, (S (S O)),
        (add (S (S (S (S (S (S (S O))))))) q), Right, k2, s2, p1, s,
        (Right_big_sizes q))), t1)
      | _ -> assert false (* absurd case *))
   | Orange (lvl, len, _, _, _, k2, p, p0, s, b) ->
     (match b with
      | Right_big_sizes q ->
        let Coq_pair (s0, s1) = two p in
        let Coq_pair (s2, s3) =
          extract_stored_left lvl c1 pl (Coq_pair (s0, (V1 (O, s1))))
        in
        let Coq_pair (p1, t1) =
          push_child (S lvl) len (S (add len lvl)) Preferred_right k2 g r s3
            p0 t0
        in
        Children (lvl, (S len), (S (add len lvl)), Coq_false, Right, k2, g,
        NoYellow, SomeOrange, r, (Orange (lvl, len, (S (S O)),
        (add (S (S (S (S (S (S O)))))) q), Right, k2, s2, p1, s,
        (Right_big_sizes q))), t1)
      | _ -> assert false (* absurd case *))
   | _ -> assert false (* absurd case *))

(** val left_of_only : nat -> color -> 'a1 path -> 'a1 path_attempt **)

let left_of_only _ _ = function
| Children (_, _, _, _, _, _, g, _, _, r, t, t0) ->
  (match t with
   | Hole (_, _) ->
     (match t0 with
      | Small (lvl, _, _, _, p0, _, s) ->
        (match s with
         | Only_small_sizes q ->
           (match has5p2 q p0 with
            | Coq_inl v ->
              ZeroSix (Left, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), v)
            | Coq_inr p1 ->
              let Coq_pair (p2, s0) = p1 in
              let Coq_pair (p3, s1) = p2 in
              Ok (Left, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
              (Children (lvl, O, lvl, Coq_true, Left, Left, SomeGreen,
              SomeYellow, SomeOrange, NoRed, (Hole (lvl, Left)), (Small (lvl,
              (add (S (S (S (S (S O)))))
                (PeanoNat.Nat.iter (S (S (S (S (S O))))) PeanoNat.Nat.pred
                  (PeanoNat.Nat.pred q))), (S (S O)), Left, p3, (pair s1 s0),
              (Left_small_sizes
              (PeanoNat.Nat.iter (S (S (S (S (S O))))) PeanoNat.Nat.pred
                (PeanoNat.Nat.pred q)))))))))
         | _ -> assert false (* absurd case *))
      | Green (lvl, _, _, _, g0, r0, p0, n, s, b) ->
        (match b with
         | Only_big_sizes (qp, qs) ->
           let Coq_pair (p1, s0) =
             eject2 (S
               (let rec add0 n0 m =
                  match n0 with
                  | O -> m
                  | S p1 -> S (add0 p1 m)
                in add0 (S (S (S (S (S O))))) qs)) s
           in
           let Coq_pair (t1, s1) = p1 in
           Ok (Left, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Children
           (lvl, O, lvl, Coq_true, Left, Left, SomeGreen, SomeYellow,
           SomeOrange, NoRed, (Hole (lvl, Left)), (Green (lvl,
           (add (S (S (S (S (S (S (S (S O)))))))) qp), (S (S O)), Left, g0,
           r0, p0,
           (inject_ne_cdeque (S lvl) (Mix (g0, NoYellow, NoOrange, r0)) n
             (ST_small (lvl, (S
             (let rec add0 n0 m =
                match n0 with
                | O -> m
                | S p2 -> S (add0 p2 m)
              in add0 (S (S O)) qs)), t1))), (pair s1 s0), (Left_big_sizes
           qp))))))
         | _ -> assert false (* absurd case *))
      | Red (lvl, _, _, _, p0, n, s, b) ->
        (match b with
         | Only_big_sizes (qp, qs) ->
           let Coq_pair (p1, s0) =
             eject2 (S
               (let rec add0 n0 m =
                  match n0 with
                  | O -> m
                  | S p1 -> S (add0 p1 m)
                in add0 (S (S O)) qs)) s
           in
           let Coq_pair (t1, s1) = p1 in
           Ok (Left, (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Children
           (lvl, O, lvl, Coq_true, Left, Left, NoGreen, SomeYellow,
           SomeOrange, SomeRed, (Hole (lvl, Left)), (Red (lvl,
           (add (S (S (S (S (S O))))) qp), (S (S O)), Left, p0,
           (inject_ne_cdeque (S lvl) (Mix (SomeGreen, NoYellow, NoOrange,
             NoRed)) n (ST_small (lvl, qs, t1))), (pair s1 s0),
           (Left_big_sizes qp))))))
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Only_big_sizes (qp, qs) ->
        let Coq_pair (p2, s0) =
          eject2 (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p2 -> S (add0 p2 m)
             in add0 (S (S (S (S O)))) qs)) s
        in
        let Coq_pair (t1, s1) = p2 in
        let Coq_pair (p3, t2) =
          inject_child (S lvl) len (S (add len lvl)) Preferred_left k2 g r p1
            t0 (ST_small (lvl, (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p3 -> S (add0 p3 m)
             in add0 (S O) qs)), t1))
        in
        Ok (Left, (Mix (g, NoYellow, NoOrange, r)), (Children (lvl, (S len),
        (S (add len lvl)), Coq_false, Left, k2, g, SomeYellow, NoOrange, r,
        (Yellow (lvl, len, (add (S (S (S (S (S (S (S O))))))) qp), (S (S O)),
        Left, k2, p0, p3, (pair s1 s0), (Left_big_sizes qp))), t2)))
      | _ -> assert false (* absurd case *))
   | Orange (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Only_big_sizes (qp, qs) ->
        let Coq_pair (p2, s0) =
          eject2 (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p2 -> S (add0 p2 m)
             in add0 (S (S (S O))) qs)) s
        in
        let Coq_pair (t1, s1) = p2 in
        let Coq_pair (p3, t2) =
          inject_child (S lvl) len (S (add len lvl)) Preferred_right k2 g r
            p1 t0 (ST_small (lvl, (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p3 -> S (add0 p3 m)
             in add0 O qs)), t1))
        in
        Ok (Left, (Mix (g, NoYellow, NoOrange, r)), (Children (lvl, (S len),
        (S (add len lvl)), Coq_false, Left, k2, g, NoYellow, SomeOrange, r,
        (Orange (lvl, len, (add (S (S (S (S (S (S O)))))) qp), (S (S O)),
        Left, k2, p0, p3, (pair s1 s0), (Left_big_sizes qp))), t2)))
      | _ -> assert false (* absurd case *))
   | _ -> assert false (* absurd case *))

(** val right_of_only : nat -> color -> 'a1 path -> 'a1 path_attempt **)

let right_of_only _ _ = function
| Children (_, _, _, _, _, _, g, _, _, r, t, t0) ->
  (match t with
   | Hole (_, _) ->
     (match t0 with
      | Small (lvl, _, _, _, p0, _, s) ->
        (match s with
         | Only_small_sizes q ->
           (match has2p5 q p0 with
            | Coq_inl v ->
              ZeroSix (Right, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), v)
            | Coq_inr p1 ->
              let Coq_pair (p2, p3) = p1 in
              let Coq_pair (s0, s1) = p2 in
              Ok (Right, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
              (Children (lvl, O, lvl, Coq_true, Right, Right, SomeGreen,
              SomeYellow, SomeOrange, NoRed, (Hole (lvl, Right)), (Small
              (lvl, (S (S O)),
              (add (S (S (S (S (S O)))))
                (PeanoNat.Nat.iter (S (S (S (S (S O))))) PeanoNat.Nat.pred
                  (PeanoNat.Nat.pred q))), Right, (pair s0 s1), p3,
              (Right_small_sizes
              (PeanoNat.Nat.iter (S (S (S (S (S O))))) PeanoNat.Nat.pred
                (PeanoNat.Nat.pred q)))))))))
         | _ -> assert false (* absurd case *))
      | Green (lvl, _, _, _, g0, r0, p0, n, s, b) ->
        (match b with
         | Only_big_sizes (qp, qs) ->
           let Coq_pair (p1, t1) =
             pop2 (S
               (let rec add0 n0 m =
                  match n0 with
                  | O -> m
                  | S p1 -> S (add0 p1 m)
                in add0 (S (S (S (S (S O))))) qp)) p0
           in
           let Coq_pair (s0, s1) = p1 in
           Ok (Right, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Children
           (lvl, O, lvl, Coq_true, Right, Right, SomeGreen, SomeYellow,
           SomeOrange, NoRed, (Hole (lvl, Right)), (Green (lvl, (S (S O)),
           (add (S (S (S (S (S (S (S (S O)))))))) qs), Right, g0, r0,
           (pair s0 s1),
           (push_ne_cdeque (S lvl) (Mix (g0, NoYellow, NoOrange, r0))
             (ST_small (lvl, (S
             (let rec add0 n0 m =
                match n0 with
                | O -> m
                | S p2 -> S (add0 p2 m)
              in add0 (S (S O)) qp)), t1)) n), s, (Right_big_sizes qs))))))
         | _ -> assert false (* absurd case *))
      | Red (lvl, _, _, _, p0, n, s, b) ->
        (match b with
         | Only_big_sizes (qp, qs) ->
           let Coq_pair (p1, t1) =
             pop2 (S
               (let rec add0 n0 m =
                  match n0 with
                  | O -> m
                  | S p1 -> S (add0 p1 m)
                in add0 (S (S O)) qp)) p0
           in
           let Coq_pair (s0, s1) = p1 in
           Ok (Right, (Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (Children
           (lvl, O, lvl, Coq_true, Right, Right, NoGreen, SomeYellow,
           SomeOrange, SomeRed, (Hole (lvl, Right)), (Red (lvl, (S (S O)),
           (add (S (S (S (S (S O))))) qs), Right, (pair s0 s1),
           (push_ne_cdeque (S lvl) (Mix (SomeGreen, NoYellow, NoOrange,
             NoRed)) (ST_small (lvl, qp, t1)) n), s, (Right_big_sizes qs))))))
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Only_big_sizes (qp, qs) ->
        let Coq_pair (p2, t1) =
          pop2 (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p2 -> S (add0 p2 m)
             in add0 (S (S (S (S O)))) qp)) p0
        in
        let Coq_pair (s0, s1) = p2 in
        let Coq_pair (p3, t2) =
          push_child (S lvl) len (S (add len lvl)) Preferred_left k2 g r
            (ST_small (lvl, (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p3 -> S (add0 p3 m)
             in add0 (S O) qp)), t1)) p1 t0
        in
        Ok (Right, (Mix (g, NoYellow, NoOrange, r)), (Children (lvl, (S len),
        (S (add len lvl)), Coq_false, Right, k2, g, SomeYellow, NoOrange, r,
        (Yellow (lvl, len, (S (S O)), (add (S (S (S (S (S (S (S O))))))) qs),
        Right, k2, (pair s0 s1), p3, s, (Right_big_sizes qs))), t2)))
      | _ -> assert false (* absurd case *))
   | Orange (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Only_big_sizes (qp, qs) ->
        let Coq_pair (p2, t1) =
          pop2 (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p2 -> S (add0 p2 m)
             in add0 (S (S (S O))) qp)) p0
        in
        let Coq_pair (s0, s1) = p2 in
        let Coq_pair (p3, t2) =
          push_child (S lvl) len (S (add len lvl)) Preferred_right k2 g r
            (ST_small (lvl, (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p3 -> S (add0 p3 m)
             in add0 O qp)), t1)) p1 t0
        in
        Ok (Right, (Mix (g, NoYellow, NoOrange, r)), (Children (lvl, (S len),
        (S (add len lvl)), Coq_false, Right, k2, g, NoYellow, SomeOrange, r,
        (Orange (lvl, len, (S (S O)), (add (S (S (S (S (S (S O)))))) qs),
        Right, k2, (pair s0 s1), p3, s, (Right_big_sizes qs))), t2)))
      | _ -> assert false (* absurd case *))
   | _ -> assert false (* absurd case *))

(** val make_left : nat -> color -> 'a1 cdeque -> 'a1 path_attempt **)

let make_left _ _ = function
| Empty _ ->
  ZeroSix (Left, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (V0 (S (S (S
    (S (S (S O))))))))
| NonEmpty (_, _, _, n) ->
  (match n with
   | Only_path (lvl, g, r, p) ->
     left_of_only lvl (Mix (g, NoYellow, NoOrange, r)) p
   | Pair_green (lvl, p, p0) ->
     Ok (Left, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
       (left_of_pair lvl (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix
         (SomeGreen, NoYellow, NoOrange, NoRed)) p p0))
   | Pair_red (lvl, cl, cr, p, p0) ->
     Any (Left, cl, (left_of_pair lvl cl cr p p0)))

(** val make_right : nat -> color -> 'a1 cdeque -> 'a1 path_attempt **)

let make_right _ _ = function
| Empty _ ->
  ZeroSix (Right, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (V0 (S (S (S
    (S (S (S O))))))))
| NonEmpty (_, _, _, n) ->
  (match n with
   | Only_path (lvl, g, r, p) ->
     right_of_only lvl (Mix (g, NoYellow, NoOrange, r)) p
   | Pair_green (lvl, p, p0) ->
     Ok (Right, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
       (right_of_pair lvl (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix
         (SomeGreen, NoYellow, NoOrange, NoRed)) p p0))
   | Pair_red (lvl, cl, cr, p, p0) ->
     Any (Right, cr, (right_of_pair lvl cl cr p p0)))

(** val concat_semi : nat -> 'a1 sdeque -> 'a1 sdeque -> 'a1 sdeque **)

let concat_semi lvl sd1 sd2 =
  let Sd (c, c0) = sd1 in
  let Sd (c1, c2) = sd2 in
  (match make_left lvl c c0 with
   | ZeroSix (_, _, v) ->
     Sd (c1, (push_vector lvl (S (S (S (S (S (S O)))))) c1 v c2))
   | Ok (_, c3, p) ->
     (match make_right lvl c1 c2 with
      | ZeroSix (_, _, v) ->
        Sd (c3, (inject_vector lvl (S (S (S (S (S (S O)))))) c3 c0 v))
      | Ok (_, c4, p0) ->
        Sd ((Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (NonEmpty (lvl,
          NoGreen, SomeRed, (Pair_red (lvl, c3, c4, p, p0)))))
      | Any (_, c4, p0) ->
        Sd ((Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (NonEmpty (lvl,
          NoGreen, SomeRed, (Pair_red (lvl, c3, c4, p, p0))))))
   | Any (_, c3, p) ->
     (match make_right lvl c1 c2 with
      | ZeroSix (_, _, v) ->
        Sd ((Mix (NoGreen, NoYellow, NoOrange, SomeRed)),
          (inject_vector lvl (S (S (S (S (S (S O)))))) (Mix (NoGreen,
            NoYellow, NoOrange, SomeRed)) c0 v))
      | Ok (_, c4, p0) ->
        Sd ((Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (NonEmpty (lvl,
          NoGreen, SomeRed, (Pair_red (lvl, c3, c4, p, p0)))))
      | Any (_, c4, p0) ->
        Sd ((Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (NonEmpty (lvl,
          NoGreen, SomeRed, (Pair_red (lvl, c3, c4, p, p0)))))))

(** val semi_of_left :
    nat -> color -> 'a1 path -> 'a1 stored_triple -> 'a1 stored_triple -> 'a1
    stored_triple -> 'a1 stored_triple -> 'a1 stored_triple -> 'a1
    stored_triple -> 'a1 sdeque **)

let semi_of_left _ _ p x1 x2 x3 x4 x5 x6 =
  let Children (_, _, _, _, _, _, g, _, _, r, t, t0) = p in
  (match t with
   | Hole (_, _) ->
     (match t0 with
      | Small (lvl, _, _, _, p0, s, s0) ->
        (match s0 with
         | Left_small_sizes q ->
           let Coq_pair (s1, s2) = two s in
           Sd ((Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (NonEmpty (lvl,
           SomeGreen, NoRed, (Only_path (lvl, SomeGreen, NoRed, (Children
           (lvl, O, lvl, Coq_true, Only, Only, SomeGreen, SomeYellow,
           SomeOrange, NoRed, (Hole (lvl, Only)), (Small (lvl,
           (add (S (S (S (S (S (S O)))))) (S (S
             (add (S (S (S (S (S O))))) q)))), O, Only,
           (inject6 (S (S (add (S (S (S (S (S O))))) q)))
             (inject2 (add (S (S (S (S (S O))))) q) p0 s1 s2) x1 x2 x3 x4 x5
             x6), empty, (Only_small_sizes (S
           (let rec add0 n m =
              match n with
              | O -> m
              | S p1 -> S (add0 p1 m)
            in add0 (S (S (S (S O)))) (S (S (add (S (S (S (S (S O))))) q)))))))))))))))
         | _ -> assert false (* absurd case *))
      | Green (lvl, _, _, _, g0, r0, p0, n, s, b) ->
        (match b with
         | Left_big_sizes q ->
           Sd ((Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (NonEmpty (lvl,
             SomeGreen, NoRed, (Only_path (lvl, SomeGreen, NoRed, (Children
             (lvl, O, lvl, Coq_true, Only, Only, SomeGreen, SomeYellow,
             SomeOrange, NoRed, (Hole (lvl, Only)), (Green (lvl,
             (add (S (S (S (S (S (S (S (S O)))))))) q),
             (add (S (S (S (S (S (S O)))))) (S (S O))), Only, g0, r0, p0, n,
             (inject6 (S (S O)) s x1 x2 x3 x4 x5 x6), (Only_big_sizes (q,
             O)))))))))))
         | _ -> assert false (* absurd case *))
      | Red (lvl, _, _, _, p0, n, s, b) ->
        (match b with
         | Left_big_sizes q ->
           Sd ((Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (NonEmpty (lvl,
             NoGreen, SomeRed, (Only_path (lvl, NoGreen, SomeRed, (Children
             (lvl, O, lvl, Coq_true, Only, Only, NoGreen, SomeYellow,
             SomeOrange, SomeRed, (Hole (lvl, Only)), (Red (lvl,
             (add (S (S (S (S (S O))))) q),
             (add (S (S (S (S (S (S O)))))) (S (S O))), Only, p0, n,
             (inject6 (S (S O)) s x1 x2 x3 x4 x5 x6), (Only_big_sizes (q, (S
             (let rec add0 n0 m =
                match n0 with
                | O -> m
                | S p1 -> S (add0 p1 m)
              in add0 O (S (S O)))))))))))))))
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Left_big_sizes q ->
        Sd ((Mix (g, NoYellow, NoOrange, r)), (NonEmpty (lvl, g, r,
          (Only_path (lvl, g, r, (Children (lvl, (S len), (S (add len lvl)),
          Coq_false, Only, k2, g, SomeYellow, NoOrange, r, (Yellow (lvl, len,
          (add (S (S (S (S (S (S (S O))))))) q),
          (add (S (S (S (S (S (S O)))))) (S (S O))), Only, k2, p0, p1,
          (inject6 (S (S O)) s x1 x2 x3 x4 x5 x6), (Only_big_sizes (q, (S
          O))))), t0)))))))
      | _ -> assert false (* absurd case *))
   | Orange (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Left_big_sizes q ->
        Sd ((Mix (g, NoYellow, NoOrange, r)), (NonEmpty (lvl, g, r,
          (Only_path (lvl, g, r, (Children (lvl, (S len), (S (add len lvl)),
          Coq_false, Only, k2, g, NoYellow, SomeOrange, r, (Orange (lvl, len,
          (add (S (S (S (S (S (S O)))))) q),
          (add (S (S (S (S (S (S O)))))) (S (S O))), Only, k2, p0, p1,
          (inject6 (S (S O)) s x1 x2 x3 x4 x5 x6), (Only_big_sizes (q, (S (S
          O)))))), t0)))))))
      | _ -> assert false (* absurd case *))
   | _ -> assert false (* absurd case *))

(** val semi_of_right :
    nat -> color -> 'a1 stored_triple -> 'a1 stored_triple -> 'a1
    stored_triple -> 'a1 stored_triple -> 'a1 stored_triple -> 'a1
    stored_triple -> 'a1 path -> 'a1 sdeque **)

let semi_of_right _ _ x1 x2 x3 x4 x5 x6 = function
| Children (_, _, _, _, _, _, g, _, _, r, t, t0) ->
  (match t with
   | Hole (_, _) ->
     (match t0 with
      | Small (lvl, _, _, _, p0, s, s0) ->
        (match s0 with
         | Right_small_sizes q ->
           let Coq_pair (s1, s2) = two p0 in
           Sd ((Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (NonEmpty (lvl,
           SomeGreen, NoRed, (Only_path (lvl, SomeGreen, NoRed, (Children
           (lvl, O, lvl, Coq_true, Only, Only, SomeGreen, SomeYellow,
           SomeOrange, NoRed, (Hole (lvl, Only)), (Small (lvl,
           (add (S (S (S (S (S (S O)))))) (S (S
             (add (S (S (S (S (S O))))) q)))), O, Only,
           (push6 (S (S (add (S (S (S (S (S O))))) q))) x1 x2 x3 x4 x5 x6
             (push2 (add (S (S (S (S (S O))))) q) s1 s2 s)), empty,
           (Only_small_sizes (S
           (let rec add0 n m =
              match n with
              | O -> m
              | S p1 -> S (add0 p1 m)
            in add0 (S (S (S (S O)))) (S (S (add (S (S (S (S (S O))))) q)))))))))))))))
         | _ -> assert false (* absurd case *))
      | Green (lvl, _, _, _, g0, r0, p0, n, s, b) ->
        (match b with
         | Right_big_sizes q ->
           Sd ((Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (NonEmpty (lvl,
             SomeGreen, NoRed, (Only_path (lvl, SomeGreen, NoRed, (Children
             (lvl, O, lvl, Coq_true, Only, Only, SomeGreen, SomeYellow,
             SomeOrange, NoRed, (Hole (lvl, Only)), (Green (lvl,
             (add (S (S (S (S (S (S O)))))) (S (S O))),
             (add (S (S (S (S (S (S (S (S O)))))))) q), Only, g0, r0,
             (push6 (S (S O)) x1 x2 x3 x4 x5 x6 p0), n, s, (Only_big_sizes
             (O, q)))))))))))
         | _ -> assert false (* absurd case *))
      | Red (lvl, _, _, _, p0, n, s, b) ->
        (match b with
         | Right_big_sizes q ->
           Sd ((Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (NonEmpty (lvl,
             NoGreen, SomeRed, (Only_path (lvl, NoGreen, SomeRed, (Children
             (lvl, O, lvl, Coq_true, Only, Only, NoGreen, SomeYellow,
             SomeOrange, SomeRed, (Hole (lvl, Only)), (Red (lvl,
             (add (S (S (S (S (S (S O)))))) (S (S O))),
             (add (S (S (S (S (S O))))) q), Only,
             (push6 (S (S O)) x1 x2 x3 x4 x5 x6 p0), n, s, (Only_big_sizes
             ((S
             (let rec add0 n0 m =
                match n0 with
                | O -> m
                | S p1 -> S (add0 p1 m)
              in add0 O (S (S O)))), q)))))))))))
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Right_big_sizes q ->
        Sd ((Mix (g, NoYellow, NoOrange, r)), (NonEmpty (lvl, g, r,
          (Only_path (lvl, g, r, (Children (lvl, (S len), (S (add len lvl)),
          Coq_false, Only, k2, g, SomeYellow, NoOrange, r, (Yellow (lvl, len,
          (add (S (S (S (S (S (S O)))))) (S (S O))),
          (add (S (S (S (S (S (S (S O))))))) q), Only, k2,
          (push6 (S (S O)) x1 x2 x3 x4 x5 x6 p0), p1, s, (Only_big_sizes ((S
          O), q)))), t0)))))))
      | _ -> assert false (* absurd case *))
   | Orange (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Right_big_sizes q ->
        Sd ((Mix (g, NoYellow, NoOrange, r)), (NonEmpty (lvl, g, r,
          (Only_path (lvl, g, r, (Children (lvl, (S len), (S (add len lvl)),
          Coq_false, Only, k2, g, NoYellow, SomeOrange, r, (Orange (lvl, len,
          (add (S (S (S (S (S (S O)))))) (S (S O))),
          (add (S (S (S (S (S (S O)))))) q), Only, k2,
          (push6 (S (S O)) x1 x2 x3 x4 x5 x6 p0), p1, s, (Only_big_sizes ((S
          (S O)), q)))), t0)))))))
      | _ -> assert false (* absurd case *))
   | _ -> assert false (* absurd case *))

(** val pop_green_left :
    nat -> 'a1 path -> ('a1 stored_triple, 'a1 path_uncolored) prod **)

let pop_green_left _ = function
| Children (_, _, _, _, _, _, _, _, _, _, t, t0) ->
  (match t with
   | Hole (_, _) ->
     (match t0 with
      | Small (lvl, _, _, _, p0, s, s0) ->
        (match s0 with
         | Left_small_sizes q ->
           let Coq_pair (s1, t1) =
             pop (S
               (let rec add0 n m =
                  match n with
                  | O -> m
                  | S p1 -> S (add0 p1 m)
                in add0 (S (S (S O))) q)) p0
           in
           (match has5 q t1 with
            | Coq_inl p1 ->
              let Coq_pair (p2, s2) = p1 in
              let Coq_pair (p3, s3) = p2 in
              let Coq_pair (s4, s5) = p3 in
              let Coq_pair (s6, s7) = two s in
              Coq_pair (s1, (Six (s4, s5, s3, s2, s6, s7)))
            | Coq_inr p1 ->
              Coq_pair (s1, (AnyColor ((Mix (SomeGreen, NoYellow, NoOrange,
                NoRed)), (Children (lvl, O, lvl, Coq_true, Left, Left,
                SomeGreen, SomeYellow, SomeOrange, NoRed, (Hole (lvl, Left)),
                (Small (lvl,
                (add (S (S (S (S (S O)))))
                  (PeanoNat.Nat.iter (S (S (S (S (S O))))) PeanoNat.Nat.pred
                    (add (S (S (S (S O)))) q))), (S (S O)), Left, p1, s,
                (Left_small_sizes
                (PeanoNat.Nat.iter (S (S (S (S (S O))))) PeanoNat.Nat.pred
                  (add (S (S (S (S O)))) q)))))))))))
         | _ -> assert false (* absurd case *))
      | Green (lvl, _, _, _, g, r, p0, n, s, b) ->
        (match b with
         | Left_big_sizes q ->
           let Coq_pair (s0, t1) =
             pop (S
               (let rec add0 n0 m =
                  match n0 with
                  | O -> m
                  | S p1 -> S (add0 p1 m)
                in add0 (S (S (S (S (S (S O)))))) q)) p0
           in
           let Pref_left (len, _, k, g0, r0, p1, t2) =
             to_pref_left (S lvl) (Mix (g, NoYellow, NoOrange, r)) n
           in
           Coq_pair (s0, (AnyColor ((Mix (g0, NoYellow, NoOrange, r0)),
           (Children (lvl, (S len), (add len (S lvl)), Coq_false, Left, k,
           g0, SomeYellow, NoOrange, r0, (Yellow (lvl, len, (S
           (let rec add0 n0 m =
              match n0 with
              | O -> m
              | S p2 -> S (add0 p2 m)
            in add0 (S (S (S (S (S (S O)))))) q)), (S (S O)), Left, k, t1,
           p1, s, (Left_big_sizes q))), t2)))))
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Left_big_sizes q ->
        let Coq_pair (s0, t1) =
          pop (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p2 -> S (add0 p2 m)
             in add0 (S (S (S (S (S O))))) q)) p0
        in
        let Pref_right (len0, _, k, g, r, p2, t2) =
          to_pref_right (S lvl) len (S (add len lvl)) k2 p1 t0
        in
        Coq_pair (s0, (AnyColor ((Mix (g, NoYellow, NoOrange, r)), (Children
        (lvl, (S len0), (add len0 (S lvl)), Coq_false, Left, k, g, NoYellow,
        SomeOrange, r, (Orange (lvl, len0, (S
        (let rec add0 n m =
           match n with
           | O -> m
           | S p3 -> S (add0 p3 m)
         in add0 (S (S (S (S (S O))))) q)), (S (S O)), Left, k, t1, p2, s,
        (Left_big_sizes q))), t2)))))
      | _ -> assert false (* absurd case *))
   | Orange (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Left_big_sizes q ->
        let Coq_pair (s0, t1) =
          pop (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p2 -> S (add0 p2 m)
             in add0 (S (S (S (S O)))) q)) p0
        in
        Coq_pair (s0, (AnyColor ((Mix (NoGreen, NoYellow, NoOrange,
        SomeRed)), (Children (lvl, O, lvl, Coq_true, Left, Left, NoGreen,
        SomeYellow, SomeOrange, SomeRed, (Hole (lvl, Left)), (Red (lvl, (S
        (let rec add0 n m =
           match n with
           | O -> m
           | S p2 -> S (add0 p2 m)
         in add0 (S (S (S (S O)))) q)), (S (S O)), Left, t1,
        (no_pref (S lvl) len (S (add len lvl)) k2 p1 t0), s, (Left_big_sizes
        q))))))))
      | _ -> assert false (* absurd case *))
   | _ -> assert false (* absurd case *))

(** val eject_green_right :
    nat -> 'a1 path -> ('a1 path_uncolored, 'a1 stored_triple) prod **)

let eject_green_right _ = function
| Children (_, _, _, _, _, _, _, _, _, _, t, t0) ->
  (match t with
   | Hole (_, _) ->
     (match t0 with
      | Small (lvl, _, _, _, p0, s, s0) ->
        (match s0 with
         | Right_small_sizes q ->
           let Coq_pair (t1, s1) =
             eject (S
               (let rec add0 n m =
                  match n with
                  | O -> m
                  | S p1 -> S (add0 p1 m)
                in add0 (S (S (S O))) q)) s
           in
           (match has5 q t1 with
            | Coq_inl p1 ->
              let Coq_pair (p2, s2) = p1 in
              let Coq_pair (p3, s3) = p2 in
              let Coq_pair (s4, s5) = p3 in
              let Coq_pair (s6, s7) = two p0 in
              Coq_pair ((Six (s6, s7, s4, s5, s3, s2)), s1)
            | Coq_inr p1 ->
              Coq_pair ((AnyColor ((Mix (SomeGreen, NoYellow, NoOrange,
                NoRed)), (Children (lvl, O, lvl, Coq_true, Right, Right,
                SomeGreen, SomeYellow, SomeOrange, NoRed, (Hole (lvl,
                Right)), (Small (lvl, (S (S O)),
                (add (S (S (S (S (S O)))))
                  (PeanoNat.Nat.iter (S (S (S (S (S O))))) PeanoNat.Nat.pred
                    (add (S (S (S (S O)))) q))), Right, p0, p1,
                (Right_small_sizes
                (PeanoNat.Nat.iter (S (S (S (S (S O))))) PeanoNat.Nat.pred
                  (add (S (S (S (S O)))) q))))))))), s1))
         | _ -> assert false (* absurd case *))
      | Green (lvl, _, _, _, g, r, p0, n, s, b) ->
        (match b with
         | Right_big_sizes q ->
           let Coq_pair (t1, s0) =
             eject (S
               (let rec add0 n0 m =
                  match n0 with
                  | O -> m
                  | S p1 -> S (add0 p1 m)
                in add0 (S (S (S (S (S (S O)))))) q)) s
           in
           let Pref_left (len, _, k, g0, r0, p1, t2) =
             to_pref_left (S lvl) (Mix (g, NoYellow, NoOrange, r)) n
           in
           Coq_pair ((AnyColor ((Mix (g0, NoYellow, NoOrange, r0)), (Children
           (lvl, (S len), (add len (S lvl)), Coq_false, Right, k, g0,
           SomeYellow, NoOrange, r0, (Yellow (lvl, len, (S (S O)), (S
           (let rec add0 n0 m =
              match n0 with
              | O -> m
              | S p2 -> S (add0 p2 m)
            in add0 (S (S (S (S (S (S O)))))) q)), Right, k, p0, p1, t1,
           (Right_big_sizes q))), t2)))), s0)
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Right_big_sizes q ->
        let Coq_pair (t1, s0) =
          eject (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p2 -> S (add0 p2 m)
             in add0 (S (S (S (S (S O))))) q)) s
        in
        let Pref_right (len0, _, k, g, r, p2, t2) =
          to_pref_right (S lvl) len (S (add len lvl)) k2 p1 t0
        in
        Coq_pair ((AnyColor ((Mix (g, NoYellow, NoOrange, r)), (Children
        (lvl, (S len0), (add len0 (S lvl)), Coq_false, Right, k, g, NoYellow,
        SomeOrange, r, (Orange (lvl, len0, (S (S O)), (S
        (let rec add0 n m =
           match n with
           | O -> m
           | S p3 -> S (add0 p3 m)
         in add0 (S (S (S (S (S O))))) q)), Right, k, p0, p2, t1,
        (Right_big_sizes q))), t2)))), s0)
      | _ -> assert false (* absurd case *))
   | Orange (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Right_big_sizes q ->
        let Coq_pair (t1, s0) =
          eject (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p2 -> S (add0 p2 m)
             in add0 (S (S (S (S O)))) q)) s
        in
        Coq_pair ((AnyColor ((Mix (NoGreen, NoYellow, NoOrange, SomeRed)),
        (Children (lvl, O, lvl, Coq_true, Right, Right, NoGreen, SomeYellow,
        SomeOrange, SomeRed, (Hole (lvl, Right)), (Red (lvl, (S (S O)), (S
        (let rec add0 n m =
           match n with
           | O -> m
           | S p2 -> S (add0 p2 m)
         in add0 (S (S (S (S O)))) q)), Right, p0,
        (no_pref (S lvl) len (S (add len lvl)) k2 p1 t0), t1,
        (Right_big_sizes q))))))), s0)
      | _ -> assert false (* absurd case *))
   | _ -> assert false (* absurd case *))

(** val pop_green :
    nat -> 'a1 non_empty_cdeque -> ('a1 stored_triple, 'a1 sdeque) prod **)

let pop_green _ = function
| Only_path (_, _, _, p) ->
  let Children (_, _, _, _, _, _, _, _, _, _, t, t0) = p in
  (match t with
   | Hole (_, _) ->
     (match t0 with
      | Small (lvl, _, _, _, p0, s, s0) ->
        (match s0 with
         | Only_small_sizes q ->
           let Coq_pair (s1, t1) = pop q p0 in
           (match has1 q t1 with
            | Some p1 ->
              Coq_pair (s1, (Sd ((Mix (SomeGreen, NoYellow, NoOrange,
                NoRed)), (NonEmpty (lvl, SomeGreen, NoRed, (Only_path (lvl,
                SomeGreen, NoRed, (Children (lvl, O, lvl, Coq_true, Only,
                Only, SomeGreen, SomeYellow, SomeOrange, NoRed, (Hole (lvl,
                Only)), (Small (lvl,
                (add (S O) (PeanoNat.Nat.iter (S O) PeanoNat.Nat.pred q)), O,
                Only, p1, s, (Only_small_sizes
                (PeanoNat.Nat.iter (S O) PeanoNat.Nat.pred q)))))))))))))
            | None ->
              Coq_pair (s1, (Sd ((Mix (SomeGreen, NoYellow, NoOrange,
                NoRed)), (Empty lvl)))))
         | _ -> assert false (* absurd case *))
      | Green (lvl, _, _, _, g, r, p0, n, s, b) ->
        (match b with
         | Only_big_sizes (qp, qs) ->
           let Coq_pair (s0, t1) =
             pop (S
               (let rec add0 n0 m =
                  match n0 with
                  | O -> m
                  | S p1 -> S (add0 p1 m)
                in add0 (S (S (S (S (S (S O)))))) qp)) p0
           in
           let Pref_left (len, _, k, g0, r0, p1, t2) =
             to_pref_left (S lvl) (Mix (g, NoYellow, NoOrange, r)) n
           in
           Coq_pair (s0, (Sd ((Mix (g0, NoYellow, NoOrange, r0)), (NonEmpty
           (lvl, g0, r0, (Only_path (lvl, g0, r0, (Children (lvl, (S len),
           (add len (S lvl)), Coq_false, Only, k, g0, SomeYellow, NoOrange,
           r0, (Yellow (lvl, len, (S
           (let rec add0 n0 m =
              match n0 with
              | O -> m
              | S p2 -> S (add0 p2 m)
            in add0 (S (S (S (S (S (S O)))))) qp)),
           (add (S (S (S (S (S (S (S (S O)))))))) qs), Only, k, t1, p1, s,
           (Only_big_sizes (qp, (S
           (let rec add0 n0 m =
              match n0 with
              | O -> m
              | S p2 -> S (add0 p2 m)
            in add0 O qs)))))), t2)))))))))
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Only_big_sizes (qp, qs) ->
        let Coq_pair (s0, t1) =
          pop (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p2 -> S (add0 p2 m)
             in add0 (S (S (S (S (S O))))) qp)) p0
        in
        let Pref_right (len0, _, k, g, r, p2, t2) =
          to_pref_right (S lvl) len (S (add len lvl)) k2 p1 t0
        in
        Coq_pair (s0, (Sd ((Mix (g, NoYellow, NoOrange, r)), (NonEmpty (lvl,
        g, r, (Only_path (lvl, g, r, (Children (lvl, (S len0),
        (add len0 (S lvl)), Coq_false, Only, k, g, NoYellow, SomeOrange, r,
        (Orange (lvl, len0, (S
        (let rec add0 n m =
           match n with
           | O -> m
           | S p3 -> S (add0 p3 m)
         in add0 (S (S (S (S (S O))))) qp)),
        (add (S (S (S (S (S (S (S O))))))) qs), Only, k, t1, p2, s,
        (Only_big_sizes (qp, (S
        (let rec add0 n m =
           match n with
           | O -> m
           | S p3 -> S (add0 p3 m)
         in add0 O qs)))))), t2)))))))))
      | _ -> assert false (* absurd case *))
   | Orange (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Only_big_sizes (qp, qs) ->
        let Coq_pair (s0, t1) =
          pop (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p2 -> S (add0 p2 m)
             in add0 (S (S (S (S O)))) qp)) p0
        in
        Coq_pair (s0, (Sd ((Mix (NoGreen, NoYellow, NoOrange, SomeRed)),
        (NonEmpty (lvl, NoGreen, SomeRed, (Only_path (lvl, NoGreen, SomeRed,
        (Children (lvl, O, lvl, Coq_true, Only, Only, NoGreen, SomeYellow,
        SomeOrange, SomeRed, (Hole (lvl, Only)), (Red (lvl, (S
        (let rec add0 n m =
           match n with
           | O -> m
           | S p2 -> S (add0 p2 m)
         in add0 (S (S (S (S O)))) qp)), (add (S (S (S (S (S (S O)))))) qs),
        Only, t1, (no_pref (S lvl) len (S (add len lvl)) k2 p1 t0), s,
        (Only_big_sizes (qp, (S
        (let rec add0 n m =
           match n with
           | O -> m
           | S p2 -> S (add0 p2 m)
         in add0 O qs)))))))))))))))
      | _ -> assert false (* absurd case *))
   | _ -> assert false (* absurd case *))
| Pair_green (lvl, p, p0) ->
  let Coq_pair (s, p1) = pop_green_left lvl p in
  (match p1 with
   | Six (s0, s1, s2, s3, s4, s5) ->
     Coq_pair (s,
       (semi_of_right lvl (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) s0 s1
         s2 s3 s4 s5 p0))
   | AnyColor (c, p2) ->
     Coq_pair (s, (Sd ((Mix (NoGreen, NoYellow, NoOrange, SomeRed)),
       (NonEmpty (lvl, NoGreen, SomeRed, (Pair_red (lvl, c, (Mix (SomeGreen,
       NoYellow, NoOrange, NoRed)), p2, p0))))))))
| Pair_red (_, _, _, _, _) -> assert false (* absurd case *)

(** val eject_green :
    nat -> 'a1 non_empty_cdeque -> ('a1 sdeque, 'a1 stored_triple) prod **)

let eject_green _ = function
| Only_path (_, _, _, p) ->
  let Children (_, _, _, _, _, _, _, _, _, _, t, t0) = p in
  (match t with
   | Hole (_, _) ->
     (match t0 with
      | Small (lvl, _, _, _, p0, s, s0) ->
        (match s0 with
         | Only_small_sizes q ->
           let Coq_pair (t1, s1) = eject q p0 in
           (match has1 q t1 with
            | Some p1 ->
              Coq_pair ((Sd ((Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
                (NonEmpty (lvl, SomeGreen, NoRed, (Only_path (lvl, SomeGreen,
                NoRed, (Children (lvl, O, lvl, Coq_true, Only, Only,
                SomeGreen, SomeYellow, SomeOrange, NoRed, (Hole (lvl, Only)),
                (Small (lvl,
                (add (S O) (PeanoNat.Nat.iter (S O) PeanoNat.Nat.pred q)), O,
                Only, p1, s, (Only_small_sizes
                (PeanoNat.Nat.iter (S O) PeanoNat.Nat.pred q)))))))))))), s1)
            | None ->
              Coq_pair ((Sd ((Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
                (Empty lvl))), s1))
         | _ -> assert false (* absurd case *))
      | Green (lvl, _, _, _, g, r, p0, n, s, b) ->
        (match b with
         | Only_big_sizes (qp, qs) ->
           let Coq_pair (t1, s0) =
             eject (S
               (let rec add0 n0 m =
                  match n0 with
                  | O -> m
                  | S p1 -> S (add0 p1 m)
                in add0 (S (S (S (S (S (S O)))))) qs)) s
           in
           let Pref_left (len, _, k, g0, r0, p1, t2) =
             to_pref_left (S lvl) (Mix (g, NoYellow, NoOrange, r)) n
           in
           Coq_pair ((Sd ((Mix (g0, NoYellow, NoOrange, r0)), (NonEmpty (lvl,
           g0, r0, (Only_path (lvl, g0, r0, (Children (lvl, (S len),
           (add len (S lvl)), Coq_false, Only, k, g0, SomeYellow, NoOrange,
           r0, (Yellow (lvl, len, (add (S (S (S (S (S (S (S (S O)))))))) qp),
           (S
           (let rec add0 n0 m =
              match n0 with
              | O -> m
              | S p2 -> S (add0 p2 m)
            in add0 (S (S (S (S (S (S O)))))) qs)), Only, k, p0, p1, t1,
           (Only_big_sizes ((S
           (let rec add0 n0 m =
              match n0 with
              | O -> m
              | S p2 -> S (add0 p2 m)
            in add0 O qp)), qs)))), t2)))))))), s0)
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Only_big_sizes (qp, qs) ->
        let Coq_pair (t1, s0) =
          eject (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p2 -> S (add0 p2 m)
             in add0 (S (S (S (S (S O))))) qs)) s
        in
        let Pref_right (len0, _, k, g, r, p2, t2) =
          to_pref_right (S lvl) len (S (add len lvl)) k2 p1 t0
        in
        Coq_pair ((Sd ((Mix (g, NoYellow, NoOrange, r)), (NonEmpty (lvl, g,
        r, (Only_path (lvl, g, r, (Children (lvl, (S len0),
        (add len0 (S lvl)), Coq_false, Only, k, g, NoYellow, SomeOrange, r,
        (Orange (lvl, len0, (add (S (S (S (S (S (S (S O))))))) qp), (S
        (let rec add0 n m =
           match n with
           | O -> m
           | S p3 -> S (add0 p3 m)
         in add0 (S (S (S (S (S O))))) qs)), Only, k, p0, p2, t1,
        (Only_big_sizes ((S
        (let rec add0 n m =
           match n with
           | O -> m
           | S p3 -> S (add0 p3 m)
         in add0 O qp)), qs)))), t2)))))))), s0)
      | _ -> assert false (* absurd case *))
   | Orange (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Only_big_sizes (qp, qs) ->
        let Coq_pair (t1, s0) =
          eject (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p2 -> S (add0 p2 m)
             in add0 (S (S (S (S O)))) qs)) s
        in
        Coq_pair ((Sd ((Mix (NoGreen, NoYellow, NoOrange, SomeRed)),
        (NonEmpty (lvl, NoGreen, SomeRed, (Only_path (lvl, NoGreen, SomeRed,
        (Children (lvl, O, lvl, Coq_true, Only, Only, NoGreen, SomeYellow,
        SomeOrange, SomeRed, (Hole (lvl, Only)), (Red (lvl,
        (add (S (S (S (S (S (S O)))))) qp), (S
        (let rec add0 n m =
           match n with
           | O -> m
           | S p2 -> S (add0 p2 m)
         in add0 (S (S (S (S O)))) qs)), Only, p0,
        (no_pref (S lvl) len (S (add len lvl)) k2 p1 t0), t1, (Only_big_sizes
        ((S
        (let rec add0 n m =
           match n with
           | O -> m
           | S p2 -> S (add0 p2 m)
         in add0 O qp)), qs)))))))))))), s0)
      | _ -> assert false (* absurd case *))
   | _ -> assert false (* absurd case *))
| Pair_green (lvl, p, p0) ->
  let Coq_pair (p1, s) = eject_green_right lvl p0 in
  (match p1 with
   | Six (s0, s1, s2, s3, s4, s5) ->
     Coq_pair
       ((semi_of_left lvl (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) p s0
          s1 s2 s3 s4 s5), s)
   | AnyColor (c, p2) ->
     Coq_pair ((Sd ((Mix (NoGreen, NoYellow, NoOrange, SomeRed)), (NonEmpty
       (lvl, NoGreen, SomeRed, (Pair_red (lvl, (Mix (SomeGreen, NoYellow,
       NoOrange, NoRed)), c, p, p2)))))), s))
| Pair_red (_, _, _, _, _) -> assert false (* absurd case *)

(** val pop_stored : nat -> 'a1 non_empty_cdeque -> 'a1 unstored **)

let pop_stored lvl cd =
  let Coq_pair (s, s0) = pop_green (S lvl) cd in
  (match s with
   | ST_ground _ -> assert false (* absurd case *)
   | ST_small (_, q, p) -> Unstored (q, p, s0)
   | ST_triple (_, qp, qs, c, p, c0, s1) ->
     Unstored (qp, p,
       (concat_semi (S lvl) (Sd (c, c0))
         (push_semi (S lvl) (ST_small (lvl, qs, s1)) s0))))

(** val eject_stored : nat -> 'a1 non_empty_cdeque -> 'a1 unstored **)

let eject_stored lvl cd =
  let Coq_pair (s, s0) = eject_green (S lvl) cd in
  (match s0 with
   | ST_ground _ -> assert false (* absurd case *)
   | ST_small (_, q, p) -> Unstored (q, p, s)
   | ST_triple (_, qp, qs, c, p, c0, s1) ->
     Unstored (qs, s1,
       (concat_semi (S lvl) (inject_semi (S lvl) s (ST_small (lvl, qp, p)))
         (Sd (c, c0)))))

(** val unsandwich_green : nat -> 'a1 non_empty_cdeque -> 'a1 sandwich **)

let unsandwich_green _ = function
| Only_path (_, _, _, p) ->
  let Children (_, _, _, _, _, _, _, _, _, _, t, t0) = p in
  (match t with
   | Hole (_, _) ->
     (match t0 with
      | Small (lvl, _, _, _, p0, s, s0) ->
        (match s0 with
         | Only_small_sizes q ->
           let Coq_pair (s1, t1) = pop q p0 in
           (match has1 q t1 with
            | Some p1 ->
              let Coq_pair (t2, s2) =
                eject (PeanoNat.Nat.iter (S O) PeanoNat.Nat.pred q) p1
              in
              (match has1 (PeanoNat.Nat.iter (S O) PeanoNat.Nat.pred q) t2 with
               | Some p2 ->
                 let only = Only_path (lvl, SomeGreen, NoRed, (Children (lvl,
                   O, lvl, Coq_true, Only, Only, SomeGreen, SomeYellow,
                   SomeOrange, NoRed, (Hole (lvl, Only)), (Small (lvl,
                   (add (S O)
                     (PeanoNat.Nat.iter (S O) PeanoNat.Nat.pred
                       (PeanoNat.Nat.iter (S O) PeanoNat.Nat.pred q))), O,
                   Only, p2, s, (Only_small_sizes
                   (PeanoNat.Nat.iter (S O) PeanoNat.Nat.pred
                     (PeanoNat.Nat.iter (S O) PeanoNat.Nat.pred q))))))))
                 in
                 Sandwich (s1, (Sd ((Mix (SomeGreen, NoYellow, NoOrange,
                 NoRed)), (NonEmpty (lvl, SomeGreen, NoRed, only)))), s2)
               | None ->
                 Sandwich (s1, (Sd ((Mix (SomeGreen, NoYellow, NoOrange,
                   NoRed)), (Empty lvl))), s2))
            | None -> Alone s1)
         | _ -> assert false (* absurd case *))
      | Green (lvl, _, _, _, g, r, p0, n, s, b) ->
        (match b with
         | Only_big_sizes (qp, qs) ->
           let Coq_pair (s0, t1) =
             pop (S
               (let rec add0 n0 m =
                  match n0 with
                  | O -> m
                  | S p1 -> S (add0 p1 m)
                in add0 (S (S (S (S (S (S O)))))) qp)) p0
           in
           let Coq_pair (t2, s1) =
             eject (S
               (let rec add0 n0 m =
                  match n0 with
                  | O -> m
                  | S p1 -> S (add0 p1 m)
                in add0 (S (S (S (S (S (S O)))))) qs)) s
           in
           let Pref_left (len, _, k, g0, r0, p1, t3) =
             to_pref_left (S lvl) (Mix (g, NoYellow, NoOrange, r)) n
           in
           let only = Only_path (lvl, g0, r0, (Children (lvl, (S len),
             (add len (S lvl)), Coq_false, Only, k, g0, SomeYellow, NoOrange,
             r0, (Yellow (lvl, len, (S
             (let rec add0 n0 m =
                match n0 with
                | O -> m
                | S p2 -> S (add0 p2 m)
              in add0 (S (S (S (S (S (S O)))))) qp)), (S
             (let rec add0 n0 m =
                match n0 with
                | O -> m
                | S p2 -> S (add0 p2 m)
              in add0 (S (S (S (S (S (S O)))))) qs)), Only, k, t1, p1, t2,
             (Only_big_sizes (qp, qs)))), t3)))
           in
           Sandwich (s0, (Sd ((Mix (g0, NoYellow, NoOrange, r0)), (NonEmpty
           (lvl, g0, r0, only)))), s1)
         | _ -> assert false (* absurd case *))
      | _ -> assert false (* absurd case *))
   | Yellow (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Only_big_sizes (qp, qs) ->
        let Coq_pair (s0, t1) =
          pop (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p2 -> S (add0 p2 m)
             in add0 (S (S (S (S (S O))))) qp)) p0
        in
        let Coq_pair (t2, s1) =
          eject (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p2 -> S (add0 p2 m)
             in add0 (S (S (S (S (S O))))) qs)) s
        in
        let Pref_right (len0, _, k, g, r, p2, t3) =
          to_pref_right (S lvl) len (S (add len lvl)) k2 p1 t0
        in
        let only = Only_path (lvl, g, r, (Children (lvl, (S len0),
          (add len0 (S lvl)), Coq_false, Only, k, g, NoYellow, SomeOrange, r,
          (Orange (lvl, len0, (S
          (let rec add0 n m =
             match n with
             | O -> m
             | S p3 -> S (add0 p3 m)
           in add0 (S (S (S (S (S O))))) qp)), (S
          (let rec add0 n m =
             match n with
             | O -> m
             | S p3 -> S (add0 p3 m)
           in add0 (S (S (S (S (S O))))) qs)), Only, k, t1, p2, t2,
          (Only_big_sizes (qp, qs)))), t3)))
        in
        Sandwich (s0, (Sd ((Mix (g, NoYellow, NoOrange, r)), (NonEmpty (lvl,
        g, r, only)))), s1)
      | _ -> assert false (* absurd case *))
   | Orange (lvl, len, _, _, _, k2, p0, p1, s, b) ->
     (match b with
      | Only_big_sizes (qp, qs) ->
        let Coq_pair (s0, t1) =
          pop (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p2 -> S (add0 p2 m)
             in add0 (S (S (S (S O)))) qp)) p0
        in
        let Coq_pair (t2, s1) =
          eject (S
            (let rec add0 n m =
               match n with
               | O -> m
               | S p2 -> S (add0 p2 m)
             in add0 (S (S (S (S O)))) qs)) s
        in
        let only = Only_path (lvl, NoGreen, SomeRed, (Children (lvl, O, lvl,
          Coq_true, Only, Only, NoGreen, SomeYellow, SomeOrange, SomeRed,
          (Hole (lvl, Only)), (Red (lvl, (S
          (let rec add0 n m =
             match n with
             | O -> m
             | S p2 -> S (add0 p2 m)
           in add0 (S (S (S (S O)))) qp)), (S
          (let rec add0 n m =
             match n with
             | O -> m
             | S p2 -> S (add0 p2 m)
           in add0 (S (S (S (S O)))) qs)), Only, t1,
          (no_pref (S lvl) len (S (add len lvl)) k2 p1 t0), t2,
          (Only_big_sizes (qp, qs)))))))
        in
        Sandwich (s0, (Sd ((Mix (NoGreen, NoYellow, NoOrange, SomeRed)),
        (NonEmpty (lvl, NoGreen, SomeRed, only)))), s1)
      | _ -> assert false (* absurd case *))
   | _ -> assert false (* absurd case *))
| Pair_green (lvl, p, p0) ->
  let Coq_pair (s, p1) = pop_green_left lvl p in
  (match p1 with
   | Six (s0, s1, s2, s3, s4, s5) ->
     let Coq_pair (p2, s6) = eject_green_right lvl p0 in
     (match p2 with
      | Six (s7, s8, s9, s10, s11, s12) ->
        let only = Only_path (lvl, SomeGreen, NoRed, (Children (lvl, O, lvl,
          Coq_true, Only, Only, SomeGreen, SomeYellow, SomeOrange, NoRed,
          (Hole (lvl, Only)), (Small (lvl,
          (add (S (S (S (S (S (S O)))))) (add (S (S (S (S (S (S O)))))) O)),
          O, Only,
          (push6 (add (S (S (S (S (S (S O)))))) O) s0 s1 s2 s3 s4 s5
            (push6 O s7 s8 s9 s10 s11 s12 empty)), empty, (Only_small_sizes
          (S
          (let rec add0 n m =
             match n with
             | O -> m
             | S p3 -> S (add0 p3 m)
           in add0 (S (S (S (S O)))) (add (S (S (S (S (S (S O)))))) O)))))))))
        in
        Sandwich (s, (Sd ((Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
        (NonEmpty (lvl, SomeGreen, NoRed, only)))), s6)
      | AnyColor (c, p3) ->
        Sandwich (s, (semi_of_right lvl c s0 s1 s2 s3 s4 s5 p3), s6))
   | AnyColor (c, p2) ->
     let Coq_pair (p3, s0) = eject_green_right lvl p0 in
     (match p3 with
      | Six (s1, s2, s3, s4, s5, s6) ->
        Sandwich (s, (semi_of_left lvl c p2 s1 s2 s3 s4 s5 s6), s0)
      | AnyColor (c0, p4) ->
        Sandwich (s, (Sd ((Mix (NoGreen, NoYellow, NoOrange, SomeRed)),
          (NonEmpty (lvl, NoGreen, SomeRed, (Pair_red (lvl, c, c0, p2,
          p4)))))), s0)))
| Pair_red (_, _, _, _, _) -> assert false (* absurd case *)

(** val unsandwich_stored :
    nat -> 'a1 non_empty_cdeque -> 'a1 unstored_sandwich **)

let unsandwich_stored lvl cd =
  match unsandwich_green (S lvl) cd with
  | Alone s ->
    (match s with
     | ST_ground _ -> assert false (* absurd case *)
     | ST_small (_, q, p) -> Unstored_alone (q, p)
     | ST_triple (_, qp, qs, c, p, c0, s0) ->
       Unstored_sandwich (qp, qs, p, (Sd (c, c0)), s0))
  | Sandwich (s, s0, s1) ->
    (match s with
     | ST_ground _ -> assert false (* absurd case *)
     | ST_small (_, q, p) ->
       (match s1 with
        | ST_ground _ -> assert false (* absurd case *)
        | ST_small (_, q0, p0) -> Unstored_sandwich (q, q0, p, s0, p0)
        | ST_triple (_, qp, qs, c, p0, c0, s2) ->
          Unstored_sandwich (q, qs, p,
            (concat_semi (S lvl)
              (inject_semi (S lvl) s0 (ST_small (lvl, qp, p0))) (Sd (c, c0))),
            s2))
     | ST_triple (_, qp, qs, c, p, c0, s2) ->
       (match s1 with
        | ST_ground _ -> assert false (* absurd case *)
        | ST_small (_, q, p0) ->
          Unstored_sandwich (qp, q, p,
            (concat_semi (S lvl) (Sd (c, c0))
              (push_semi (S lvl) (ST_small (lvl, qs, s2)) s0)), p0)
        | ST_triple (_, qp0, qs0, c1, p0, c2, s3) ->
          Unstored_sandwich (qp, qs0, p,
            (concat_semi (S lvl)
              (concat_semi (S lvl) (Sd (c, c0))
                (inject_semi (S lvl)
                  (push_semi (S lvl) (ST_small (lvl, qs, s2)) s0) (ST_small
                  (lvl, qp0, p0)))) (Sd (c1, c2))), s3)))

(** val only_small :
    nat -> nat -> nat -> 'a1 prefix -> 'a1 suffix -> 'a1 triple **)

let only_small lvl qp qs p s =
  match has3p8 qs s with
  | Coq_inl p0 ->
    let Coq_pair (p1, v) = p0 in
    let Coq_pair (p2, s0) = p1 in
    let Coq_pair (p3, s1) = p2 in
    let Coq_pair (p4, s2) = p3 in
    let Coq_pair (p5, s3) = p4 in
    let Coq_pair (p6, s4) = p5 in
    let Coq_pair (p7, s5) = p6 in
    let Coq_pair (s6, s7) = p7 in
    Small (lvl,
    (add
      (add (S (S (S (S (S (S (S (S O))))))))
        (add (S (S (S (S (S (S (S (S O)))))))) qp))
      (vector_length (S (S O)) v)), O, Only,
    (Buffer.inject_vector (S (S O))
      (add (S (S (S (S (S (S (S (S O))))))))
        (add (S (S (S (S (S (S (S (S O)))))))) qp))
      (inject8 (add (S (S (S (S (S (S (S (S O)))))))) qp) p s6 s7 s5 s4 s3 s2
        s1 s0) v), empty, (Only_small_sizes (S
    (let rec add0 n m =
       match n with
       | O -> m
       | S p8 -> S (add0 p8 m)
     in add0
          (let rec add0 n m =
             match n with
             | O -> m
             | S p8 -> S (add0 p8 m)
           in add0 (S (S (S (S (S (S O))))))
                (add (S (S (S (S (S (S (S (S O)))))))) qp))
          (vector_length (S (S O)) v)))))
  | Coq_inr p0 ->
    let Coq_pair (p1, p2) = p0 in
    let Coq_pair (p3, s0) = p1 in
    let Coq_pair (s1, s2) = p3 in
    Green (lvl, (add (S (S (S (S (S (S (S (S O)))))))) qp),
    (add (S (S (S (S (S (S (S (S O))))))))
      (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S O)))))))) PeanoNat.Nat.pred
        (add (S (S (S (S (S O))))) qs))), Only, SomeGreen, NoRed, p,
    (only_single (S lvl) (ST_small (lvl, O, (triple s1 s2 s0)))), p2,
    (Only_big_sizes (qp,
    (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S O)))))))) PeanoNat.Nat.pred
      (add (S (S (S (S (S O))))) qs)))))

(** val only_green :
    nat -> nat -> nat -> 'a1 prefix -> 'a1 sdeque -> 'a1 suffix -> 'a1 triple **)

let only_green lvl qp qs p sd s =
  let Sd (_, c) = sd in
  (match c with
   | Empty _ -> only_small lvl qp qs p s
   | NonEmpty (_, g, r, n) ->
     Green (lvl, (add (S (S (S (S (S (S (S (S O)))))))) qp),
       (add (S (S (S (S (S (S (S (S O)))))))) qs), Only, g, r, p, n, s,
       (Only_big_sizes (qp, qs))))

(** val green_of_red_only : nat -> 'a1 triple -> 'a1 triple **)

let green_of_red_only _ = function
| Red (lvl, _, _, _, p, n, s, b) ->
  (match b with
   | Only_big_sizes (qp, qs) ->
     (match has8 qp p with
      | Coq_inl p0 ->
        let Coq_pair (p1, v) = p0 in
        let Coq_pair (p2, s0) = p1 in
        let Coq_pair (p3, s1) = p2 in
        let Coq_pair (p4, s2) = p3 in
        let Coq_pair (s3, s4) = p4 in
        (match has8 qs s with
         | Coq_inl p5 ->
           let Coq_pair (p6, v0) = p5 in
           let Coq_pair (p7, s5) = p6 in
           let Coq_pair (p8, s6) = p7 in
           let Coq_pair (p9, s7) = p8 in
           let Coq_pair (s8, s9) = p9 in
           (match unsandwich_stored lvl n with
            | Unstored_alone (q, p10) ->
              Small (lvl,
                (add
                  (add (S (S (S (S (S O)))))
                    (add (add (S (S (S (S (S O))))) (add (S (S (S O))) q))
                      (vector_length (S (S O)) v)))
                  (vector_length (S (S O)) v0)), O, Only,
                (inject5_vector (S (S O))
                  (add (add (S (S (S (S (S O))))) (add (S (S (S O))) q))
                    (vector_length (S (S O)) v))
                  (push5_vector (S (S O)) (add (S (S (S O))) q) s3 s4 s2 s1
                    s0 v p10) s8 s9 s7 s6 s5 v0), empty, (Only_small_sizes (S
                (let rec add0 n0 m =
                   match n0 with
                   | O -> m
                   | S p11 -> S (add0 p11 m)
                 in add0
                      (let rec add0 n0 m =
                         match n0 with
                         | O -> m
                         | S p11 -> S (add0 p11 m)
                       in add0 (S (S (S O)))
                            (add
                              (add (S (S (S (S (S O)))))
                                (add (S (S (S O))) q))
                              (vector_length (S (S O)) v)))
                      (vector_length (S (S O)) v0)))))
            | Unstored_sandwich (qp0, qs0, p10, s10, s11) ->
              only_green lvl
                (let rec add0 n0 m =
                   match n0 with
                   | O -> m
                   | S p11 -> S (add0 p11 m)
                 in add0 qp0 (vector_length (S (S O)) v))
                (let rec add0 n0 m =
                   match n0 with
                   | O -> m
                   | S p11 -> S (add0 p11 m)
                 in add0 qs0 (vector_length (S (S O)) v0))
                (push5_vector (S (S O)) (add (S (S (S O))) qp0) s3 s4 s2 s1
                  s0 v p10) s10
                (inject5_vector (S (S O)) (add (S (S (S O))) qs0) s11 s8 s9
                  s7 s6 s5 v0))
         | Coq_inr p5 ->
           let Unstored (q, p6, s5) = pop_stored lvl n in
           only_green lvl
             (let rec add0 n0 m =
                match n0 with
                | O -> m
                | S p7 -> S (add0 p7 m)
              in add0 q (vector_length (S (S O)) v))
             (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S O))))))))
               PeanoNat.Nat.pred (add (S (S (S (S (S O))))) qs))
             (push5_vector (S (S O)) (add (S (S (S O))) q) s3 s4 s2 s1 s0 v
               p6) s5 p5)
      | Coq_inr p0 ->
        (match has8 qs s with
         | Coq_inl p1 ->
           let Coq_pair (p2, v) = p1 in
           let Coq_pair (p3, s0) = p2 in
           let Coq_pair (p4, s1) = p3 in
           let Coq_pair (p5, s2) = p4 in
           let Coq_pair (s3, s4) = p5 in
           let Unstored (q, p6, s5) = eject_stored lvl n in
           only_green lvl
             (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S O))))))))
               PeanoNat.Nat.pred (add (S (S (S (S (S O))))) qp))
             (let rec add0 n0 m =
                match n0 with
                | O -> m
                | S p7 -> S (add0 p7 m)
              in add0 q (vector_length (S (S O)) v)) p0 s5
             (inject5_vector (S (S O)) (add (S (S (S O))) q) p6 s3 s4 s2 s1
               s0 v)
         | Coq_inr p1 ->
           Green (lvl,
             (add (S (S (S (S (S (S (S (S O))))))))
               (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S O))))))))
                 PeanoNat.Nat.pred (add (S (S (S (S (S O))))) qp))),
             (add (S (S (S (S (S (S (S (S O))))))))
               (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S O))))))))
                 PeanoNat.Nat.pred (add (S (S (S (S (S O))))) qs))), Only,
             SomeGreen, NoRed, p0, n, p1, (Only_big_sizes
             ((PeanoNat.Nat.iter (S (S (S (S (S (S (S (S O))))))))
                PeanoNat.Nat.pred (add (S (S (S (S (S O))))) qp)),
             (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S O))))))))
               PeanoNat.Nat.pred (add (S (S (S (S (S O))))) qs)))))))
   | _ -> assert false (* absurd case *))
| _ -> assert false (* absurd case *)

(** val green_of_red_left : nat -> 'a1 triple -> 'a1 triple **)

let green_of_red_left _ = function
| Red (lvl, _, _, _, p, n, s, b) ->
  (match b with
   | Left_big_sizes q ->
     (match has8 q p with
      | Coq_inl p0 ->
        let Coq_pair (p1, v) = p0 in
        let Coq_pair (p2, s0) = p1 in
        let Coq_pair (p3, s1) = p2 in
        let Coq_pair (p4, s2) = p3 in
        let Coq_pair (s3, s4) = p4 in
        let Unstored (q0, p5, s5) = pop_stored lvl n in
        let Sd (_, c) = s5 in
        (match c with
         | Empty _ ->
           Small (lvl,
             (add (add (S (S (S (S (S O))))) (add (S (S (S O))) q0))
               (vector_length (S (S O)) v)), (S (S O)), Left,
             (push5_vector (S (S O)) (add (S (S (S O))) q0) s3 s4 s2 s1 s0 v
               p5), s, (Left_small_sizes (S
             (let rec add0 n0 m =
                match n0 with
                | O -> m
                | S p6 -> S (add0 p6 m)
              in add0
                   (let rec add0 n0 m =
                      match n0 with
                      | O -> m
                      | S p6 -> S (add0 p6 m)
                    in add0 (S (S O)) q0) (vector_length (S (S O)) v)))))
         | NonEmpty (_, g, r, n0) ->
           Green (lvl,
             (add (add (S (S (S (S (S O))))) (add (S (S (S O))) q0))
               (vector_length (S (S O)) v)), (S (S O)), Left, g, r,
             (push5_vector (S (S O)) (add (S (S (S O))) q0) s3 s4 s2 s1 s0 v
               p5), n0, s, (Left_big_sizes
             (let rec add0 n1 m =
                match n1 with
                | O -> m
                | S p6 -> S (add0 p6 m)
              in add0 q0 (vector_length (S (S O)) v)))))
      | Coq_inr p0 ->
        Green (lvl,
          (add (S (S (S (S (S (S (S (S O))))))))
            (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S O))))))))
              PeanoNat.Nat.pred (add (S (S (S (S (S O))))) q))), (S (S O)),
          Left, SomeGreen, NoRed, p0, n, s, (Left_big_sizes
          (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S O))))))))
            PeanoNat.Nat.pred (add (S (S (S (S (S O))))) q)))))
   | _ -> assert false (* absurd case *))
| _ -> assert false (* absurd case *)

(** val green_of_red_right : nat -> 'a1 triple -> 'a1 triple **)

let green_of_red_right _ = function
| Red (lvl, _, _, _, p, n, s, b) ->
  (match b with
   | Right_big_sizes q ->
     (match has8 q s with
      | Coq_inl p0 ->
        let Coq_pair (p1, v) = p0 in
        let Coq_pair (p2, s0) = p1 in
        let Coq_pair (p3, s1) = p2 in
        let Coq_pair (p4, s2) = p3 in
        let Coq_pair (s3, s4) = p4 in
        let Unstored (q0, p5, s5) = eject_stored lvl n in
        let Sd (_, c) = s5 in
        (match c with
         | Empty _ ->
           Small (lvl, (S (S O)),
             (add (add (S (S (S (S (S O))))) (add (S (S (S O))) q0))
               (vector_length (S (S O)) v)), Right, p,
             (inject5_vector (S (S O)) (add (S (S (S O))) q0) p5 s3 s4 s2 s1
               s0 v), (Right_small_sizes (S
             (let rec add0 n0 m =
                match n0 with
                | O -> m
                | S p6 -> S (add0 p6 m)
              in add0
                   (let rec add0 n0 m =
                      match n0 with
                      | O -> m
                      | S p6 -> S (add0 p6 m)
                    in add0 (S (S O)) q0) (vector_length (S (S O)) v)))))
         | NonEmpty (_, g, r, n0) ->
           Green (lvl, (S (S O)),
             (add (add (S (S (S (S (S O))))) (add (S (S (S O))) q0))
               (vector_length (S (S O)) v)), Right, g, r, p, n0,
             (inject5_vector (S (S O)) (add (S (S (S O))) q0) p5 s3 s4 s2 s1
               s0 v), (Right_big_sizes
             (let rec add0 n1 m =
                match n1 with
                | O -> m
                | S p6 -> S (add0 p6 m)
              in add0 q0 (vector_length (S (S O)) v)))))
      | Coq_inr p0 ->
        Green (lvl, (S (S O)),
          (add (S (S (S (S (S (S (S (S O))))))))
            (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S O))))))))
              PeanoNat.Nat.pred (add (S (S (S (S (S O))))) q))), Right,
          SomeGreen, NoRed, p, n, p0, (Right_big_sizes
          (PeanoNat.Nat.iter (S (S (S (S (S (S (S (S O))))))))
            PeanoNat.Nat.pred (add (S (S (S (S (S O))))) q)))))
   | _ -> assert false (* absurd case *))
| _ -> assert false (* absurd case *)

(** val ensure_green :
    nat -> kind -> green_hue -> red_hue -> 'a1 triple -> 'a1 triple **)

let ensure_green lvl k g r t =
  match g with
  | SomeGreen ->
    (match r with
     | SomeRed -> assert false (* absurd case *)
     | NoRed -> t)
  | NoGreen ->
    (match k with
     | Only ->
       (match r with
        | SomeRed -> green_of_red_only lvl t
        | NoRed -> assert false (* absurd case *))
     | Left ->
       (match r with
        | SomeRed -> green_of_red_left lvl t
        | NoRed -> assert false (* absurd case *))
     | Right ->
       (match r with
        | SomeRed -> green_of_red_right lvl t
        | NoRed -> assert false (* absurd case *)))

(** val ensure_green_path : nat -> kind -> color -> 'a1 path -> 'a1 path **)

let ensure_green_path _ _ _ = function
| Children (lvl, len, _, is_hole, k1, k2, g, y, o, r, t, t0) ->
  Children (lvl, len, (add len lvl), is_hole, k1, k2, SomeGreen, y, o, NoRed,
    t, (ensure_green (add len lvl) k2 g r t0))

(** val ensure_green_cdeque :
    nat -> color -> 'a1 non_empty_cdeque -> 'a1 non_empty_cdeque **)

let ensure_green_cdeque _ _ = function
| Only_path (lvl, g, r, p) ->
  Only_path (lvl, SomeGreen, NoRed,
    (ensure_green_path lvl Only (Mix (g, NoYellow, NoOrange, r)) p))
| Pair_green (lvl, p, p0) -> Pair_green (lvl, p, p0)
| Pair_red (lvl, cl, cr, p, p0) ->
  Pair_green (lvl, (ensure_green_path lvl Left cl p),
    (ensure_green_path lvl Right cr p0))

(** val regular_of_semi : 'a1 sdeque -> 'a1 deque **)

let regular_of_semi = function
| Sd (_, c) ->
  (match c with
   | Empty _ -> Empty O
   | NonEmpty (_, g, r, n) ->
     NonEmpty (O, SomeGreen, NoRed,
       (ensure_green_cdeque O (Mix (g, NoYellow, NoOrange, r)) n)))
