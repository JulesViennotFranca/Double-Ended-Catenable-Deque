module Deq = Deq.Core

type 'a pr = out_channel -> 'a -> unit

type nh = NOT_HOLE
type hole = Hole
type has_hole = HAS_HOLE

(* Types for the different kinds of triples. *)

type only   = ONLY
type left   = LEFT
type right  = RIGHT
type stored = STORED

(* Types for preferred child. *)

type preferred_left  = PREFERRED_LEFT
type preferred_right = PREFERRED_RIGHT

(* Types for zero and the successor of a type. *)

type    z = ZERO
type 'a s = SUCC

(* Types representing 1 to 8 successors. *)

type 'a ge1 = 'a s
type 'a ge2 = 'a s s
type 'a ge3 = 'a s s s
type 'a ge4 = 'a s s s s
type 'a ge5 = 'a s s s s s
type 'a ge6 = 'a s s s s s s
type 'a ge7 = 'a s s s s s s s
type 'a ge8 = 'a s s s s s s s s

(* Types representing 1, 2 and 6. *)

type eq1  = z s
type eq2  = z ge2
type eq6  = z ge6

(* Types representing tuple of size 4, 5, 6 and 8. *)

type 'a four  = 'a * 'a * 'a * 'a
type 'a five  = 'a * 'a * 'a * 'a * 'a
type 'a six   = 'a * 'a * 'a * 'a * 'a * 'a
type 'a eight = 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a

(* A type for vector of size 0 to 6. *)

type ('a, 'upperbound) vector =
  | V0 : ('a, 'n) vector
  | V1 : 'a -> ('a, 'n ge1) vector
  | V2 : 'a * 'a -> ('a, 'n ge2) vector
  | V3 : 'a * 'a * 'a -> ('a, 'n ge3) vector
  | V4 : 'a * 'a * 'a * 'a -> ('a, 'n ge4) vector
  | V5 : 'a * 'a * 'a * 'a * 'a -> ('a, 'n ge5) vector
  | V6 : 'a * 'a * 'a * 'a * 'a * 'a -> ('a, 'n ge6) vector

(* Fold right on vectors. *)

let vector_fold_right
: type z a n. (a -> z -> z) -> (a, n) vector -> z -> z
= fun fn v z -> match v with
  | V0 -> z
  | V1 a -> fn a z
  | V2 (a, b) -> fn a (fn b z)
  | V3 (a, b, c) -> fn a (fn b (fn c z))
  | V4 (a, b, c, d) -> fn a (fn b (fn c (fn d z)))
  | V5 (a, b, c, d, e) -> fn a (fn b (fn c (fn d (fn e z))))
  | V6 (a, b, c, d, e, f) -> fn a (fn b (fn c (fn d (fn e (fn f z)))))

(* Fold left on vectors. *)

let vector_fold_left
: type z a n. (z -> a -> z) -> z -> (a, n) vector -> z
= fun fn z v -> match v with
  | V0 -> z
  | V1 a -> fn z a
  | V2 (a, b) -> fn (fn z a) b
  | V3 (a, b, c) -> fn (fn (fn z a) b) c
  | V4 (a, b, c, d) -> fn (fn (fn (fn z a) b) c) d
  | V5 (a, b, c, d, e) -> fn (fn (fn (fn (fn z a) b) c) d) e
  | V6 (a, b, c, d, e, f) -> fn (fn (fn (fn (fn (fn z a) b) c) d) e) f

module Buffer : sig
  (* The type for buffer is parametrized by the type of elements it contains and
     a type representing the number of elements it contains. *)
  type ('a, 'n) t

  (* Different operations needed on buffers, and how they change the size of the
     buffer. *)
     
  val empty : ('a, z) t
  val push : 'a -> ('a, 'n) t -> ('a, 'n s) t
  val inject : ('a, 'n) t -> 'a -> ('a, 'n s) t

  val pop : ('a, 'n s) t -> 'a * ('a, 'n) t
  val eject : ('a, 'n s) t -> ('a, 'n) t * 'a

  val pop2 : ('a, 'n s s) t -> 'a * 'a * ('a, 'n) t
  val eject2 : ('a, 'n s s) t -> ('a, 'n) t * 'a * 'a

  val single : 'a -> ('a, z s) t
  val pair   : 'a -> 'a -> ('a, z s s) t
  val triple : 'a -> 'a -> 'a -> ('a, z s s s) t

  val two : ('a, eq2) t -> 'a * 'a
  val push2 : 'a * 'a -> ('a, 'n) t -> ('a, 'n s s) t
  val inject2 : ('a, 'n) t -> 'a * 'a -> ('a, 'n s s) t

  val push_5_vector : 'a five * ('a, _) vector -> ('a, 'n) t -> ('a, 'n ge5) t
  val inject_5_vector : ('a, 'n) t -> 'a five * ('a, _) vector -> ('a, 'n ge5) t

  val push6 : 'a six -> ('a, 'n) t -> ('a, 'n ge6) t
  val inject6 : ('a, 'n) t -> 'a six -> ('a, 'n ge6) t

  val inject8 : ('a, 'n) t -> 'a eight -> ('a, 'n ge8) t

  val push_vector : ('a, _) vector -> ('a, 'n) t -> ('a, 'n) t
  val inject_vector : ('a, 'n) t -> ('a, _) vector -> ('a, 'n) t

  (* A type storing either 0 element or a buffer with at least 1 element. *)

  type _ has1 =
    | Exact_0 : 'a has1
    | Lte1 : ('a, _ ge1) t -> 'a has1
  val has1 : ('a, 'n) t -> 'a has1

  (* Translation between buffers and non-catenable non_empty_cdeque. *)

  val to_dequeue : ('a, _) t -> 'a Deq.t
  val of_dequeue : 'a Deq.t -> 'a has1

  (* A type storing either 4 elements or a buffer with at least 5 elements. *)

  type 'a has5 =
    | Exact_4 : 'a four -> 'a has5
    | At_least_5 : ('a, _ ge5) t -> 'a has5
  val has5   : ('a, _ ge4) t -> 'a has5

  (* A type storing either 1 to 6 elements or a buffer with at least 5 
     elements and 2 additionnal elements. *)

  type 'a has5p2 =
    | Less_than_5p2 : ('a, eq6) vector -> 'a has5p2
    | At_least_5p2 : ('a, _ ge5) t * 'a * 'a -> 'a has5p2
  val has5p2 : ('a, _ ge1) t -> 'a has5p2

  (* A type storing either 1 to 6 elements or 2 elements along a buffer with 
     at least 5 elements. *)

  type 'a has2p5 =
    | Less_than_2p5 : ('a, eq6) vector -> 'a has2p5
    | At_least_2p5 : 'a * 'a * ('a, _ ge5) t -> 'a has2p5
  val has2p5 : ('a, _ ge1) t -> 'a has2p5

  (* A type storing either 5 to 7 elements or a buffer with at least 8 
     elements. *)

  type 'a has8 =
    | Less_than_8 : ('a five * ('a, eq2) vector) -> 'a has8
    | At_least_8 : ('a, _ ge8) t -> 'a has8
  val has8   : ('a, _ ge5) t -> 'a has8

  (* A type storing either 8 to 10 elements or 3 elements along a buffer with 
     at least 8 elements. *)

  type 'a has3p8 =
    | Less_than_11 : 'a eight * ('a, eq2) vector -> 'a has3p8
    | At_least_11 : 'a * 'a * 'a * ('a, _ ge8) t -> 'a has3p8
  val has3p8 : ('a, _ ge8) t -> 'a has3p8

end = struct
  (* Buffers are simply the non-catenable deques previously defined. *)
  type ('a, 'quantity) t = 'a Deq.t

  let empty = Deq.empty
  let push x t = Deq.push x t
  let inject t x = Deq.inject t x

  let pop t = match Deq.pop t with
    | None -> assert false
    | Some (x, t') -> (x, t')
  let eject t = match Deq.eject t with
    | None -> assert false
    | Some (t', x) -> (t', x)

  let single x = push x empty
  let pair x y = push x (single y)
  let triple x y z = push x (pair y z)

  let pop2 t =
    let x, t = pop t in
    let y, t = pop t in
    x, y, t

  let eject2 t =
    let t, x = eject t in
    let t, y = eject t in
    t, y, x

  let two t =
    let x, y, t = pop2 t in
    assert (Deq.is_empty t) ;
    (x, y)

  type _ has1 =
    | Exact_0 : 'a has1
    | Lte1 : ('a, _ ge1) t -> 'a has1

  let has1 t =
    if Deq.is_empty t
    then Exact_0
    else Lte1 t

  let to_dequeue t = t
  let of_dequeue d =
    if Deq.is_empty d
    then Exact_0
    else Lte1 d

  let inject2 t (a, b) = inject (inject t a) b
  let push2 (a, b) t = push a (push b t)

  let push6 (a, b, c, d, e, f) t =
    push a (push b (push c (push d (push e (push f t)))))
  let inject6 t (a, b, c, d, e, f) =
    inject (inject (inject (inject (inject (inject t a) b) c) d) e) f

  type (_, _) pop =
    | Not_enough : ('a, 'n) vector -> ('a, 'n s) pop
    | Enough : ('a, 'n) vector * 'a Deq.t -> ('a, 'n) pop

  let pop3 t =
    match Deq.pop t with
    | None -> Not_enough V0
    | Some (x, t) ->
    match Deq.pop t with
    | None -> Not_enough (V1 x)
    | Some (y, t) ->
    match Deq.pop t with
    | None -> Not_enough (V2 (x, y))
    | Some (z, t) -> Enough (V3 (x, y, z), t)

  type 'a has8 =
    | Less_than_8 : ('a five * ('a, eq2) vector) -> 'a has8
    | At_least_8 : ('a, _ ge8) t -> 'a has8

  let pop5 t =
    let a, b, t = pop2 t in
    let c, d, t = pop2 t in
    let e, t = pop t in
    (a, b, c, d, e), t

  let has8 buffer =
    let five, t = pop5 buffer in
    match pop3 t with
    | Not_enough vec -> Less_than_8 (five, vec)
    | Enough _ -> At_least_8 buffer

  type 'a has5 =
    | Exact_4 : 'a four -> 'a has5
    | At_least_5 : ('a, _ ge5) t -> 'a has5

  let has5 buffer =
    let a, b, t = pop2 buffer in
    let c, d, t = pop2 t in
    match has1 t with
    | Exact_0 -> Exact_4 (a, b, c, d)
    | Lte1 _ -> At_least_5 buffer

  let push_vector v t = vector_fold_right Deq.push v t
  let inject_vector t v = vector_fold_left  Deq.inject t v

  type 'a has5p2 =
    | Less_than_5p2 : ('a, eq6) vector -> 'a has5p2
    | At_least_5p2 : ('a, _ ge5) t * 'a * 'a -> 'a has5p2

  let has5p2 t =
      let t, a = eject t in
      match Deq.eject t with
      | None -> Less_than_5p2 (V1 a)
      | Some ((t as t5), b) ->
      match Deq.eject t with
      | None -> Less_than_5p2 (V2 (b, a))
      | Some (t, c) ->
      match Deq.eject t with
      | None -> Less_than_5p2 (V3 (c, b, a))
      | Some (t, d) ->
      match Deq.eject t with
      | None -> Less_than_5p2 (V4 (d, c, b, a))
      | Some (t, e) ->
      match Deq.eject t with
      | None -> Less_than_5p2 (V5 (e, d, c, b, a))
      | Some (t, f) ->
      match Deq.eject t with
      | None -> Less_than_5p2 (V6 (f, e, d, c, b, a))
      | Some _ -> At_least_5p2 (t5, b, a)

  type 'a has2p5 =
    | Less_than_2p5 : ('a, eq6) vector -> 'a has2p5
    | At_least_2p5 : 'a * 'a * ('a, _ ge5) t -> 'a has2p5

  let has2p5 t =
      let a, t = pop t in
      match Deq.pop t with
      | None -> Less_than_2p5 (V1 a)
      | Some (b, (t as t5)) ->
      match Deq.pop t with
      | None -> Less_than_2p5 (V2 (a, b))
      | Some (c, t) ->
      match Deq.pop t with
      | None -> Less_than_2p5 (V3 (a, b, c))
      | Some (d, t) ->
      match Deq.pop t with
      | None -> Less_than_2p5 (V4 (a, b, c, d))
      | Some (e, t) ->
      match Deq.pop t with
      | None -> Less_than_2p5 (V5 (a, b, c, d, e))
      | Some (f, t) ->
      match Deq.pop t with
      | None -> Less_than_2p5 (V6 (a, b, c, d, e, f))
      | Some _ -> At_least_2p5 (a, b, t5)

  type 'a has3p8 =
    | Less_than_11 : 'a eight * ('a, eq2) vector -> 'a has3p8
    | At_least_11 : 'a * 'a * 'a * ('a, _ ge8) t -> 'a has3p8

  let has3p8 t =
    let a, b, t = pop2 t in
    let c, (t as t8) = pop t in
    let d, e, t = pop2 t in
    let f, g, t = pop2 t in
    let h, t = pop t in
    match pop3 t with
    | Not_enough vec -> Less_than_11 ((a, b, c, d, e, f, g, h), vec)
    | Enough _ -> At_least_11 (a, b, c, t8)

  let push5 (a, b, c, d, e) t =
    push a (push b (push c (push d (push e t))))

  let inject5 t (a, b, c, d, e) =
    inject (inject (inject (inject (inject t a) b) c) d) e

  let push_5_vector (five, v) t = push5 five (push_vector v t)
  let inject_5_vector t (five, v) = inject_vector (inject5 t five) v

  let inject8 t (a, b, c, d, e, f, g, h) =
    inject (inject (inject (inject (inject (inject (inject (inject t a) b) c) d) e) f) g) h
end

(* Types for prefix and suffix that are simply buffers. *)

type ('a, 'n) prefix = ('a, 'n) Buffer.t
type ('a, 'n) suffix = ('a, 'n) Buffer.t

type is_hole = IS_HOLE

and 'a stored_triple =
  (* A stored triple is either only a buffer (the child non_empty_cdeque and the other buffer are empty) ... *)
  | ST_small : ('a, _ ge3) prefix -> 'a stored_triple
  (* ... or a triple with non-empty prefix and suffix. *)
  | ST_triple : ('a, _ ge3) prefix
             (* Triples contained in a stored triple are also stored triples. *)
           * ('a stored_triple, _) cdeque
           * ('a, _ ge3) suffix
          -> 'a stored_triple

(** An only triple is a triple of kind [only] that is not a hole. *)
and ('a, 'b, 'color, 'hole_loc, 'has_hole) only_triple =
  ('a, 'b, 'color, only, 'hole_loc, nh, 'has_hole) triple

(** A left triple is a triple of kind [left] that is not a hole. *)
and ('a, 'b, 'color, 'hole_loc, 'has_hole) left_triple =
  ('a, 'b, 'color, left, 'hole_loc, nh, 'has_hole) triple

(** A right triple is a triple of kind [right] that is not a hole. *)
and ('a, 'b, 'color, 'hole_loc, 'has_hole) right_triple =
  ('a, 'b, 'color, right, 'hole_loc, nh, 'has_hole) triple

(** A triple is parametrized with the types of elements it contains, the types 
    of elements at his hole (= end of the path), its color, its kind, the 
    location of its hole, if it is itself a hole and if it has a hole. *)
and ('a, 'b, 'color, 'kind, 'hole_loc, 'is_hole, 'has_hole) triple =

  (* The hole constructor, is yellow or orange, works for every kind, is and 
     has a hole. *)
  | Hole : ('a, 'a, [< `yellow | `orange], 'k, 'k, is_hole, has_hole) triple

  (* If there is only one non-empty buffer. *)
  | Only_small : ('a, _ ge1) prefix
               -> ('a, 'a, [`green], only, nh, nh, nh) triple

  (* If it is a green only triple, followed by a stored_triple non_empty_cdeque. *)
  | Only_green :
           ('a, _ ge8) prefix
         * ('a stored_triple, [< `green | `red]) non_empty_cdeque
         * ('a, _ ge8) suffix
        -> ('a, 'a, [`green], only, nh, nh, nh) triple

  (* If it is a yellow only triple, followed by a non-empty non_empty_cdeque that has a 
     hole. The preferred child is the left one. *)
  | Only_yellow :
           ('a, _ ge7) prefix
         * ('a stored_triple, 'b, preferred_left, 'hole) packet
         * ('a, _ ge7) suffix
        -> ('a, 'b, [`yellow], only, 'hole, nh, has_hole) triple

  (* If it is an orange only triple, followed by a non-empty non_empty_cdeque that has a 
     hole. The preferred child is the right one. *)
  | Only_orange :
           ('a, _ ge6) prefix
         * ('a stored_triple, 'b, preferred_right, 'hole) packet
         * ('a, _ ge6) suffix
        -> ('a, 'b, [`orange], only, 'hole, nh, has_hole) triple

  (* If it is a red only triple, followed by a stored_triple green non_empty_cdeque. *)
  | Only_red :
           ('a, _ ge5) prefix
         * ('a stored_triple, [`green]) non_empty_cdeque
         * ('a, _ ge5) suffix
        -> ('a, 'a, [`red], only, nh, nh, nh) triple

  (* Similar description for left triples and right triples cases. *)

  | Left_small :
           ('a, _ ge5) prefix
         * ('a, eq2) suffix
        -> ('a, 'b, [`green], left, nh, nh, nh) triple
  | Left_green :
           ('a, _ ge8) prefix
         * ('a stored_triple, [< `green | `red]) non_empty_cdeque
         * ('a, eq2) suffix
        -> ('a, 'b, [`green], left, nh, nh, nh) triple
  | Left_yellow :
           ('a, _ ge7) prefix
         * ('a stored_triple, 'b, preferred_left, 'hole) packet
         * ('a, eq2) suffix
        -> ('a, 'b, [`yellow], left, 'hole, nh, has_hole) triple
  | Left_orange :
           ('a, _ ge6) prefix
         * ('a stored_triple, 'b, preferred_right, 'hole) packet
         * ('a, eq2) suffix
        -> ('a, 'b, [`orange], left, 'hole, nh, has_hole) triple
  | Left_red :
           ('a, _ ge5) prefix
         * ('a stored_triple, [`green]) non_empty_cdeque
         * ('a, eq2) suffix
        -> ('a, 'a, [`red], left, nh, nh, nh) triple

  | Right_small :
           ('a, eq2) prefix
         * ('a, _ ge5) suffix
        -> ('a, 'b, [`green], right, nh, nh, nh) triple
  | Right_green :
           ('a, eq2) prefix
         * ('a stored_triple, [< `green | `red]) non_empty_cdeque
         * ('a, _ ge8) suffix
        -> ('a, 'a, [`green], right, nh, nh, nh) triple
  | Right_yellow :
           ('a, eq2) prefix
         * ('a stored_triple, 'b, preferred_left, 'hole) packet
         * ('a, _ ge7) suffix
        -> ('a, 'b, [`yellow], right, 'hole, nh, has_hole) triple
  | Right_orange :
           ('a, eq2) prefix
         * ('a stored_triple, 'b, preferred_right, 'hole) packet
         * ('a, _ ge6) suffix
        -> ('a, 'b, [`orange], right, 'hole, nh, has_hole) triple
  | Right_red :
           ('a, eq2) prefix
         * ('a stored_triple, [`green]) non_empty_cdeque
         * ('a, _ ge5) suffix
        -> ('a, 'a, [`red], right, nh, nh, nh) triple

(** packet are triple with at least a yellow or orange child. *)
and ('a, 'b, 'preference, 'hole_loc) packet =
  | Only_child :
       ('a, 'b, [< `yellow | `orange], only, 'hole_loc, _, has_hole) triple
    -> ('a, 'b, _, 'hole_loc) packet

  | Left_child  :
       ('a, 'b, [< `yellow | `orange], left, 'hole_loc, _, has_hole) triple
     * ('a, _, right) path
    -> ('a, 'b, preferred_left, 'hole_loc) packet

  | Right_child :
       ('a, [`green], left) path
     * ('a, 'b, [< `yellow | `orange], right, 'hole_loc, _, has_hole) triple
    -> ('a, 'b, preferred_right, 'hole_loc) packet

(** A path stores the natural child and the adoptive child. *)
and ('a, 'color, 'kind) path =
  | Children :
       ('a, 'b, [< `yellow | `orange], 'kind, 'hole_loc, _, has_hole) triple
     * ('b, 'b, [< `green | `red] as 'color, 'hole_loc, nh, nh, nh) triple
    -> ('a, 'color, 'kind) path

(** A non-empty non_empty_cdeque is represented as the compressed forest form. *)
and ('a, 'parent_color) non_empty_cdeque =
  | Only_path : ('a, [< `green | `red] as 'c, only) path -> ('a, 'c) non_empty_cdeque
  | Pair_green :
        ('a, _, left) path
      * ('a, _, right) path
     -> ('a, [`red]) non_empty_cdeque
  | Pair_red :
        ('a, [`green], left) path
      * ('a, [`green], right) path
     -> ('a, [`green]) non_empty_cdeque

(* Types for green and red deques. *)

and 'a green_deque = ('a, [`green]) non_empty_cdeque
and 'a red_deque = ('a, [`red]) non_empty_cdeque

(** A type for deques, either empty or made of a non-empty non_empty_cdeque. *)
and ('a, 'c) cdeque =
  | Empty : ('a, [`green]) cdeque
  | NonEmpty : ('a, [< `green | `red] as 'c) non_empty_cdeque -> ('a, 'c) cdeque

(** A type for semiregular deques. *)
type 'a sdeque = Sd : ('a, _) cdeque -> 'a sdeque

(** A type for regulare deques. *)
type 'a deque = T : ('a, [`green]) cdeque -> 'a deque

(** The empty deque. *)
let empty = T Empty

(** A test to see if a deque is empty or not. *)
let is_empty = function
  | T Empty -> true
  | _ -> false

(** Pushing on an only triple. *)
let push_only_triple
: type a b c h hh.
  a -> (a, b, c, h, hh) only_triple -> (a, b, c, h, hh) only_triple
= fun x triple ->
  match triple with
  | Only_small buf       -> Only_small (Buffer.push x buf)
  | Only_green  (p, c, s) -> Only_green  (Buffer.push x p, c, s)
  | Only_yellow (p, c, s) -> Only_yellow (Buffer.push x p, c, s)
  | Only_orange (p, c, s) -> Only_orange (Buffer.push x p, c, s)
  | Only_red    (p, c, s) -> Only_red    (Buffer.push x p, c, s)

(** Injecting on an only triple. *)
let inject_only_triple
: type a b c h hh.
  (a, b, c, h, hh) only_triple -> a -> (a, b, c, h, hh) only_triple
= fun triple x ->
  match triple with
  | Only_small buf       -> Only_small (Buffer.inject buf x)
  | Only_green  (p, c, s) -> Only_green  (p, c, Buffer.inject s x)
  | Only_yellow (p, c, s) -> Only_yellow (p, c, Buffer.inject s x)
  | Only_orange (p, c, s) -> Only_orange (p, c, Buffer.inject s x)
  | Only_red    (p, c, s) -> Only_red    (p, c, Buffer.inject s x)

(** Destructing on this type tells wheither its parameter [is_hole] or not. *)
type _ hole_test =
  | Is_hole  : is_hole hole_test
  | Not_hole : nh hole_test

(** Takes a triple and returns a hole_test parametrized with the triple hole 
    information. *)
let is_hole
: type a b c k hl h. (a, b, c, k, hl, h, has_hole) triple -> h hole_test
= function
  | Hole -> Is_hole
  | Only_yellow _ -> Not_hole
  | Only_orange _ -> Not_hole
  | Left_yellow _ -> Not_hole
  | Left_orange _ -> Not_hole
  | Right_yellow _ -> Not_hole
  | Right_orange _ -> Not_hole

(** Pushing on an only path. *)
let push_only_path
: type a c. a -> (a, c, only) path -> (a, c, only) path
= fun x (Children (only, kont)) ->
  match is_hole only, only with
  | Is_hole, Hole -> Children (only, push_only_triple x kont)
  | Not_hole, _   -> Children (push_only_triple x only, kont)

(** Injecting on an only path. *)
let inject_only_path
: type a c. (a, c, only) path -> a -> (a, c, only) path
= fun (Children (only, kont)) x ->
  match is_hole only, only with
  | Is_hole, Hole -> Children (Hole, inject_only_triple kont x)
  | Not_hole, _   -> Children (inject_only_triple only x, kont)

(** Pushing on a left triple. *)
let push_left_triple
: type a b c hl hh.
     a
  -> (a, b, c, left, hl, nh, hh) triple
  -> (a, b, c, left, hl, nh, hh) triple
= fun x triple ->
  match triple with
  | Left_small  (p,    s) -> Left_small  (Buffer.push x p, s)
  | Left_green  (p, c, s) -> Left_green  (Buffer.push x p, c, s)
  | Left_yellow (p, c, s) -> Left_yellow (Buffer.push x p, c, s)
  | Left_orange (p, c, s) -> Left_orange (Buffer.push x p, c, s)
  | Left_red    (p, c, s) -> Left_red    (Buffer.push x p, c, s)

(** Injecting on a right triple. *)
let inject_right_triple
: type a b c hl hh.
     (a, b, c, right, hl, nh, hh) triple
  -> a
  -> (a, b, c, right, hl, nh, hh) triple
= fun triple x ->
  match triple with
  | Right_small  (p,    s) -> Right_small  (p,    Buffer.inject s x)
  | Right_green  (p, c, s) -> Right_green  (p, c, Buffer.inject s x)
  | Right_yellow (p, c, s) -> Right_yellow (p, c, Buffer.inject s x)
  | Right_orange (p, c, s) -> Right_orange (p, c, Buffer.inject s x)
  | Right_red    (p, c, s) -> Right_red    (p, c, Buffer.inject s x)

(** Pushing on a left path. *)
let push_left_path
: type a c. a -> (a, c, left) path -> (a, c, left) path
= fun x (Children (left, kont)) ->
  match is_hole left, left with
  | Is_hole, Hole -> Children (left, push_left_triple x kont)
  | Not_hole, _   -> Children (push_left_triple x left, kont)

(** Injecting on a right path. *)
let inject_right_path
: type a c. (a, c, right) path -> a -> (a, c, right) path
= fun (Children (right, kont)) x ->
  match is_hole right, right with
  | Is_hole, Hole -> Children (right, inject_right_triple kont x)
  | Not_hole, _   -> Children (inject_right_triple right x, kont)

(** Pushing on a non empty colored deque. *)
let push_deque
: type a c. a -> (a, c) non_empty_cdeque -> (a, c) non_empty_cdeque
= fun x deq ->
  match deq with
  | Only_path p -> Only_path (push_only_path x p)
  | Pair_green (prefix, suffix) -> Pair_green (push_left_path x prefix, suffix)
  | Pair_red   (prefix, suffix) -> Pair_red   (push_left_path x prefix, suffix)


(** Injecting on a non empty colored deque. *)
let inject_deque
: type a c. (a, c) non_empty_cdeque -> a -> (a, c) non_empty_cdeque
= fun deq x ->
  match deq with
  | Only_path p -> Only_path (inject_only_path p x)
  | Pair_green (prefix, suffix) ->
      Pair_green (prefix, inject_right_path suffix x)
  | Pair_red (prefix, suffix) ->
      Pair_red (prefix, inject_right_path suffix x)
    
(** Creates an only triple containing only one element. *)
let single_triple x = Only_small (Buffer.single x)

(** Creates a non empty colored deque containing only one element. *)
let only_single x = Only_path (Children (Hole, single_triple x))

(** Creates a colored deque containing only one element. *)
let single x = NonEmpty (only_single x)

(** Pushing on a colored deque. *)
let push_t
: type a c. a -> (a, c) cdeque -> (a, c) cdeque
= fun x t ->
  match t with
  | Empty  -> single x
  | NonEmpty deq -> NonEmpty (push_deque x deq)

(** Injecting on a colored deque. *)
let inject_t
: type a c. (a, c) cdeque -> a -> (a, c) cdeque
= fun t x ->
  match t with
  | Empty  -> single x
  | NonEmpty deq -> NonEmpty (inject_deque deq x)

(** Pushing on a deque. *)
let push x (T t) = T (push_t x t)

(** Injecting on a deque. *)
let inject (T t) x = T (inject_t t x)

(** Pushing on a semi-regular deque. *)
let push_semi x (Sd t) = Sd (push_t x t)

(** Injecting on a semi-regular deque. *)
let inject_semi (Sd t) x = Sd (inject_t t x)

(** Pushing a whole vector into a deque. *)
let push_vector v t = vector_fold_right (fun x t -> push x t) v t

(** Injecting a whole vector into a deque. *)
let inject_vector t v = vector_fold_left (fun t x -> inject t x) t v

(** Pushing a whole vector into a semi-regular deque. *)
let push_semi_vector v t = vector_fold_right (fun x t -> push_semi x t) v t

(** Injecting a whole vector into a semi-regular deque. *)
let inject_semi_vector t v = vector_fold_left (fun t x -> inject_semi t x) t v

(** Destructing on this type tells weither its parameter is [green] or [red]. *)
type _ green_or_red =
  | Is_green : [`green] green_or_red
  | Is_red   : [`red  ] green_or_red

(** Takes a green or red triple and returns a [green_or_red] parametrized with 
    its color. *)
let color
: type a c hl. (a, a, c, hl, nh, nh, nh) triple -> c green_or_red
= function
  | Only_red    _ -> Is_red
  | Left_red    _ -> Is_red
  | Right_red   _ -> Is_red
  | Only_green  _ -> Is_green
  | Only_small _ -> Is_green
  | Left_small  _ -> Is_green
  | Left_green  _ -> Is_green
  | Right_small _ -> Is_green
  | Right_green _ -> Is_green

(** Takes a path and returns a [green_or_red] parametrized with the color of 
    its ouput triple. *)
let path_uncolored
: type a c k. (a, c, k) path -> c green_or_red
= fun (Children (_, t)) -> color t

(** Takes a non empty colored deque and returns a [green_or_red] parametrized 
    with its color. *)
let color_deque
: type a c. (a, c) non_empty_cdeque -> c green_or_red
= function
  | Only_path t -> path_uncolored t
  | Pair_red _ -> Is_green
  | Pair_green _ -> Is_red

(** Takes a colored deque and returns a [green_or_red] parametrized with its 
    color. *)
let color_st
: type a c. (a, c) cdeque -> c green_or_red
= function
  | Empty -> Is_green
  | (NonEmpty t) -> color_deque t

(** Stores a packet and a green or red triple of the output type of the packet. 
    It represents a preferred left packet and the triple that will follow from
    its hole. *)
type 'a pref_left =
  | Pref_left : ('a, 'b, preferred_left, 'hole2) packet
              * ('b, 'b, [< `green | `red], 'hole2, nh, nh, nh) triple
             -> 'a pref_left

(** Stores a packet and a green or red triple of the output type of the packet. 
    It represents a preferred right packet and the triple that will follow from
    its hole. *)
type 'a pref_right =
  | Pref_right : ('a, 'b, preferred_right, 'hole2) packet
               * ('b, 'b, [< `green | `red], 'hole2, nh, nh, nh) triple
              -> 'a pref_right

(** Takes a non empty colored deque and represents it as a [pref_left]. *)
let pref_left
: type a c.  (a, c) non_empty_cdeque -> a pref_left
= function
  (* If the non empty colored deque has only one child, the result is simply 
     the decomposition of the only path. *)
  | Only_path  (Children (d1, k))         -> 
      Pref_left (Only_child d1, k)
  (* If it has two children, the natural child of the left path and the right 
     path can be merged into a packet, the adoptive child of the left path is 
     the triple of the [pref_left]. *)
  | Pair_red   (Children (le, ft), right) ->
      Pref_left (Left_child (le, right), ft)
  | Pair_green (Children (le, ft), right) -> 
      Pref_left (Left_child (le, right), ft)

(** Takes a preferred left packet and the triple following from its hole and 
    represents them as a [pref_right]. *)
let pref_right
: type a b.
     (a, b, preferred_left, 'hole) packet
  -> (b, b, [< `green | `red], 'hole, nh, nh, nh) triple
  -> a pref_right
= fun deq ft ->
  match deq with
  (* If the packet is an only child, it can easily be translated to a preferred
     right packet. *)
  | Only_child le -> Pref_right (Only_child le, ft)
  (* If there is a left child and a right path, a left path can be made with 
     the left child and the argument triple. The right child is the natural 
     child of the right path, and the triple of the [pref_right] is its 
     adoptive child. *)
  | Left_child (le, Children (ri, ght)) ->
      Pref_right (Right_child (Children (le, ft), ri), ght)

(** Takes a preferred right packet and the triple following from its hole and 
    returns a non empty colored deque made from them. *)
let no_pref
: type a b.
     (a, b, preferred_right, 'hole) packet
  -> (b, b, [`green], 'hole, nh, nh, nh) triple
  -> (a, [`green]) non_empty_cdeque
= fun d1 ght ->
  (* The preferred right packet contains a preferred child that will have the 
     hole of the packet as one of its descendant. By considering this preferred
     child as the natural one, and the argument triple as the adoptive child, a
     path can be made. 
     The non empty colored deque can easily be constructed with it. *)
  match d1 with
  | Only_child ri ->
      Only_path (Children (ri, ght))
  | Right_child (left, ri) ->
      Pair_red (left, Children (ri, ght))

(** Takes a packet and a triple following from its hole and creates a semi-
    regular deque out of them. *)
let make_child
: type a b c p hl.
     (a, b, p, hl) packet
  -> (b, b, c, hl, nh, nh, nh) triple
  -> a sdeque
= fun ne_deq trip ->
  match color trip, ne_deq, trip with
  | Is_green, Only_child y, g -> Sd (NonEmpty (Only_path (Children (y, g))))
  | Is_red,   Only_child y, g -> Sd (NonEmpty (Only_path (Children (y, g))))
  | Is_green, Left_child (le, right), ft ->
      Sd (NonEmpty (Pair_green (Children (le, ft), right)))
  | Is_red, Left_child (le, right), ft ->
      Sd (NonEmpty (Pair_green (Children (le, ft), right)))
  | Is_green, Right_child (left, ri), ght ->
      Sd (NonEmpty (Pair_red (left, Children (ri, ght))))
  | Is_red, Right_child (left, ri), ght ->
      Sd (NonEmpty (Pair_green (left, Children (ri, ght))))

(** Takes a packet and the triple following from its hole and pushes an element
    on it. *)
let push_child
: type a b c p hl.
     a
  -> (a, b, p, hl) packet
  -> (b, b, c, hl, nh, nh, nh) triple
  -> (a, b, p, hl) packet
   * (b, b, c, hl, nh, nh, nh) triple
= fun x ne_deq trip ->
  (* If the preferred child is the only or left one, the tricky part is to 
     differentiate weither the preferred child of the packet is a hole, pushing 
     is done on the following triple, or not, pushing is done on the preferred 
     child. *)
  match ne_deq, trip with
  | Only_child only, g ->
      begin match is_hole only, only with
      | Is_hole, Hole -> Only_child Hole, push_only_triple x g
      | Not_hole, only -> Only_child (push_only_triple x only), g
      end
  | Left_child (left, right), g ->
      begin match is_hole left, left with
      | Is_hole,  Hole -> Left_child (Hole, right), push_left_triple x g
      | Not_hole, left -> Left_child (push_left_triple x left, right), g
      end
  (* If the preferred child is the right one, pushing is done on the right path. *)
  | Right_child (left, right), g ->
      Right_child (push_left_path x left, right), g

(** Takes a packet and the triple following from its hole and injects an element
    on it. *)
let inject_child
: type a b c p hl.
     (a, b, p, hl) packet
  -> (b, b, c, hl, nh, nh, nh) triple
  -> a
  -> (a, b, p, hl) packet
   * (b, b, c, hl, nh, nh, nh) triple
= fun ne_deq trip x ->
  (* As in the previous function, if the preferred child of the packet is the 
     only or right one, injecting is done on it if it is not a hole, on the 
     following triple otherwise. *)
  match ne_deq, trip with
  | Only_child only, g ->
      begin match is_hole only, only with
      | Is_hole,  Hole -> Only_child only, inject_only_triple g x
      | Not_hole, only -> Only_child (inject_only_triple only x), g
      end
  | Right_child (left, right), g ->
      begin match is_hole right, right with
      | Is_hole,  Hole  -> Right_child (left, right), inject_right_triple g x
      | Not_hole, right -> Right_child (left, inject_right_triple right x), g
      end
  (* If the preferred child is the left one, injecting is done on the left path. *)
  | Left_child (left, right), g ->
      Left_child (left, inject_right_path right x), g

(** [buffer_12] stores 1 or 2 elements. *)
type 'a buffer_12 = 'a * ('a, eq1) vector

(** Takes a prefix of at least 5 elements, a colored deque containing stored 
    triples, a suffix of 2 elements and a buffer_12, and returns a prefix of 2
    elements and a stored triple. *)
let stored_left
: type a c.
     (a, _ ge5) prefix
  -> (a stored_triple, c) cdeque
  -> (a, eq2) suffix
  -> a buffer_12
  -> (a, eq2) prefix * a stored_triple
= fun p2 d2 s2 s1 ->
  (* The buffer_12 is injected in the suffix, making a suffix of at least 3 
     elements. *)
  let s2 =
    let a, v1 = s1 in
    Buffer.inject_vector (Buffer.inject s2 a) v1
  in
  (* Two elements are poped from the prefix, lefting a prefix of at least 3 
     elements. *)
  let x, p2 = Buffer.pop p2 in
  let y, p2 = Buffer.pop p2 in
  (* The two poped elements make up the final prefix. *)
  let s3 = Buffer.pair x y in
  (* The stored triple is made from the transformed prefix and suffix, and the 
     colored deque containing stored triples. *)
  s3, ST_triple (p2, d2, s2)

(** Takes a buffer_12, a prefix of 2 elements, a colored deque containing stored
    triples, and a suffix of at least 5 elements, and returns a stored triple 
    and a suffix of 2 elements. *)
let stored_right
: type a any_c.
     a buffer_12
  -> (a, eq2) prefix
  -> (a stored_triple, any_c) cdeque
  -> (a, _ ge5) suffix
  -> a stored_triple * (a, eq2) suffix
= fun s1 p2 d2 s2 ->
  (* The buffer_12 is pushed in the prefix, making a prefix of at least 3 
     elements. *)
  let p2 =
    let a, v1 = s1 in
    Buffer.push a (Buffer.push_vector v1 p2)
  in
  (* Two elements are ejected from the suffix, lefting a suffix of at least 3
     elements. *)
  let s2, y, x = Buffer.eject2 s2 in
  (* The two ejected elements make up the final suffix. *)
  let s3 = Buffer.pair y x in
  (* The stored triple is made from the transformed prefix and suffix, and the
     colored deque containing stored triples. *)
  ST_triple (p2, d2, s2), s3

(** Takes a left path and a buffer_12 and makes a suffix of two elements and a
    stored triple out of them. *)
let extract_stored_left
: type a c.
     (a, c, left) path
  -> a buffer_12
  -> (a, eq2) suffix * a stored_triple
= fun left s1 ->
  (* Use stored_left to obtain the result. If the first triple of the path is 
     yellow or orange, the child colored deque needed is made from the child 
     packet and the following triple with make_child. *)
  match left with
  | Children (Left_orange (p2, d2, s2), d2_kont) ->
      let Sd d2 = make_child d2 d2_kont in
      stored_left p2 d2 s2 s1
  | Children (Left_yellow (p2, d2, s2), d2_kont) ->
      let Sd d2 = make_child d2 d2_kont in
      stored_left p2 d2 s2 s1
  | Children (Hole, Left_small (p2,     s2)) -> stored_left p2 Empty   s2 s1
  | Children (Hole, Left_green (p2, d2, s2)) -> stored_left p2 (NonEmpty d2) s2 s1
  | Children (Hole, Left_red   (p2, d2, s2)) -> stored_left p2 (NonEmpty d2) s2 s1

(** Takes a buffer_12 and a right path and makes a stored triple and a suffix 
    of 2 elements out of them. *)
let extract_stored_right
: type a c.
     a buffer_12
  -> (a, c, right) path
  -> a stored_triple * (a, eq2) suffix
= fun s1 right ->
  (* The same construction as extract_stored_left applies here. *)
  match right with
  | Children (Right_orange (p2, d2, s2), d2_kont) ->
      let Sd d2 = make_child d2 d2_kont in
      stored_right s1 p2 d2 s2
  | Children (Right_yellow (p2, d2, s2), d2_kont) ->
      let Sd d2 = make_child d2 d2_kont in
      stored_right s1 p2 d2 s2
  | Children (Hole, Right_small (p2,     s2)) -> stored_right s1 p2 Empty   s2
  | Children (Hole, Right_green (p2, d2, s2)) -> stored_right s1 p2 (NonEmpty d2) s2
  | Children (Hole, Right_red   (p2, d2, s2)) -> stored_right s1 p2 (NonEmpty d2) s2

(** Takes a left path of color C and a right path and makes a left path of 
    color C. *)
let left_of_pair
: type a c1 c2.
     (a, c1, left) path
  -> (a, c2, right) path
  -> (a, c1, left) path
= fun left right ->
  (* The idea is to translate the right path into a stored triple, and inject
     this stored triple on the child of the first triple of the left path. *)
  match path_uncolored left, left with
  | _, Children (Left_yellow (p1, d1, s1), kont) ->
      let a, b = Buffer.two s1 in
      let s1 = (a, V1 b) in
      let stored, s3 = extract_stored_right s1 right in
      let d1, kont = inject_child d1 kont stored in
      Children (Left_yellow (p1, d1, s3), kont)
  | _, Children (Left_orange (p1, d1, s1), kont) ->
      let a, b = Buffer.two s1 in
      let s1 = (a, V1 b) in
      let stored, s3 = extract_stored_right s1 right in
      let d1, kont = inject_child d1 kont stored in
      Children (Left_orange (p1, d1, s3), kont)
  | Is_green, Children (Hole, Left_green (p1, d1, s1)) ->
      let a, b = Buffer.two s1 in
      let s1 = (a, V1 b) in
      let stored, s3 = extract_stored_right s1 right in
      let d1 = inject_deque d1 stored in
      Children (Hole, Left_green (p1, d1, s3))
  | Is_red, Children (Hole, Left_red (p1, d1, s1)) ->
      let a, b = Buffer.two s1 in
      let s1 = (a, V1 b) in
      let stored, s3 = extract_stored_right s1 right in
      let d1 = inject_deque d1 stored in
      Children (Hole, Left_red (p1, d1, s3))
  | Is_green, Children (Hole, Left_small (p1, s1)) ->
      let a, b = Buffer.two s1 in
      let p1 = Buffer.inject p1 a in
      let s1 = (b, V0) in
      let stored, s3 = extract_stored_right s1 right in
      Children (Left_orange (p1, Only_child Hole, s3), single_triple stored)

(** Takes a left path and a right path of color C and makes a right path of 
    color C. *)
let right_of_pair
: type a c1 c2.
   (a, c1, left) path -> (a, c2, right) path -> (a, c2, right) path
= fun left right ->
  (* As in left_of_pair, the left path is translated into a stored triple, and
     is pushed on the child of the first child of the right path. *)
  match path_uncolored right, right with
  | _, Children (Right_yellow (p1, d1, s1), kont) ->
      let a, b = Buffer.two p1 in
      let p1 = (a, V1 b) in
      let p3, stored = extract_stored_left left p1 in
      let d1, kont = push_child stored d1 kont in
      Children (Right_yellow (p3, d1, s1), kont)
  | _, Children (Right_orange (p1, d1, s1), kont) ->
      let a, b = Buffer.two p1 in
      let p1 = (a, V1 b) in
      let p3, stored = extract_stored_left left p1 in
      let d1, kont = push_child stored d1 kont in
      Children (Right_orange (p3, d1, s1), kont)
  | Is_green, Children (Hole, Right_green (p1, d1, s1)) ->
      let a, b = Buffer.two p1 in
      let p1 = (a, V1 b) in
      let p3, stored = extract_stored_left left p1 in
      let d1 = push_deque stored d1 in
      Children (Hole, Right_green (p3, d1, s1))
  | Is_red, Children (Hole, Right_red (p1, d1, s1)) ->
      let a, b = Buffer.two p1 in
      let p1 = (a, V1 b) in
      let p3, stored = extract_stored_left left p1 in
      let d1 = push_deque stored d1 in
      Children (Hole, Right_red (p3, d1, s1))
  | Is_green, Children (Hole, Right_small (p1, s1)) ->
      let a, b = Buffer.two p1 in
      let p1 = (a, V0) in
      let s1 = Buffer.push b s1 in
      let p3, stored = extract_stored_left left p1 in
      Children (Right_orange (p3, Only_child Hole, s1), single_triple stored)

(** Stores six or less elements, or paths which color is known or not. *)
type (_, _, _) path_attempt =
  | ZeroSix : ('a, eq6) vector -> ('a, _, _) path_attempt
  | Ok : ('a, 'c, 'k) path -> ('a, 'c, 'k) path_attempt
  | Any : ('a, _, 'k) path -> ('a, [`red], 'k) path_attempt

(** Takes a only path and makes a left path_attempt of the same color. *)
let left_of_only
: type a c. (a, c, only) path -> (a, c, left) path_attempt
= fun path ->
  (* If the child of the first triple of the only path is non empty, the two 
     last elements of its suffix can be ejected to form a new suffix. The 
     remaining elements of the suffix can be seen as a stored triple and 
     injected in its child. The condition to make a left triple are met. *)
  match path_uncolored path, path with
  | _, Children (Only_yellow (p1, d1, s1), kont) ->
      let s1, b, a = Buffer.eject2 s1 in
      let s1' = Buffer.pair b a in
      let d1, kont = inject_child d1 kont (ST_small s1) in
      Ok (Children (Left_yellow (p1, d1, s1'), kont))
  | _, Children (Only_orange (p1, d1, s1), kont) ->
      let s1, b, a = Buffer.eject2 s1 in
      let s1' = Buffer.pair b a in
      let d1, kont = inject_child d1 kont (ST_small s1) in
      Ok (Children (Left_orange (p1, d1, s1'), kont))
  | Is_green, Children (Hole, Only_green (p1, d1, s1)) ->
      let s1, b, a = Buffer.eject2 s1 in
      let s1' = Buffer.pair b a in
      let d1 = inject_deque d1 (ST_small s1) in
      Ok (Children (Hole, Left_green (p1, d1, s1')))
  | Is_red, Children (Hole, Only_red (p1, d1, s1)) ->
      let s1, b, a = Buffer.eject2 s1 in
      let s1' = Buffer.pair b a in
      let d1 = inject_deque d1 (ST_small s1) in
      Ok (Children (Hole, Left_red (p1, d1, s1')))
  (* If the child is empty, the is only a prefix. If the prefix has less than 6
     elements, a path cannot be constructed, hence the use of [path_attempt] as 
     the return type. If the prefix has at least 7 elements, they can be 
     rearranged to meet the left triple conditions. *)
  | Is_green, Children (Hole, Only_small p1) ->
      begin match Buffer.has5p2 p1 with
      | Buffer.Less_than_5p2 vec -> ZeroSix vec
      | Buffer.At_least_5p2 (p1, x, y) ->
          let s1 = Buffer.pair x y in
          Ok (Children (Hole, Left_small (p1, s1)))
      end

(** Takes a only path and makes a rigth path_attempt of the same color. *)
let right_of_only
: type a c.  (a, c, only) path -> (a, c, right) path_attempt
= fun path ->
  (* If the child of the first triple of the only path is non empty, the two 
     first elements of its prefix can be poped to form a new prefix. The 
     remaining elements of the prefix can be seen as a stored triple and 
     pushed in its child. The condition to make a right triple are met. *)
  match path_uncolored path, path with
  | _, Children (Only_yellow (p1, d1, s1), kont) ->
      let a, b, p1 = Buffer.pop2 p1 in
      let d1, kont = push_child (ST_small p1) d1 kont in
      let p1' = Buffer.pair a b in
      Ok (Children (Right_yellow (p1', d1, s1), kont))
  | _, Children (Only_orange (p1, d1, s1), kont) ->
      let a, b, p1 = Buffer.pop2 p1 in
      let d1, kont = push_child (ST_small p1) d1 kont in
      let p1' = Buffer.pair a b in
      Ok (Children (Right_orange (p1', d1, s1), kont))
  | Is_green, Children (Hole, Only_green (p1, d1, s1)) ->
      let a, b, p1 = Buffer.pop2 p1 in
      let d1 = push_deque (ST_small p1) d1 in
      let p1' = Buffer.pair a b in
      Ok (Children (Hole, Right_green (p1', d1, s1)))
  | Is_red, Children (Hole, Only_red (p1, d1, s1)) ->
      let a, b, p1 = Buffer.pop2 p1 in
      let d1 = push_deque (ST_small p1) d1 in
      let p1' = Buffer.pair a b in
      Ok (Children (Hole, Right_red (p1', d1, s1)))
  (* If the child is empty, the is only a prefix. If the prefix has less than 6
     elements, a path cannot be constructed, hence the use of [path_attempt] as 
     the return type. If the prefix has at least 7 elements, they can be 
     rearranged to meet the right triple conditions. *)
  | Is_green, Children (Hole, Only_small p1) ->
      begin match Buffer.has2p5 p1 with
      | Buffer.Less_than_2p5 vec -> ZeroSix vec
      | Buffer.At_least_2p5 (x, y, s1) ->
          let p1 = Buffer.pair x y in
          Ok (Children (Hole, Right_small (p1, s1)))
      end

(** Takes a colored deque and makes a left path attempt of the same color. *)
let make_left
: type a c. (a, c) cdeque -> (a, c, left) path_attempt
= fun cdeque ->
  match color_st cdeque, cdeque with
  | _, Empty -> ZeroSix V0
  | _, NonEmpty (Only_path only) -> left_of_only only
  | Is_green, NonEmpty (Pair_red (a, b)) -> Ok  (left_of_pair a b)
  | Is_red, NonEmpty (Pair_green (a, b)) -> Any (left_of_pair a b)

(** Takes a colored deque and makes a right path attempt of the same color. *)
let make_right
: type a c. (a, c) cdeque -> (a, c, right) path_attempt
= fun cdeque ->
  match color_st cdeque, cdeque with
  | _, Empty -> ZeroSix V0
  | _, NonEmpty (Only_path only) -> right_of_only only
  | Is_green, NonEmpty (Pair_red (a, b)) -> Ok  (right_of_pair a b)
  | Is_red, NonEmpty (Pair_green (a, b)) -> Any (right_of_pair a b)

(** Concatenates two semi-regular deques. *)
let concat_semi
: type a. a sdeque -> a sdeque -> a sdeque
= fun ((Sd dl) as deq_left) ((Sd dr) as deq_right) ->
  (* Try making a left and a right path of the 2 semi-regular deques to be 
     concatenated. 
     If a left and right paths can be made out of them, the return semi-regular
     deque is a pair of those two paths. 
     If one doesn't have enough elements to make a path, those elements can be
     pushed or injected on the other semi-regular deque to make the final one. *)
  match make_left dl with
  | ZeroSix vec -> push_semi_vector vec deq_right
  | Ok left ->
      begin match make_right dr with
      | ZeroSix vec -> inject_semi_vector deq_left vec
      | Ok  right -> Sd (NonEmpty (Pair_green (left, right)))
      | Any right -> Sd (NonEmpty (Pair_green (left, right)))
      end
  | Any left ->
      begin match make_right dr with
      | ZeroSix vec -> inject_semi_vector deq_left vec
      | Ok  right -> Sd (NonEmpty (Pair_green (left, right)))
      | Any right -> Sd (NonEmpty (Pair_green (left, right)))
      end

(** Concatenates two deques. *)
let concat
: type a. a deque -> a deque -> a deque
= fun ((T dl) as deq_left) ((T dr) as deq_right) ->
  (* Same principle as the concatenation of two semi-regular deques but the 
     paths created can only be green, meeting the conditions for the pair of 
     paths to be a deque. *)
  match make_left dl with
  | ZeroSix vec -> push_vector vec deq_right
  | Ok left ->
      begin match make_right dr with
      | ZeroSix vec -> inject_vector deq_left vec
      | Ok right -> T (NonEmpty (Pair_red (left, right)))
      | _ -> .
      end
  | _ -> .

(** Stores 6 elements or a path which color is forgotten. *)
type ('a, 'k) path_uncolored =
  | Exact_6 : 'a six -> ('a, _) path_uncolored
  | Any : ('a, _, 'k) path -> ('a, 'k) path_uncolored

(** Takes a left path and 6 elements and returns a semi-regular deque. *)
let semi_of_left
: type a c.  (a, c, left) path -> a six -> a sdeque
= fun left six ->
  (* Transforms the first triple of the left path into an only triple using the
     6 elements, making an only path, and forming a semi-regular deque made of 
     it. *)
  match path_uncolored left, left with
  | Is_green, Children (Hole, Left_small (p2, s2)) ->
      let c, d = Buffer.two s2 in
      let p2 = Buffer.inject2 p2 (c, d) in
      let p2 = Buffer.inject6 p2 six in
      Sd (NonEmpty (Only_path (Children (Hole, Only_small p2))))
  | Is_green, Children (Hole, Left_green (p2, d2, s2)) ->
      let s2 = Buffer.inject6 s2 six in
      Sd (NonEmpty (Only_path (Children (Hole, Only_green (p2, d2, s2)))))
  | _, Children (Left_yellow (p2, d2, s2), kont) ->
      let s2 = Buffer.inject6 s2 six in
      Sd (NonEmpty (Only_path (Children (Only_yellow (p2, d2, s2), kont))))
  | _, Children (Left_orange (p2, d2, s2), kont) ->
      let s2 = Buffer.inject6 s2 six in
      Sd (NonEmpty (Only_path (Children (Only_orange (p2, d2, s2), kont))))
  | Is_red, Children (Hole, Left_red (p2, d2, s2)) ->
      let s2 = Buffer.inject6 s2 six in
      Sd (NonEmpty (Only_path (Children (Hole, Only_red (p2, d2, s2)))))

(** Takes 6 elements and a right path and returns a semi-regular deque. *)
let semi_of_right
: type a c.  a six -> (a, c, right) path -> a sdeque
= fun six right ->
  (* Transforms the first triple of the right path into an only triple using the
     6 elements, making an only path, and forming a semi-regular deque made of 
     it. *)
     match path_uncolored right, right with
  | Is_green, Children (Hole, Right_small (p2, s2)) ->
      let c, d = Buffer.two p2 in
      let s2 = Buffer.push2 (c, d) s2 in
      let s2 = Buffer.push6 six s2 in
      Sd (NonEmpty (Only_path (Children (Hole, Only_small s2))))
  | Is_green, Children (Hole, Right_green (p2, d2, s2)) ->
      let p2 = Buffer.push6 six p2 in
      Sd (NonEmpty (Only_path (Children (Hole, Only_green (p2, d2, s2)))))
  | _, Children (Right_yellow (p2, d2, s2), kont) ->
      let p2 = Buffer.push6 six p2 in
      Sd (NonEmpty (Only_path (Children (Only_yellow (p2, d2, s2), kont))))
  | _, Children (Right_orange (p2, d2, s2), kont) ->
      let p2 = Buffer.push6 six p2 in
      Sd (NonEmpty (Only_path (Children (Only_orange (p2, d2, s2), kont))))
  | Is_red, Children (Hole, Right_red (p2, d2, s2)) ->
      let p2 = Buffer.push6 six p2 in
      Sd (NonEmpty (Only_path (Children (Hole, Only_red (p2, d2, s2)))))

(** Takes a left green path and pops an element from it, lefting a
    [path_uncolored]. *)
let pop_green_left
: type a. (a, [`green], left) path -> a * (a, left) path_uncolored
= function
  | Children (Hole, Left_small (p1, s1)) ->
      let x, p1 = Buffer.pop p1 in
      let result = match Buffer.has5 p1 with
         | Buffer.At_least_5 p1 ->
             Any (Children (Hole, Left_small (p1, s1)))
         | Buffer.Exact_4 (a, b, c, d) ->
             let e, f = Buffer.two s1 in
             Exact_6 (a, b, c, d, e, f) in
      x, result
  | Children (Hole, Left_green (p1, d1, s1)) ->
      let x, p1 = Buffer.pop p1 in
      let Pref_left (d1, k) = pref_left d1 in
      let path = Children (Left_yellow (p1, d1, s1), k) in
      x, Any path
  | Children (Left_yellow (p1, d1, s1), kont) ->
      let x, p1 = Buffer.pop p1 in
      let Pref_right (d1, kont) = pref_right d1 kont in
      let path = Children (Left_orange (p1, d1, s1), kont) in
      x, Any path
  | Children (Left_orange (p1, d1, s1), kont) ->
      let x, p1 = Buffer.pop p1 in
      let d1 = no_pref d1 kont in
      let path = Children (Hole, Left_red (p1, d1, s1)) in
      x, Any path

(** Takes a right green path and ejects an element from it, lefting a
    [path_uncolored]. *)
let eject_green_right
: type a. (a, [`green], right) path -> (a, right) path_uncolored * a
= function
  | Children (Hole, Right_small (p1, s1)) ->
      let s1, x = Buffer.eject s1 in
      let result = match Buffer.has5 s1 with
        | Buffer.At_least_5 s1 ->
            Any (Children (Hole, Right_small (p1, s1)))
        | Buffer.Exact_4 (c, d, e, f) ->
            let a, b = Buffer.two p1 in
            Exact_6 (a, b, c, d, e, f) in
      result, x
  | Children (Hole, Right_green (p1, d1, s1)) ->
      let s1, x = Buffer.eject s1 in
      let Pref_left (d1, k) = pref_left d1 in
      let path = Children (Right_yellow (p1, d1, s1), k) in
      Any path, x
  | Children (Right_yellow (p1, d1, s1), kont) ->
      let s1, x = Buffer.eject s1 in
      let Pref_right (d1, kont) = pref_right d1 kont in
      let path = Children (Right_orange (p1, d1, s1), kont) in
      Any path, x
  | Children (Right_orange (p1, d1, s1), kont) ->
      let s1, x = Buffer.eject s1 in
      let d1 = no_pref d1 kont in
      let path = Children (Hole, Right_red (p1, d1, s1)) in
      Any path, x

(** Takes a non empty green deque and pops an element from it, lefting a semi-
    regulare deque. *)
let pop_green
: type a. (a, [`green]) non_empty_cdeque -> a * a sdeque
= function
  | Only_path (Children (Hole, Only_small p1)) ->
      let x, p1 = Buffer.pop p1 in
      x, begin match Buffer.has1 p1 with
         | Buffer.Exact_0 -> Sd Empty
         | Buffer.Lte1 p1 -> Sd (NonEmpty (Only_path (Children (Hole, Only_small p1))))
         end
  | Only_path (Children (Hole, Only_green (p1, d1, s1))) ->
      let x, p1 = Buffer.pop p1 in
      let Pref_left (d1, k) = pref_left d1 in
      let only = Children (Only_yellow (p1, d1, s1), k) in
      x, Sd (NonEmpty (Only_path only))
  | Only_path (Children (Only_yellow (p1, d1, s1), kont)) ->
      let x, p1 = Buffer.pop p1 in
      let Pref_right (d1, kont) = pref_right d1 kont in
      let only = (Children (Only_orange (p1, d1, s1), kont)) in
      x, Sd (NonEmpty (Only_path only))
  | Only_path (Children (Only_orange (p1, d1, s1), kont)) ->
      let x, p1 = Buffer.pop p1 in
      let d1 = no_pref d1 kont in
      let only = Children (Hole, Only_red (p1, d1, s1)) in
      x, Sd (NonEmpty (Only_path only))
  | Pair_red (left, right) ->
      let x, result = pop_green_left left in
      x, begin match result with
         | Any left ->
             Sd (NonEmpty (Pair_green (left, right)))
         | Exact_6 six ->
             semi_of_right six right
         end

(** Takes a non empty green deque and ejects an element from it, lefting a semi-
    regular deque. *)
let eject_green
: type a. (a, [`green]) non_empty_cdeque -> a sdeque * a
= function
  | Only_path (Children (Hole, Only_small p1)) ->
      let p1, x = Buffer.eject p1 in
      let result = match Buffer.has1 p1 with
         | Buffer.Exact_0 -> Sd Empty
         | Buffer.Lte1 p1 -> Sd (NonEmpty (Only_path (Children (Hole, Only_small p1))))
      in
      result, x
  | Only_path (Children (Hole, Only_green (p1, d1, s1))) ->
      let s1, x = Buffer.eject s1 in
      let Pref_left (d1, k) = pref_left d1 in
      let only = Children (Only_yellow (p1, d1, s1), k) in
      Sd (NonEmpty (Only_path only)), x
  | Only_path (Children (Only_yellow (p1, d1, s1), kont)) ->
      let s1, x = Buffer.eject s1 in
      let Pref_right (d1, kont) = pref_right d1 kont in
      let only = (Children (Only_orange (p1, d1, s1), kont)) in
      Sd (NonEmpty (Only_path only)), x
  | Only_path (Children (Only_orange (p1, d1, s1), kont)) ->
      let s1, x = Buffer.eject s1 in
      let d1 = no_pref d1 kont in
      let only = Children (Hole, Only_red (p1, d1, s1)) in
      Sd (NonEmpty (Only_path only)), x
  | Pair_red (left, right) ->
      let result, x = eject_green_right right in
      let result = match result with
         | Any right -> Sd (NonEmpty (Pair_green (left, right)))
         | Exact_6 six -> semi_of_left left six
      in
      result, x

(** Stores a prefix of at least 3 elements and a semi-regular deque containing
    stored triples. *)
type _ unstored =
  Unstored : ('a, _ ge3) prefix * 'a stored_triple sdeque -> 'a unstored

(** Takes a non empty green deque containing stored triples and returns a 
    [unstored]. *)
let pop_stored
= fun d1 ->
    let stored, d1 = pop_green d1 in
    match stored with
    | ST_small p2 -> Unstored (p2, d1)
    | ST_triple (p2, d2, s2) ->
        let s2 = ST_small s2 in
        let d1 = push_semi s2 d1 in
        let d1 = concat_semi (Sd d2) d1 in
        Unstored (p2, d1)

(** Takes a non empty green deque containing stored triples and returns a 
    [unstored]. *)
let eject_stored
= fun d1 ->
    let d1, stored = eject_green d1 in
    match stored with
    | ST_small p2 -> Unstored (p2, d1)
    | ST_triple (p2, d2, s2) ->
        let p2 = ST_small p2 in
        let d1 = inject_semi d1 p2 in
        let d1 = concat_semi d1 (Sd d2) in
        Unstored (s2, d1)

(** Stores either 1 element or a 1 element, a semi-regular deque and another 
    element. *)
type _ sandwich =
  | Alone : 'a -> 'a sandwich
  | Sandwich : 'a * 'a sdeque * 'a -> 'a sandwich

(** Takes a non empty green deque and returns its sandwiched form. *)
let unsandwich_green
: type a. (a, [`green]) non_empty_cdeque -> a sandwich
= function
  | Only_path (Children (Hole, Only_small p1)) ->
      let x, p1 = Buffer.pop p1 in
      begin match Buffer.has1 p1 with
      | Buffer.Exact_0 -> Alone x
      | Buffer.Lte1 p1 ->
          let p1, y = Buffer.eject p1 in
          let d1 = match Buffer.has1 p1 with
            | Buffer.Exact_0 -> Sd Empty
            | Buffer.Lte1 p1 -> Sd (NonEmpty (Only_path (Children (Hole, Only_small p1))))
          in
          Sandwich (x, d1, y)
      end
  | Only_path (Children (Hole, Only_green (p1, d1, s1))) ->
      let x, p1 = Buffer.pop p1 in
      let s1, y = Buffer.eject s1 in
      let Pref_left (d1, k) = pref_left d1 in
      let only = Children (Only_yellow (p1, d1, s1), k) in
      Sandwich (x, Sd (NonEmpty (Only_path only)), y)
  | Only_path (Children (Only_yellow (p1, d1, s1), kont)) ->
      let x, p1 = Buffer.pop p1 in
      let s1, y = Buffer.eject s1 in
      let Pref_right (d1, kont) = pref_right d1 kont in
      let only = (Children (Only_orange (p1, d1, s1), kont)) in
      Sandwich (x, Sd (NonEmpty (Only_path only)), y)
  | Only_path (Children (Only_orange (p1, d1, s1), kont)) ->
      let x, p1 = Buffer.pop p1 in
      let s1, y = Buffer.eject s1 in
      let d1 = no_pref d1 kont in
      let only = Children (Hole, Only_red (p1, d1, s1)) in
      Sandwich (x, Sd (NonEmpty (Only_path only)), y)

  | Pair_red (left, right) ->
      let x, left = pop_green_left left in
      let right, y = eject_green_right right in
      let d1 = match left, right with
        | Any left, Any right -> Sd (NonEmpty (Pair_green (left, right)))
        | Exact_6 lst, Any right -> semi_of_right lst right
        | Any left, Exact_6 lst  -> semi_of_left left lst
        | Exact_6 left_lst, Exact_6 right_lst ->
            let buf = Buffer.empty in
            let buf = Buffer.push6 right_lst buf in
            let buf = Buffer.push6 left_lst  buf in
            Sd (NonEmpty (Only_path (Children (Hole, Only_small buf))))
      in
      Sandwich (x, d1, y)

(** Similarly to [unstored] and [sandwich], stores either a prefix of at least
    3 elements or a prefix of at least 3 elements, a semi-regular deque 
    containing stored triples and a suffix of at least 3 elements. *)
type _ unstored_sandwich =
  | Unstored_alone    : ('a, _ ge3) prefix -> 'a unstored_sandwich
  | Unstored_sandwich : ('a, _ ge3) prefix
                      * 'a stored_triple sdeque
                      * ('a, _ ge3) suffix
                     -> 'a unstored_sandwich

(** Takes a non empty green deque containing stored triple and returns its 
    unstored sandwiched form. *)
let unsandwich_stored
= fun d1 ->
  match unsandwich_green d1 with
  | Alone (ST_small x) -> Unstored_alone x
  | Alone (ST_triple (p1, d1, s1)) -> Unstored_sandwich (p1, Sd d1, s1)
  | Sandwich (ST_small p2, d1, ST_small s3) ->
      Unstored_sandwich (p2, d1, s3)
  | Sandwich (ST_triple (p2, d2, s2), d1, ST_small s3) ->
        let d1 = push_semi (ST_small s2) d1 in
        let d1 = concat_semi (Sd d2) d1 in
        Unstored_sandwich (p2, d1, s3)
  | Sandwich (ST_small p2, d1, ST_triple (p3, d3, s3)) ->
        let d1 = inject_semi d1 (ST_small p3) in
        let d1 = concat_semi d1 (Sd d3) in
        Unstored_sandwich (p2, d1, s3)
  | Sandwich (ST_triple (p2, d2, s2), d1, ST_triple (p3, d3, s3)) ->
        let d1 = push_semi (ST_small s2) d1 in
        let d1 = inject_semi d1 (ST_small p3) in
        let d1 = concat_semi (Sd d2) d1 in
        let d1 = concat_semi d1 (Sd d3) in
        Unstored_sandwich (p2, d1, s3)

(** Takes a prefix and suffix of at least 8 elements and returns a green only 
    triple. *)
let only_small
: type a.
     (a, _ ge8) prefix
  -> (a, _ ge8) suffix
  -> (a, a, [`green], only, nh, nh, nh) triple
= fun p2 s2 ->
  match Buffer.has3p8 s2 with
  | Buffer.Less_than_11 (eight, vec) ->
      let p2 = Buffer.inject_vector (Buffer.inject8 p2 eight) vec in
      Only_small p2
  | Buffer.At_least_11 (a, b, c, s2) ->
      let stored = ST_small (Buffer.triple a b c) in
      let d1 = only_single stored in
      Only_green (p2, d1, s2)

(** Takes a prefix of at least 8 elements, a semi-regular deque containing 
    stored triples and a suffix of at least 8 elements and returns a green only
    triple. *)
let only_green p2 d2 s2 = match d2 with
  | Sd (NonEmpty d2) -> Only_green (p2, d2, s2)
  | Sd Empty -> only_small p2 s2

(** Takes a green or red triple of any color and kind, and returns a green 
    triple of the same kind. *)
let ensure_green
: type a ho c.
     (a, a, c, ho, nh, nh, nh) triple
  -> (a, a, [`green], ho, nh, nh, nh) triple
= fun t ->
  match color t, t with
  (* If the triple is already green, it can be returned as it is. *)
  | Is_green, t ->
      t
  (* If the triple is a red only triple: *)
  | Is_red, Only_red (p1, d1, s1) ->
      begin match Buffer.has8 p1, Buffer.has8 s1 with
      (* if both the prefix and the suffix have more than 8 elements, the 
         triple can be seen as green. *)
      | Buffer.At_least_8 p1, Buffer.At_least_8 s1 ->
          Only_green (p1, d1, s1)
      (* if both the prefix and the suffix have less than 8 elements, the 
         unstored sandwiched form of the child is used to make a green triple. *)
      | Buffer.Less_than_8 p1_lst, Buffer.Less_than_8 s1_lst ->
          begin match unsandwich_stored d1 with
          | Unstored_alone center ->
              let center = Buffer.push_5_vector p1_lst center in
              let center = Buffer.inject_5_vector center s1_lst in
              Only_small center
          | Unstored_sandwich (p2, d2, s2) ->
              let p2 = Buffer.push_5_vector p1_lst p2 in
              let s2 = Buffer.inject_5_vector s2 s1_lst in
              only_green p2 d2 s2
          end
      (* if only one of the two has less than 8 elements, a prefix or suffix 
         can be taken from the child to have enough elements to make a green 
         triple. *)
      | Buffer.Less_than_8 p1_lst, Buffer.At_least_8 s1 ->
          let Unstored (p2, d1) = pop_stored d1 in
          let p2 = Buffer.push_5_vector p1_lst p2 in
          let result = only_green p2 d1 s1 in
          result
      | Buffer.At_least_8 p1, Buffer.Less_than_8 s1_lst ->
          let Unstored (s2, d1) = eject_stored d1 in
          let s2 = Buffer.inject_5_vector s2 s1_lst in
          only_green p1 d1 s2
      end
  (* If the triple is a red left or right triple, the same transformation are 
     made but only for the prefix or the suffix. *)
  | Is_red, Left_red (p1, d1, s1) ->
      begin match Buffer.has8 p1 with
      | Buffer.At_least_8 p1 ->
          Left_green (p1, d1, s1)
      | Buffer.Less_than_8 p1_lst ->
          let Unstored (p2, Sd d1) = pop_stored d1 in
          let p2 = Buffer.push_5_vector p1_lst p2 in
          begin match d1 with
          | Empty -> Left_small (p2, s1)
          | NonEmpty d1 -> Left_green (p2, d1, s1)
          end
      end
  | Is_red, Right_red (p1, d1, s1) ->
      begin match Buffer.has8 s1 with
      | Buffer.At_least_8 s1 ->
          Right_green (p1, d1, s1)
      | Buffer.Less_than_8 s1_lst ->
          let Unstored (s2, Sd d1) = eject_stored d1 in
          let s2 = Buffer.inject_5_vector s2 s1_lst in
          begin match d1 with
          | Empty -> Right_small (p1, s2)
          | NonEmpty d1 -> Right_green (p1, d1, s2)
          end
      end

(** Takes a path of any color and returns a green path containing the same 
    elements. *)
let ensure_green_path
: type a c k. (a, c, k) path -> (a, [`green], k) path
= fun (Children (y, g)) -> Children (y, ensure_green g)

(** Takes a non empty deque of any color and returns a non empty green deque
    containing the same elements. *)
let ensure_green_deque
: type a c. (a, c) non_empty_cdeque -> (a, [`green]) non_empty_cdeque
= function
  | Only_path p -> Only_path (ensure_green_path p)
  | Pair_red (a, b) -> Pair_red (a, b)
  | Pair_green (a, b) ->
      Pair_red (ensure_green_path a, ensure_green_path b)

(** Takes a semi-regular deque and returns a deque containing the same elements. *)
let regular_of_semi
: type a. a sdeque -> a deque
= function
  | Sd Empty -> T Empty
  | Sd (NonEmpty deq) -> T (NonEmpty (ensure_green_deque deq))

(** Poping of a deque. *)
let pop
: type a. a deque -> (a * a deque) option
= fun (T t) ->
  match t with
  | Empty -> None
  | NonEmpty deq ->
      let x, semi_deq = pop_green deq in
      let reg = regular_of_semi semi_deq in
      Some (x, reg)

(** Ejecting from a deque. *)
let eject
: type a. a deque -> (a deque * a) option
= fun (T t) ->
  match t with
  | Empty -> None
  | NonEmpty deq ->
      let semi_deq, x = eject_green deq in
      Some (regular_of_semi semi_deq, x)