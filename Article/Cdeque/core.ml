module Deq = Sdeque.Core

type 'a pr = out_channel -> 'a -> unit

(* Support for natural number types. *)

type    z = ZERO
type 'a s = SUCC

type 'a ge1 = 'a s
type 'a ge2 = 'a s s
type 'a ge3 = 'a s s s
type 'a ge4 = 'a s s s s
type 'a ge5 = 'a s s s s s
type 'a ge6 = 'a s s s s s s
type 'a ge7 = 'a s s s s s s s
type 'a ge8 = 'a s s s s s s s s

type eq1 = z s
type eq2 = z ge2
type eq6 = z ge6

(* Some tupple renaming. *)

type 'a four  = 'a * 'a * 'a * 'a
type 'a five  = 'a * 'a * 'a * 'a * 'a
type 'a six   = 'a * 'a * 'a * 'a * 'a * 'a
type 'a eight = 'a * 'a * 'a * 'a * 'a * 'a * 'a * 'a

(** A type for vector of size 0 to 6. The second parameter will always be a
    natural number and represents the maximum number of elements the vector can
    contain. *)
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
  (* The type for buffer is parametrized by the type of elements it contains
     and a type representing the number of elements it contains. *)
  type ('a, 'n) t

  (* Different operations needed on buffers, and how they change the size of
     the buffer. *)

  val empty : ('a, z) t

  val push : 'a -> ('a, 'n) t -> ('a, 'n s) t
  val inject : ('a, 'n) t -> 'a -> ('a, 'n s) t
  val pop : ('a, 'n s) t -> 'a * ('a, 'n) t
  val eject : ('a, 'n s) t -> ('a, 'n) t * 'a

  val push2 : 'a * 'a -> ('a, 'n) t -> ('a, 'n s s) t
  val inject2 : ('a, 'n) t -> 'a * 'a -> ('a, 'n s s) t
  val pop2 : ('a, 'n s s) t -> 'a * 'a * ('a, 'n) t
  val eject2 : ('a, 'n s s) t -> ('a, 'n) t * 'a * 'a
  val two : ('a, eq2) t -> 'a * 'a

  val single : 'a -> ('a, z s) t
  val pair   : 'a -> 'a -> ('a, z s s) t

  val push3 : 'a * 'a * 'a -> ('a, 'n) t -> ('a, 'n s s s) t
  val inject3 : ('a, 'n) t -> 'a * 'a * 'a -> ('a, 'n s s s) t

  val push_5vector : 'a five * ('a, _) vector -> ('a, 'n) t -> ('a, 'n ge5) t
  val inject_5vector : ('a, 'n) t -> 'a five * ('a, _) vector -> ('a, 'n ge5) t

  val push6 : 'a six -> ('a, 'n) t -> ('a, 'n ge6) t
  val inject6 : ('a, 'n) t -> 'a six -> ('a, 'n ge6) t

  val inject8 : ('a, 'n) t -> 'a eight -> ('a, 'n ge8) t

  val push_vector : ('a, _) vector -> ('a, 'n) t -> ('a, 'n) t
  val inject_vector : ('a, 'n) t -> ('a, _) vector -> ('a, 'n) t

  (** A type storing either 0 element or a buffer with at least 1 element. *)
  type _ has1 =
    | Exact_0 : 'a has1
    | At_least_1 : ('a, _ ge1) t -> 'a has1
  (** Tells if a given buffer is empty or not. *)
  val has1 : ('a, 'n) t -> 'a has1

  (** A type storing either 0, 1 or 2 elements, or a buffer with at least 3
      elements. *)
  type 'a has3 =
    | Less_than_3 : ('a, eq2) vector -> 'a has3
    | At_least_3 : ('a, _ ge3) t -> 'a has3

  (** Tells if a given buffer of at least 3 elements has 3, 4, 5 elements or
      more than 6. *)
  val has3p : ('a, _ ge3) t -> ('a * 'a * 'a) * 'a has3

  (** Tells if a given buffer of at least 3 elements has 3, 4, 5 elements or
      more than 6. *)
  val has3s : ('a, _ ge3) t -> 'a has3 * ('a * 'a * 'a)

  (** A type storing either 4 elements or a buffer with at least 5 elements. *)
  type 'a has5 =
    | Exact_4 : 'a four -> 'a has5
    | At_least_5 : ('a, _ ge5) t -> 'a has5

  (** Tells if a given buffer of at least 4 elements has just 4 elements or
      more. *)
  val has5   : ('a, _ ge4) t -> 'a has5

  (** A type storing 6 elements or less or a buffer of at least 7 elements. *)
  type 'a has7 =
    | Less_than_7 : ('a, eq6) vector -> 'a has7
    | At_least_7 : ('a, _ ge7) t -> 'a has7

  (** Tells if a given buffer has 6 elements or less, or if it has more than 7
      elements. *)
  val has7 : ('a, _ ge1) t -> 'a has7

  (** A type storing either 5, 6 or 7 elements, or a buffer with at least 8
      elements. *)
  type 'a has8 =
    | Less_than_8 : ('a five * ('a, eq2) vector) -> 'a has8
    | At_least_8 : ('a, _ ge8) t -> 'a has8

  (** Tells if a given buffer of at least 5 elements has 5, 6, 7 elements or
      more than 8. *)
  val has8   : ('a, _ ge5) t -> 'a has8

  (** A type storing 8, 9 or 10 elements, or a buffer of 3 elements and a
      buffer of at least 8 elements. *)
  type 'a has3p8 =
    | Less_than_11 : 'a eight * ('a, eq2) vector -> 'a has3p8
    | At_least_11 : ('a, z ge3) t * ('a, _ ge8) t -> 'a has3p8

  (** Tells if a given buffer of at least 8 elements has 8, 9 or 10 elements,
      or if it has at least 11 elements. If it the case, it returns a buffer of
      3 elements and a buffer of at least 8 elements. *)
  val has3p8 : ('a, _ ge8) t -> 'a has3p8

end = struct
  type ('a, 'quantity) t = 'a Deq.deque

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
    | At_least_1 : ('a, _ ge1) t -> 'a has1

  let has1 t =
    if Deq.is_empty t
    then Exact_0
    else At_least_1 t

  let push2 (a, b) t = push a (push b t)
  let inject2 t (a, b) = inject (inject t a) b

  let push3 (a, b, c) t = push a (push2 (b, c) t)
  let inject3 t (a, b, c) = inject (inject2 t (a, b)) c
  let pop3 t = let a, b, t = pop2 t in let c, t = pop t in ((a, b, c), t)
  let eject3 t = let t, b, c = eject2 t in let t, a = eject t in (t, (a, b, c))

  let push6 (a, b, c, d, e, f) t =
    push a (push b (push c (push d (push e (push f t)))))
  let inject6 t (a, b, c, d, e, f) =
    inject (inject (inject (inject (inject (inject t a) b) c) d) e) f

  type 'a has3 =
    | Less_than_3 : ('a, eq2) vector -> 'a has3
    | At_least_3 : ('a, _ ge3) t -> 'a has3

  let has3 t =
    match Deq.pop t with
    | None -> Less_than_3 V0
    | Some (x, s) ->
    match Deq.pop s with
    | None -> Less_than_3 (V1 x)
    | Some (y, s) ->
    match Deq.pop s with
    | None -> Less_than_3 (V2 (x, y))
    | Some _ -> At_least_3 t

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
    match has3 t with
    | Less_than_3 vec -> Less_than_8 (five, vec)
    | At_least_3 _ -> At_least_8 buffer

  let has3p buf =
    let three, buf = pop3 buf in
    three, has3 buf

  let has3s buf =
    let buf, three = eject3 buf in
    has3 buf, three

  type 'a has7 =
    | Less_than_7 : ('a, eq6) vector -> 'a has7
    | At_least_7 : ('a, _ ge7) t -> 'a has7

  let has7 t =
    let a, s = pop t in
    match Deq.pop s with
    | None -> Less_than_7 (V1 a)
    | Some (b, s) ->
    match Deq.pop s with
    | None -> Less_than_7 (V2 (a, b))
    | Some (c, s) ->
    match Deq.pop s with
    | None -> Less_than_7 (V3 (a, b, c))
    | Some (d, s) ->
    match Deq.pop s with
    | None -> Less_than_7 (V4 (a, b, c, d))
    | Some (e, s) ->
    match Deq.pop s with
    | None -> Less_than_7 (V5 (a, b, c, d, e))
    | Some (f, s) ->
    match Deq.pop s with
    | None -> Less_than_7 (V6 (a, b, c, d, e, f))
    | Some _ -> At_least_7 t

  type 'a has5 =
    | Exact_4 : 'a four -> 'a has5
    | At_least_5 : ('a, _ ge5) t -> 'a has5

  let has5 buffer =
    let a, b, t = pop2 buffer in
    let c, d, t = pop2 t in
    match has1 t with
    | Exact_0 -> Exact_4 (a, b, c, d)
    | At_least_1 _ -> At_least_5 buffer

  let push_vector v t = vector_fold_right Deq.push v t
  let inject_vector t v = vector_fold_left  Deq.inject t v

  type 'a has3p8 =
    | Less_than_11 : 'a eight * ('a, eq2) vector -> 'a has3p8
    | At_least_11 : ('a, z ge3) t * ('a, _ ge8) t -> 'a has3p8

  let has3p8 t =
    let (a, b, c), (t as t8) = pop3 t in
    let d, e, t = pop2 t in
    let (f, g, h), t = pop3 t in
    match has3 t with
    | Less_than_3 vec -> Less_than_11 ((a, b, c, d, e, f, g, h), vec)
    | At_least_3 _ ->
      let t3 = push a (pair b c) in
      At_least_11 (t3, t8)

  let push5 (a, b, c, d, e) t =
    push a (push b (push c (push d (push e t))))

  let inject5 t (a, b, c, d, e) =
    inject (inject (inject (inject (inject t a) b) c) d) e

  let push_5vector (five, v) t = push5 five (push_vector v t)
  let inject_5vector t (five, v) = inject_vector (inject5 t five) v

  let inject8 t (a, b, c, d, e, f, g, h) =
    inject2 (inject2 (inject2 (inject2 t (a, b)) (c, d)) (e, f)) (g, h)
end

(* Prefixes and suffixes are simply buffers. *)

type ('a, 'n) prefix = ('a, 'n) Buffer.t
type ('a, 'n) suffix = ('a, 'n) Buffer.t

(* Types for different kinds of triples and chains. *)

type only   = ONLY
type pair   = PAIR
type left   = LEFT
type right  = RIGHT

(* Types for ending parameters. *)

type ie = IS_END
type ne = NOT_END

(** The coloring links a color to the size of a prefix and the size of a suffix. *)
type ('sizep, 'sizes, 'c) coloring =
  | G : (_ ge3, _ ge3, [`green ]) coloring
  | Y : (_ ge2, _ ge2, [`yellow]) coloring
  | O : (_ ge1, _ ge1, [`orange]) coloring
  | R : (    _,     _, [`red   ]) coloring

(** A storage represents a prefix - suffix pair.

    [only] storage follow the coloring constraints linking the prefix size, the
    suffix size and the color, except for the ending one, representing solely a
    prefix of at least one element.

    [left] ([right]) storage follow the coloring constraints only for the size
    of the prefix (suffix), the suffix (prefix) containing two elements. The
    prefix (suffix) of an ending left (right) storage must contain at least
    five elements. *)
type ('a, 'kind, 'ending, 'c) storage =
  | Only_end  : ('a, _ ge1) prefix -> ('a, only, ie, [`green]) storage
  | Left_end  : ('a, _ ge5) prefix * ('a,   eq2) suffix
             -> ('a, left , ie, [`green]) storage
  | Right_end : ('a,   eq2) prefix * ('a, _ ge5) suffix
             -> ('a, right, ie, [`green]) storage
  | Only  : ('sizep, 'sizes, 'c) coloring
          * ('a, 'sizep ge5) prefix * ('a, 'sizes ge5) suffix
         -> ('a, only, ne, 'c) storage
  | Left  : ('sizep, _, 'c) coloring
          * ('a, 'sizep ge5) prefix * ('a, eq2) suffix
         -> ('a, left, ne, 'c) storage
  | Right : (_, 'sizes, 'c) coloring
          * ('a, eq2) prefix * ('a, 'sizes ge5) suffix
         -> ('a, right, ne, 'c) storage

(** Chain regularity links the color of a packet to the color of its descending
    chain. A green packet can be followed by chains of any color, a red packet
    must be followed by green chains. *)
type (_, _, _) chain_regularity =
  | Green : ([`green], _, _) chain_regularity
  | Red   : ([`red], [`green], [`green]) chain_regularity

(** A stored triple is either small, and made of one buffer, or big, and made
    of prefix - child - suffix triple. *)
type 'a stored_triple =
  | Small : ('a, _ ge3) prefix -> 'a stored_triple
  | Big : ('a, _ ge3) prefix
        * ('a stored_triple, _, only, _, _, _) chain
        * ('a, _ ge3) suffix
       -> 'a stored_triple

(** A body represents a descending preferred path : it follows yellow and
    orange nodes according to the preferred child relation. A body always end
    with a [Hole]. Its parameters are its input and output types, and its
    input and output kinds. *)
and ('a, 'b, 'head_kind, 'tail_kind) body =
  | Hole : ('a, 'a, 'kind, 'kind) body
  | Only_yellow :
       ('a, 'head_kind, ne, [`yellow]) storage
     * ('a stored_triple, 'b, only, 'tail_kind) body
    -> ('a, 'b, 'head_kind, 'tail_kind) body
  | Only_orange :
       ('a, 'head_kind, ne, [`orange]) storage
     * ('a stored_triple, 'b, only, 'tail_kind) body
    -> ('a, 'b, 'head_kind, 'tail_kind) body
  | Pair_yellow :
       ('a, 'head_kind, ne, [`yellow]) storage
     * ('a stored_triple, 'b, left, 'tail_kind) body
     * ('a stored_triple, only, right, ne, 'c, 'c) chain
    -> ('a, 'b, 'head_kind, 'tail_kind) body
  | Pair_orange :
       ('a, 'head_kind, ne, [`orange]) storage
     * ('a stored_triple, only, left, ne, [`green], [`green]) chain
     * ('a stored_triple, 'b, right, 'tail_kind) body
    -> ('a, 'b, 'head_kind, 'tail_kind) body

(** A packet represents a preferred path and its last node. As the last node is
    not yellow or orange, it is necessarily green or red. The last node take
    the place of the body's hole. Its parameter are its input and output types,
    its input kind, wether or not its last node is an ending one, and the color
    of its last node. *)
and ('a, 'b, 'kind, 'ending, 'color) packet =
  | Packet :
       ('a, 'b, 'kind, 'tail_kind) body
     * ('b, 'tail_kind, 'ending, [< `green | `red] as 'c) storage
    -> ('a, 'b, 'kind, 'ending, 'c) packet

(** A chain represents a semi regular deque with a lot of additional
    information. The first parameter is simply the input type of the deque.

    The second parameter concerns the shape of the chain. [only] means that the
    chain starts with one branch, [pair] means that the chain starts with a
    left and a right branch.

    The third parameter is the kind of the chain. Here, this parameter is used
    to describe two concepts. First, as for other types, the kind represents
    wether the top node of the chain is an only, a left or a right one. But
    this only make sense for only chains, as pair chains have two top nodes.
    Hence, the kind of pair chains is considered to be [only]. In fact, the
    [only] kind also tells us that this chain can be a child of a node. [left]
    and [right] chains can solely be only chains, and alone, they cannot be the
    child of a node.

    The fourth parameter is straight forward, it differentiates the empty chain
    from others. Thanks to it, a ending packet is necessarily followed by the
    empty chain.

    The last two parameters concerns the chain coloring. In the case of a pair
    chain, two colors are needed to know the color of the left path and the
    color of the right path. If the chain is only, the left and right colors
    are the same, the color of its only path. *)
and ('a, 'pair, 'kind, 'ending, 'color_left, 'color_right) chain =
  | Empty : ('a, only, only, ie, [`green], [`green]) chain
  | Only : ('c, 'cl, 'cr) chain_regularity
         * ('a, 'b, 'kind, 'ending, 'c) packet
         * ('b stored_triple, _, only, 'ending, 'cl, 'cr) chain
        -> ('a, only, 'kind, ne, 'c, 'c) chain
  | Pair : ('a, only, left , ne, 'cl, 'cl) chain
         * ('a, only, right, ne, 'cr, 'cr) chain
        -> ('a, pair, only , ne, 'cl, 'cr) chain

(** A type for semi regular deques. *)
type 'a semi_deque = S : ('a, _, only, _, _, _) chain -> 'a semi_deque

(** A type for regular deques. *)
type 'a deque = T : ('a, _, only, _, [`green], [`green]) chain -> 'a deque

(** The empty deque. *)
let empty = T Empty

(** A test to know if a deque is empty or not. *)
let is_empty = function
  | T Empty -> true
  | _ -> false

(** Pushes on a left storage. *)
let push_left_storage
: type a e c. a -> (a, left, e, c) storage -> (a, left, e, c) storage
= fun x store ->
  match store with
  | Left_end (p, s) -> Left_end (Buffer.push x p, s)
  | Left (G, p, s) -> Left (G, Buffer.push x p, s)
  | Left (Y, p, s) -> Left (Y, Buffer.push x p, s)
  | Left (O, p, s) -> Left (O, Buffer.push x p, s)
  | Left (R, p, s) -> Left (R, Buffer.push x p, s)

(** Injects on a right storage. *)
let inject_right_storage
: type a e c. (a, right, e, c) storage -> a -> (a, right, e, c) storage
= fun store x ->
  match store with
  | Right_end (p, s) -> Right_end (p, Buffer.inject s x)
  | Right (G, p, s) -> Right (G, p, Buffer.inject s x)
  | Right (Y, p, s) -> Right (Y, p, Buffer.inject s x)
  | Right (O, p, s) -> Right (O, p, Buffer.inject s x)
  | Right (R, p, s) -> Right (R, p, Buffer.inject s x)

(** Pushes on an only storage. *)
let push_only_storage
: type a e c. a -> (a, only, e, c) storage -> (a, only, e, c) storage
= fun x store ->
  match store with
  | Only_end p -> Only_end (Buffer.push x p)
  | Only (G, p, s) -> Only (G, Buffer.push x p, s)
  | Only (Y, p, s) -> Only (Y, Buffer.push x p, s)
  | Only (O, p, s) -> Only (O, Buffer.push x p, s)
  | Only (R, p, s) -> Only (R, Buffer.push x p, s)

(** Injects on an only storage. *)
let inject_only_storage
: type a e c. (a, only, e, c) storage -> a -> (a, only, e, c) storage
= fun store x ->
  match store with
  | Only_end p -> Only_end (Buffer.inject p x)
  | Only (G, p, s) -> Only (G, p, Buffer.inject s x)
  | Only (Y, p, s) -> Only (Y, p, Buffer.inject s x)
  | Only (O, p, s) -> Only (O, p, Buffer.inject s x)
  | Only (R, p, s) -> Only (R, p, Buffer.inject s x)

(** Pushes on a left packet. *)
let push_left_packet
: type a b e c. a -> (a, b, left, e, c) packet -> (a, b, left, e, c) packet
= fun x (Packet (body, tail)) ->
  match body with
  | Hole -> Packet (Hole, push_left_storage x tail)
  | Only_yellow (head, child) ->
      Packet (Only_yellow (push_left_storage x head, child), tail)
  | Only_orange (head, child) ->
      Packet (Only_orange (push_left_storage x head, child), tail)
  | Pair_yellow (head, child, right) ->
      Packet (Pair_yellow (push_left_storage x head, child, right), tail)
  | Pair_orange (head, left, child) ->
      Packet (Pair_orange (push_left_storage x head, left, child), tail)

(** Injects on a right packet. *)
let inject_right_packet
: type a b e c. (a, b, right, e, c) packet -> a -> (a, b, right, e, c) packet
= fun (Packet (body, tail)) x ->
  match body with
  | Hole -> Packet (Hole, inject_right_storage tail x)
  | Only_yellow (head, child) ->
      Packet (Only_yellow (inject_right_storage head x, child), tail)
  | Only_orange (head, child) ->
      Packet (Only_orange (inject_right_storage head x, child), tail)
  | Pair_yellow (head, child, right) ->
      Packet (Pair_yellow (inject_right_storage head x, child, right), tail)
  | Pair_orange (head, left, child) ->
      Packet (Pair_orange (inject_right_storage head x, left, child), tail)

(** Pushes on an only packet. *)
let push_only_packet
: type a b e c. a -> (a, b, only, e, c) packet -> (a, b, only, e, c) packet
= fun x (Packet (body, tail)) ->
  match body with
  | Hole -> Packet (Hole, push_only_storage x tail)
  | Only_yellow (head, child) ->
      Packet (Only_yellow (push_only_storage x head, child), tail)
  | Only_orange (head, child) ->
      Packet (Only_orange (push_only_storage x head, child), tail)
  | Pair_yellow (head, child, right) ->
      Packet (Pair_yellow (push_only_storage x head, child, right), tail)
  | Pair_orange (head, left, child) ->
      Packet (Pair_orange (push_only_storage x head, left, child), tail)

(** Injects on an only packet. *)
let inject_only_packet
: type a b e c. (a, b, only, e, c) packet -> a -> (a, b, only, e, c) packet
= fun (Packet (body, tail)) x ->
  match body with
  | Hole -> Packet (Hole, inject_only_storage tail x)
  | Only_yellow (head, child) ->
      Packet (Only_yellow (inject_only_storage head x, child), tail)
  | Only_orange (head, child) ->
      Packet (Only_orange (inject_only_storage head x, child), tail)
  | Pair_yellow (head, child, right) ->
      Packet (Pair_yellow (inject_only_storage head x, child, right), tail)
  | Pair_orange (head, left, child) ->
      Packet (Pair_orange (inject_only_storage head x, left, child), tail)

(** Returns an only storage containing only one element. *)
let single_storage x = Only_end (Buffer.single x)

(** Returns a packet containing only one element. *)
let single_packet x = Packet (Hole, single_storage x)

(** Returns a chain containing only one element. *)
let single_chain x = Only (Green, single_packet x, Empty)

(** Pushes on a left chain. *)
let push_left_chain x c = match c with
  | Only (rule, pkt, c) -> Only (rule, push_left_packet x pkt, c)

(** Injects on a right chain. *)
let inject_right_chain c x = match c with
  | Only (rule, pkt, c) -> Only (rule, inject_right_packet pkt x, c)

(** Pushes on a chain. *)
let push_chain
: type a p e cl cr. a -> (a, p, only, e, cl, cr) chain
                      -> (a, p, only, ne, cl, cr) chain
= fun x c ->
  match c with
  | Empty -> single_chain x
  | Only (rule, pkt, c) -> Only (rule, push_only_packet x pkt, c)
  | Pair (left, right) -> Pair (push_left_chain x left, right)

(** Injects on a chain. *)
let inject_chain
: type a p e cl cr. (a, p, only, e, cl, cr) chain -> a
                 -> (a, p, only, ne, cl, cr) chain
= fun c x ->
  match c with
  | Empty -> single_chain x
  | Only (rule, pkt, c) -> Only (rule, inject_only_packet pkt x, c)
  | Pair (left, right) -> Pair (left, inject_right_chain right x)

(** A type for chain without the ending information. *)
type (_, _, _, _, _) no_ending_chain =
  | NE_chain : ('a, 'p, 'k, _, 'cl, 'cr) chain
            -> ('a, 'p, 'k, 'cl, 'cr) no_ending_chain

(** Pushes on chain without keeping track of ending information. *)
let push_ne_chain x (NE_chain c) = NE_chain (push_chain x c)

(** Injects on chain without keeping track of ending information. *)
let inject_ne_chain (NE_chain c) x = NE_chain (inject_chain c x)

(** Pushes a vector on a chain. *)
let push_vector v c = vector_fold_right (fun x c -> push_ne_chain x c) v c

(** Injects a vector on a chain. *)
let inject_vector c v = vector_fold_left (fun c x -> inject_ne_chain c x) c v

(** Pushes on a semi regular deque. *)
let push_semi x (S t) = S (push_chain x t)

(** Injects on a semi regular deque. *)
let inject_semi (S t) x = S (inject_chain t x)

(** Pushes on a regular deque. *)
let push x (T t) = T (push_chain x t)

(** Injects on a regular deque. *)
let inject (T t) x = T (inject_chain t x)

(** Regularity represents constraints between a node color and its child chain
    parameters. The last parameter keeps track of the color of the packet
    starting at this node. *)
type ('color, 'pair, 'ending, 'colorl, 'colorr, 'packet_color) regularity =
  | Green   : ([`green ], _, _, _, _, [`green]) regularity
  | Yellow  : ([`yellow], _, ne, 'cl, _, 'cl) regularity
  | OrangeO : ([`orange], only, ne, 'c, 'c, 'c) regularity
  | OrangeP : ([`orange], pair, ne, [`green], 'cr, 'cr) regularity
  | Red     : ([`red   ], _, _, [`green], [`green], [`red]) regularity

(** A type for the triple representation of a non-empty deque. First comes the
    regularity constraints, then the node as a storage, then the child deque as
    a chain. *)
type ('a, 'kind, 'packet_color) triple =
  | Triple :
       ('c, 'p, 'ending, 'cl, 'cr, 'pktc) regularity
     * ('a, 'kind, 'ending, 'c) storage
     * ('a stored_triple, 'p, only, 'ending, 'cl, 'cr) chain
    -> ('a, 'kind, 'pktc) triple

(** Returns the triple representation of a non-empty only chain. *)
let triple_of_chain
: type a k c. (a, only, k, ne, c, c) chain -> (a, k, c) triple
= function
  | Only (Green, Packet (Hole, tail), child) -> Triple (Green, tail, child)
  | Only (Red  , Packet (Hole, tail), child) -> Triple (Red  , tail, child)
  | Only (rule, Packet (Only_yellow (head, body), tail), child) ->
    Triple (Yellow, head, Only (rule, Packet (body, tail), child))
  | Only (rule, Packet (Only_orange (head, body), tail), child) ->
    Triple (OrangeO, head, Only (rule, Packet (body, tail), child))
  | Only (rule, Packet (Pair_yellow (head, body, right), tail), child) ->
    Triple (Yellow, head, Pair (Only (rule, Packet (body, tail), child), right))
  | Only (rule, Packet (Pair_orange (head, left, body), tail), child) ->
    Triple (OrangeP, head, Pair (left, Only (rule, Packet (body, tail), child)))

(** Returns the non-empty only chain associated to a triple. *)
let chain_of_triple
: type a k c. (a, k, c) triple -> (a, only, k, ne, c, c) chain
= function
  | Triple (Green, head, child) -> Only (Green, Packet (Hole, head), child)
  | Triple (Yellow, head, Only (rule, Packet (body, tail), child)) ->
    Only (rule, Packet (Only_yellow (head, body), tail), child)
  | Triple (Yellow, head, Pair (Only (rule, Packet (body, tail), child), right)) ->
    Only (rule, Packet (Pair_yellow (head, body, right), tail), child)
  | Triple (OrangeO, head, Only (rule, Packet (body, tail), child)) ->
    Only (rule, Packet (Only_orange (head, body), tail), child)
  | Triple (OrangeP, head, Pair (left, Only (rule, Packet (body, tail), child))) ->
    Only (rule, Packet (Pair_orange (head, left, body), tail), child)
  | Triple (Red, head, child) -> Only (Red, Packet (Hole, head), child)

(** A type used to represent left or right triples. If there is not enough
    elements to make one, they are stored in a vector. *)
type (_, _, _) left_right_triple =
  | Not_enough : ('a, eq6) vector -> ('a, _, [`green]) left_right_triple
  | Ok : ('a, 'k, 'c) triple -> ('a, 'k, 'c) left_right_triple

(** Makes a left [left_right_triple] out of an only triple. *)
let left_of_only
: type a c. (a, only, c) triple -> (a, left, c) left_right_triple
= function
  | Triple (Green, Only_end p, Empty) ->
    begin match Buffer.has7 p with
    | Less_than_7 v -> Not_enough v
    | At_least_7 p ->
      let p, y, x = Buffer.eject2 p in
      let s = Buffer.pair y x in
      Ok (Triple (Green, Left_end (p, s), Empty))
    end
  | Triple (reg, Only (coloring, p, s), child) ->
    let s', y, x = Buffer.eject2 s in
    let s = Buffer.pair y x in
    let child = inject_chain child (Small s') in
    Ok (Triple (reg, Left (coloring, p, s), child))

(** Makes a right [left_right_triple] out of an only triple. *)
let right_of_only
: type a c. (a, only, c) triple -> (a, right, c) left_right_triple
= function
  | Triple (Green, Only_end s, Empty) ->
    begin match Buffer.has7 s with
    | Less_than_7 v -> Not_enough v
    | At_least_7 s ->
      let x, y, s = Buffer.pop2 s in
      let p = Buffer.pair x y in
      Ok (Triple (Green, Right_end (p, s), Empty))
    end
  | Triple (reg, Only (coloring, p, s), child) ->
    let x, y, p' = Buffer.pop2 p in
    let p = Buffer.pair x y in
    let child = push_chain (Small p') child in
    Ok (Triple (reg, Right (coloring, p, s), child))

(** Takes a suffix of at least one element, a right prefix, a child chain and a
    right suffix, and returns a stored triple and a left suffix. *)
let make_stored_suffix sleft p child s =
  let pelt = Buffer.two p in
  let p = Buffer.inject2 sleft pelt in
  let s, y, x = Buffer.eject2 s in
  let sleft = Buffer.pair y x in
  (Big (p, child, s), sleft)

(** Takes a left prefix, a child chain, a left suffix and a prefix of at least
    one elements, and returns a right prefix and a stored_triple. *)
let make_prefix_stored p child s pright =
  let selt = Buffer.two s in
  let s = Buffer.push2 selt pright in
  let x, y, p = Buffer.pop2 p in
  let pright = Buffer.pair x y in
  (pright, Big (p, child, s))

(** Takes a suffix of at least one element and a right triple and returns a
    stored triple and a left suffix. *)
let stored_of_right
: type a cr.
     (a, _ ge1) suffix -> (a, right, cr) triple
  -> a stored_triple * (a, eq2) suffix
= fun sl tr ->
  match tr with
  | Triple (Green, Right_end (pr, sr), Empty) ->
    make_stored_suffix sl pr Empty sr
  | Triple (_, Right (_, pr, sr), child) ->
    make_stored_suffix sl pr child sr

(** Takes a left triple and a prefix of at least one element and returns a
    right prefix and a stored triple. *)
let stored_of_left
: type a cl.
     (a, left, cl) triple -> (a, _ ge1) prefix
  -> (a, eq2) prefix * a stored_triple
= fun tl pr ->
  match tl with
  | Triple (Green, Left_end (pl, sl), Empty) ->
    make_prefix_stored pl Empty sl pr
  | Triple (_, Left (_, pl, sl), child) ->
    make_prefix_stored pl child sl pr

(** Makes a left triple out of a pair of left and right triples. *)
let left_of_pair
: type a cl cr.
     (a, left , cl) triple
  -> (a, right, cr) triple
  -> (a, left , cl) triple
= fun tl tr ->
  match tl with
  | Triple (Green, Left_end (p, s), Empty) ->
    let a, s = Buffer.pop s in
    let p = Buffer.inject p a in
    let stored, s = stored_of_right s tr in
    let child = single_chain stored in
    Triple (OrangeO, Left (O, p, s), child)
  | Triple (reg, Left (coloring, p, s), child) ->
    let stored, s = stored_of_right s tr in
    let child = inject_chain child stored in
    Triple (reg, Left (coloring, p, s), child)

(** Makes a right triple out of a pair of left and right triples. *)
let right_of_pair
: type a cl cr.
     (a, left , cl) triple
  -> (a, right, cr) triple
  -> (a, right, cr) triple
= fun tl tr ->
  match tr with
  | Triple (Green, Right_end (p, s), Empty) ->
    let p, a = Buffer.eject p in
    let s = Buffer.push a s in
    let p, stored = stored_of_left tl p in
    let child = single_chain stored in
    Triple (OrangeO, Right (O, p, s), child)
  | Triple (reg, Right (coloring, p, s), child) ->
    let p, stored = stored_of_left tl p in
    let child = push_chain stored child in
    Triple (reg, Right (coloring, p, s), child)

(** Makes a left [left_right_triple] out of a chain. *)
let make_left
: type a p e cl cr. (a, p, only, e, cl, cr) chain -> (a, left, cl) left_right_triple
= function
  | Empty -> Not_enough V0
  | Only _ as c -> left_of_only (triple_of_chain c)
  | Pair (cl, cr) -> Ok (left_of_pair (triple_of_chain cl) (triple_of_chain cr))

(** Makes a right [left_right_triple] out of a chain. *)
let make_right
: type a p e cl cr. (a, p, only, e, cl, cr) chain -> (a, right, cr) left_right_triple
= function
  | Empty -> Not_enough V0
  | Only _ as c -> right_of_only (triple_of_chain c)
  | Pair (cl, cr) -> Ok (right_of_pair (triple_of_chain cl) (triple_of_chain cr))

(** Concatenates two semi regular deques. *)
let concat_semi (S c1) (S c2) =
  match make_left c1 with
  | Not_enough v ->
    let NE_chain c2 = push_vector v (NE_chain c2) in
    S c2
  | Ok tl ->
    match make_right c2 with
    | Not_enough v ->
      let NE_chain c1 = inject_vector (NE_chain c1) v in
      S c1
    | Ok tr -> S (Pair (chain_of_triple tl, chain_of_triple tr))

(** Concatenates two regular deques. *)
let concat (T c1) (T c2) =
  match make_left c1 with
  | Not_enough v ->
    let NE_chain c2 = push_vector v (NE_chain c2) in
    T c2
  | Ok tl ->
    match make_right c2 with
    | Not_enough v ->
      let NE_chain c1 = inject_vector (NE_chain c1) v in
      T c1
    | Ok tr -> T (Pair (chain_of_triple tl, chain_of_triple tr))

(** A type used to represent triples after a pop or eject operation. If the
    remaining triple is still valid, it is stored as it is. If not, it means it
    remains six elements if it was a left or right triple, or no element if it
    was an only triple. The [pair] parameter is used to differentiate between
    those two possible cases. It translates to : was the modified triple part
    of a pair or not. *)
type ('a, 'pair, 'kind) partial_triple =
  | Empty : ('a, only, _) partial_triple
  | End : 'a * 'a * 'a * 'a * 'a * 'a -> ('a, pair, _) partial_triple
  | Ok : ('a, 'k, _) triple -> ('a, _, 'k) partial_triple

(** Returns the orange regularity cases required according to the following
    chain, i.e. if it is an only chain or a pair chain. *)
let orange_reg
: type a p cr.
     (a, p, only, ne, [`green], cr) chain
  -> ([`orange], p, ne, [`green], cr, cr) regularity
= function
  | Only _ -> OrangeO
  | Pair _ -> OrangeP

(** Pops from a green left triple. *)
let pop_left_green = function
  | Triple (Green, Left_end (p, s), Empty) ->
    let a, p = Buffer.pop p in
    begin match Buffer.has5 p with
    | Exact_4 (b, c, d, e) ->
      let f, g = Buffer.two s in
      (a, End (b, c, d, e, f, g))
    | At_least_5 p -> (a, Ok (Triple (Green, Left_end (p, s), Empty)))
    end
  | Triple (reg, Left (coloring, p, s), child) ->
    let a, p = Buffer.pop p in
    match reg, coloring with
    | Green  , G -> (a, Ok (Triple (Yellow, Left (Y, p, s), child)))
    | Yellow , Y -> (a, Ok (Triple (orange_reg child, Left (O, p, s), child)))
    | OrangeO, O -> (a, Ok (Triple (Red, Left (R, p, s), child)))
    | OrangeP, O -> (a, Ok (Triple (Red, Left (R, p, s), child)))

(** Ejects from a green right triple. *)
let eject_right_green = function
  | Triple (Green, Right_end (p, s), Empty) ->
    let s, a = Buffer.eject s in
    begin match Buffer.has5 s with
    | Exact_4 (e, d, c, b) ->
      let g, f = Buffer.two p in
      (End (g, f, e, d, c, b), a)
    | At_least_5 s -> (Ok (Triple (Green, Right_end (p, s), Empty)), a)
    end
  | Triple (reg, Right (coloring, p, s), child) ->
    let s, a = Buffer.eject s in
    match reg, coloring with
    | Green  , G -> (Ok (Triple (Yellow, Right (Y, p, s), child)), a)
    | Yellow , Y -> (Ok (Triple (orange_reg child, Right (O, p, s), child)), a)
    | OrangeO, O -> (Ok (Triple (Red, Right (R, p, s), child)), a)
    | OrangeP, O -> (Ok (Triple (Red, Right (R, p, s), child)), a)

(** Pops from an green only triple. *)
let pop_only_green = function
  | Triple (Green, Only_end p, Empty) ->
    let a, p = Buffer.pop p in
    begin match Buffer.has1 p with
    | Exact_0 -> (a, Empty)
    | At_least_1 p -> (a, Ok (Triple (Green, Only_end p, Empty)))
    end
  | Triple (reg, Only (coloring, p, s), child) ->
    let a, p = Buffer.pop p in
    match reg, coloring with
    | Green  , G -> (a, Ok (Triple (Yellow, Only (Y, p, s), child)))
    | Yellow , Y -> (a, Ok (Triple (orange_reg child, Only (O, p, s), child)))
    | OrangeO, O -> (a, Ok (Triple (Red, Only (R, p, s), child)))
    | OrangeP, O -> (a, Ok (Triple (Red, Only (R, p, s), child)))

(** Ejects from an green only triple. *)
let eject_only_green = function
  | Triple (Green, Only_end s, Empty) ->
    let s, a = Buffer.eject s in
    begin match Buffer.has1 s with
    | Exact_0 -> (Empty, a)
    | At_least_1 s -> (Ok (Triple (Green, Only_end s, Empty)), a)
    end
  | Triple (reg, Only (coloring, p, s), child) ->
    let s, a = Buffer.eject s in
    match reg, coloring with
    | Green  , G -> (Ok (Triple (Yellow, Only (Y, p, s), child)), a)
    | Yellow , Y -> (Ok (Triple (orange_reg child, Only (O, p, s), child)), a)
    | OrangeO, O -> (Ok (Triple (Red, Only (R, p, s), child)), a)
    | OrangeP, O -> (Ok (Triple (Red, Only (R, p, s), child)), a)

(** The sandwich type contains either one element of type [exter] or an element
    of type [inter] sandwiched into two elements of type [exter]. *)
type ('exter, 'inter) sandwich =
  | Alone : 'exter -> ('exter, _) sandwich
  | Sandwich : 'exter * 'inter * 'exter -> ('exter, 'inter) sandwich

(** Takes an green only triple and represent it as a sandwich. *)
let sandwich_only_green
: type a. (a, only, [`green]) triple
       -> (a, (a, only, only) partial_triple) sandwich
= function
  | Triple (Green, Only_end p, Empty) ->
    let a, p = Buffer.pop p in
    begin match Buffer.has1 p with
    | Exact_0 -> Alone a
    | At_least_1 s ->
      let s, z = Buffer.eject s in
      match Buffer.has1 s with
      | Exact_0 -> Sandwich (a, Empty, z)
      | At_least_1 b -> Sandwich (a, Ok (Triple (Green, Only_end b, Empty)), z)
    end
  | Triple (reg, Only (coloring, p, s), child) ->
    let a, p = Buffer.pop p in
    let s, z = Buffer.eject s in
    let t = match reg, coloring with
    | Green  , G -> Ok (Triple (Yellow, Only (Y, p, s), child))
    | Yellow , Y -> Ok (Triple (orange_reg child, Only (O, p, s), child))
    | OrangeO, O -> Ok (Triple (Red, Only (R, p, s), child))
    | OrangeP, O -> Ok (Triple (Red, Only (R, p, s), child))
    in
    Sandwich (a, t, z)

(** Adapts a coloring to a prefix of 8 or more elements. *)
let adapt_to_prefix
: type sp sp1 ss1 c. (sp1, ss1, c) coloring -> (sp ge3, ss1, c) coloring
= function G -> G | Y -> Y | O -> O | R -> R

(** Makes an only triple out of six elements and a right triple. *)
let only_of_right
: type a c.
     (a * a * a * a * a * a)
  -> (a, right, c) triple
  -> (a, only, c) triple
= fun six tr ->
  match tr with
  | Triple (Green, Right_end (p, s), Empty) ->
    let two = Buffer.two p in
    let s = Buffer.push2 two s in
    let s = Buffer.push6 six s in
    Triple (Green, Only_end s, Empty)
  | Triple (reg, Right (coloring, p, s), child) ->
    let p = Buffer.push6 six p in
    Triple (reg, Only (adapt_to_prefix coloring, p, s), child)

(** Adapts a coloring to a suffix of 8 or more elements. *)
let adapt_to_suffix
: type ss sp1 ss1 c. (sp1, ss1, c) coloring -> (sp1, ss ge3, c) coloring
= function G -> G | Y -> Y | O -> O | R -> R

(** Makes an only triple out of a left triple and six elements. *)
let only_of_left
: type a c.
     (a, left, c) triple
  -> (a * a * a * a * a * a)
  -> (a, only, c) triple
= fun tl six ->
  match tl with
  | Triple (Green, Left_end (p, s), Empty) ->
    let two = Buffer.two s in
    let p = Buffer.inject2 p two in
    let p = Buffer.inject6 p six in
    Triple (Green, Only_end p, Empty)
  | Triple (reg, Left (coloring, p, s), child) ->
    let s = Buffer.inject6 s six in
    Triple (reg, Only (adapt_to_suffix coloring, p, s), child)

(** Pops from a green pair chain. *)
let pop_pair_green (Pair (cl, cr)) =
  let tl = triple_of_chain cl in
  let a, tl = pop_left_green tl in
  match tl with
  | End (b, c, d, e, f, g) ->
    let tr = triple_of_chain cr in
    let t = only_of_right (b, c, d, e, f, g) tr in
    (a, S (chain_of_triple t))
  | Ok tl -> (a, S (Pair (chain_of_triple tl, cr)))

(** Ejects from a green pair chain. *)
let eject_pair_green (Pair (cl, cr)) =
  let tr = triple_of_chain cr in
  let tr, a = eject_right_green tr in
  match tr with
  | End (g, f, e, d, c, b) ->
    let tl = triple_of_chain cl in
    let t = only_of_left tl (g, f, e, d, c, b) in
    (S (chain_of_triple t), a)
  | Ok tr -> (S (Pair (cl, chain_of_triple tr)), a)

(** Takes a green pair chain and represent it as a sandwich. *)
let sandwich_pair_green (Pair (cl, cr)) =
  let tl = triple_of_chain cl in
  let tr = triple_of_chain cr in
  let a, tl = pop_left_green tl in
  let tr, z = eject_right_green tr in
  match tl, tr with
  | End (b, c, d, e, f, g), End (t, u, v, w, x, y) ->
    let s = Buffer.empty in
    let s = Buffer.push6 (b, c, d, e, f, g) s in
    let s = Buffer.inject6 s (t, u, v, w, x, y) in
    Sandwich (a, S (Only (Green, Packet (Hole, Only_end s), Empty)), z)
  | End (b, c, d, e, f, g), Ok tr ->
    let t = only_of_right (b, c, d, e, f, g) tr in
    Sandwich (a, S (chain_of_triple t), z)
  | Ok tl, End (t, u, v, w, x, y) ->
    let t = only_of_left tl (t, u, v, w, x, y) in
    Sandwich (a, S (chain_of_triple t), z)
  | Ok tl, Ok tr ->
    Sandwich (a, S (Pair (chain_of_triple tl, chain_of_triple tr)), z)

(** Pops from a non-empty green chain. *)
let pop_green
: type a p.
     (a, p, only, ne, [`green], [`green]) chain
  -> a * a semi_deque
= function
  | Pair _ as c -> pop_pair_green c
  | Only _ as c ->
    let t = triple_of_chain c in
    let a, t = pop_only_green t in
    match t with
    | Empty -> (a, S Empty)
    | Ok t -> (a, S (chain_of_triple t))

(** Ejects from a non-empty green chain. *)
let eject_green
: type a p.
     (a, p, only, ne, [`green], [`green]) chain
  -> a semi_deque * a
= function
  | Pair _ as c -> eject_pair_green c
  | Only _ as c ->
    let t = triple_of_chain c in
    let t, a = eject_only_green t in
    match t with
    | Empty -> (S Empty, a)
    | Ok t -> (S (chain_of_triple t), a)

(** Takes a non-empty green chain and represent it as a sandwich. *)
let sandwich_green
: type a p.
     (a, p, only, ne, [`green], [`green]) chain
  -> (a, a semi_deque) sandwich
= function
  | Pair _ as c -> sandwich_pair_green c
  | Only _ as c ->
    let t = triple_of_chain c in
    match sandwich_only_green t with
    | Alone a -> Alone a
    | Sandwich (a, Empty, z) -> Sandwich (a, S Empty, z)
    | Sandwich (a, Ok t, z) -> Sandwich (a, S (chain_of_triple t), z)

(** Takes a prefix of at least 5 elements, a prefix of at least 3 elements and
    and a semi regular deque of stored triples. Rearranges the elements of the
    second prefix to make the first one green (i.e. at least 8 elements). *)
let make_green_prefix p1 p2 child =
  match Buffer.has3p p2 with
  | three, Less_than_3 v ->
    let p1 = Buffer.inject3 p1 three in
    let p1 = Buffer.inject_vector p1 v in
    (p1, child)
  | three, At_least_3 p2 ->
    let p1 = Buffer.inject3 p1 three in
    let child = push_semi (Small p2) child in
    (p1, child)

(** Takes a semi regular deque of stored triples, a suffix of at least 3
    elements and a suffix of at least 5 elements. Rearranges the elements of
    the first suffix to make the second one green (i.e. at least 8 elements). *)
let make_green_suffix child s2 s1 =
  match Buffer.has3s s2 with
  | Less_than_3 v, three ->
    let s1 = Buffer.push3 three s1 in
    let s1 = Buffer.push_vector v s1 in
    (child, s1)
  | At_least_3 s2, three ->
    let s1 = Buffer.push3 three s1 in
    let child = inject_semi child (Small s2) in
    (child, s1)

(** A type representing prefix and suffix of at least 3 elements. *)
type _ stored_buffer =
  | Stored_buffer : ('a, _ ge3) Buffer.t -> 'a stored_buffer

(** Takes a stored triple and a semi regular deque of stored triples. Extracts
    the prefix of the stored triple, the remaining elements and the semi
    regular deque form a new semi regular deque. *)
let extract_prefix stored child = match stored with
  | Small p -> (Stored_buffer p, child)
  | Big (p, stored_child, s) ->
    let child = push_semi (Small s) child in
    let child = concat_semi (S stored_child) child in
    (Stored_buffer p, child)

(** Takes a semi regular deque of stored triples and a stored triple. Extracs
    the suffix of the stored triple, the semi regular deque and the remaining
    elements form a new semi regular deque. *)
let extract_suffix child stored = match stored with
  | Small s -> (child, Stored_buffer s)
  | Big (p, stored_child, s) ->
    let child = inject_semi child (Small p) in
    let child = concat_semi child (S stored_child) in
    (child, Stored_buffer s)

(** Takes a prefix of at least 5 elements and a semi regular deque of stored
    triples. Rearranges elements of the semi regular deque to make the prefix
    green. *)
let ensure_green_prefix p child =
  let stored, child = pop_green child in
  let Stored_buffer p2, child = extract_prefix stored child in
  make_green_prefix p p2 child

(** Takes a semi regular deque of stored triples and a suffix of at least 5
    elements. Rearranges elements of the semi regular deque to make the suffix
    green. *)
let ensure_green_suffix child s =
  let child, stored = eject_green child in
  let child, Stored_buffer s2 = extract_suffix child stored in
  make_green_suffix child s2 s

(** Takes a body, a following red left storage and the following green chain,
    and makes a green chain out of them. *)
let ensure_green_left body (Left (R, p, s)) child =
  let p, S child = ensure_green_prefix p child in
  match child with
  | Empty -> Only (Green, Packet (body, Left_end (p, s)), Empty)
  | Only _ as child -> Only (Green, Packet (body, Left (G, p, s)), child)
  | Pair _ as child -> Only (Green, Packet (body, Left (G, p, s)), child)

(** Takes a body, a following red right storage and the following green chain,
    and makes a green chain out of them. *)
let ensure_green_right body (Right (R, p, s)) child =
  let S child, s = ensure_green_suffix child s in
  match child with
  | Empty -> Only (Green, Packet (body, Right_end (p, s)), Empty)
  | Only _ as child -> Only (Green, Packet (body, Right (G, p, s)), child)
  | Pair _ as child -> Only (Green, Packet (body, Right (G, p, s)), child)

(** Takes a body and a following green triple, and makes a green chain out of
    them. *)
let make_green_only body (p, S child, s) =
  match child with
  | Only _ as child -> Only (Green, Packet (body, Only (G, p, s)), child)
  | Pair _ as child -> Only (Green, Packet (body, Only (G, p, s)), child)
  | Empty ->
    match Buffer.has3p8 s with
    | Less_than_11 (eight, v) ->
      let p = Buffer.inject8 p eight in
      let p = Buffer.inject_vector p v in
      Only (Green, Packet (body, Only_end p), Empty)
    | At_least_11 (small, s) ->
      Only (Green, Packet (body, Only (G, p, s)), single_chain (Small small))

(** Takes a body, a following red only storage and the following green chain,
    and makes a green chain out of them. *)
let ensure_green_only body (Only (R, p, s) : _ storage) child =
  match Buffer.has8 p, Buffer.has8 s with
  | At_least_8 p, At_least_8 s ->
    Only (Green, Packet (body, Only (G, p, s)), child)
  | At_least_8 p, Less_than_8 _ ->
    let child, s = ensure_green_suffix child s in
    make_green_only body (p, child, s)
  | Less_than_8 _, At_least_8 s ->
    let p, child = ensure_green_prefix p child in
    make_green_only body (p, child, s)
  | Less_than_8 eltp, Less_than_8 elts ->
    match sandwich_green child with
    | Alone (Small p) ->
      let p = Buffer.push_5vector eltp p in
      let s = Buffer.inject_5vector p elts in
      Only (Green, Packet (body, Only_end s), Empty)
    | Alone (Big (p, child, s)) ->
      let p = Buffer.push_5vector eltp p in
      let s = Buffer.inject_5vector s elts in
      make_green_only body (p, S child, s)
    | Sandwich (storedl, child, storedr) ->
      let Stored_buffer p, child = extract_prefix storedl child in
      let child, Stored_buffer s = extract_suffix child storedr in
      let p = Buffer.push_5vector eltp p in
      let s = Buffer.inject_5vector s elts in
      make_green_only body (p, child, s)

(** Takes any chain and makes it green. *)
let rec ensure_green
: type a p k e cl cr.
     (a, p, k, e, cl, cr) chain
  -> (a, p, k, e, [`green], [`green]) chain
= function
  | Empty -> Empty
  | Only (Green, pkt, c) -> Only (Green, pkt, c)
  | Only (Red, Packet (body, red), rest) ->
    begin match red with
    | Only  _ as red -> ensure_green_only  body red rest
    | Left  _ as red -> ensure_green_left  body red rest
    | Right _ as red -> ensure_green_right body red rest
    end
  | Pair (cl, cr) ->
    Pair (ensure_green cl, ensure_green cr)

(** Pops from a regular deque. *)
let pop (T c) = match c with
  | Empty -> None
  | Only _ as c ->
    let a, S c = pop_green c in
    Some (a, T (ensure_green c))
  | Pair _ as c ->
    let a, S c = pop_green c in
    Some (a, T (ensure_green c))

(** Ejects from a regular deque. *)
let eject (T c) = match c with
  | Empty -> None
  | Only _ as c ->
    let S c, z = eject_green c in
    Some (T (ensure_green c), z)
  | Pair _ as c ->
    let S c, z = eject_green c in
    Some (T (ensure_green c), z)