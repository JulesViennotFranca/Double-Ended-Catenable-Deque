open Color.GYR

(** A type for colored buffers. *)
type ('a, 'color) buffer =
  | B0 :                           ('a, red) buffer
  | B1 : 'a                     -> ('a, nogreen * _ * _) buffer
  | B2 : 'a * 'a                -> ('a, _) buffer
  | B3 : 'a * 'a * 'a           -> ('a, _) buffer
  | B4 : 'a * 'a * 'a * 'a      -> ('a, nogreen * _ * _) buffer
  | B5 : 'a * 'a * 'a * 'a * 'a -> ('a, red) buffer

  (** A type for packets. *)
type ('a, 'b, 'color) packet =
  (* The empty packet. *)
  | Hole : ('a, 'a, uncolored) packet
  | Packet : ('a, 'c) buffer
           * ('a * 'a, 'b, nogreen * _ * nored) packet
           * ('a, 'c) buffer
          -> ('a, 'b, 'c) packet

type ('color_pkt, 'color_chain) regularity =
  | G : (green , _ * noyellow * _) regularity
  | Y : (yellow, green) regularity
  | R : (red   , green) regularity

(** A typed for colored deques. *)
type ('a, 'color) chain =
  (* Colored deque made of only one buffer. *)
  | Ending : ('a, _) buffer -> ('a, green) chain

  | Chain : ('c1, 'c2) regularity
          * ('a, 'b, 'c1) packet
          * ('b, 'c2) chain
         -> ('a, 'c1) chain

(** A type for deques. *)
type 'a deque = T : ('a, _ * _ * nored) chain -> 'a deque

(** The empty deque. *)
let empty = T (Ending B0)

(** Emptyness test for deques. *)
let is_empty d = d = empty

(** Pushes an element onto a buffer, and returns a green chain. *)
let buffer_push : type a c. a -> (a, c) buffer -> (a, green) chain
= fun x buf ->
  match buf with
  | B0 -> Ending (B1 x)
  | B1 a -> Ending (B2 (x, a))
  | B2 (a, b) -> Ending (B3 (x, a, b))
  | B3 (a, b, c) -> Ending (B4 (x, a, b, c))
  | B4 (a, b, c, d) -> Ending (B5 (x, a, b, c, d))
  | B5 (a, b, c, d, e) ->
      Chain (G, Packet (B3 (x, a, b), Hole, B3 (c, d, e)), Ending B0)

(** Injects an element onto a buffer, and returns a green chain. *)
let buffer_inject : type a c. (a, c) buffer -> a -> (a, green) chain
= fun buf x ->
  match buf with
  | B0 -> Ending (B1 x)
  | B1 a -> Ending (B2 (a, x))
  | B2 (a, b) -> Ending (B3 (a, b, x))
  | B3 (a, b, c) -> Ending (B4 (a, b, c, x))
  | B4 (a, b, c, d) -> Ending (B5 (a, b, c, d, x))
  | B5 (a, b, c, d, e) ->
      Chain (G, Packet (B3 (a, b, c), Hole, B3 (d, e, x)), Ending B0)

(** Pops an element from a buffer, when there is no elements in the buffer, an
    error is raised. Otherwise, it returns the removed element and the new
    buffer. *)
let buffer_pop_unsafe : type a c. (a, c) buffer -> a * (a, red) buffer
= function
  | B0 -> assert false
  | B1 a -> a, B0
  | B2 (a, b) -> a, (B1 b)
  | B3 (a, b, c) -> a, (B2 (b, c))
  | B4 (a, b, c, d) -> a, (B3 (b, c, d))
  | B5 (a, b, c, d, e) -> a, (B4 (b, c, d, e))

(** Pops an element from a buffer, if the buffer is empty, it returns [None],
    otherwise, it returns an option containing the removed element and the new
    buffer. *)
let buffer_pop : type a c. (a, c) buffer -> (a * (a, red) buffer) option
= function
  | B0  -> None
  | buf -> Some (buffer_pop_unsafe buf)

(** Ejects an element from a buffer, when there is no elements in the buffer, an
    error is raised. Otherwise, it returns the new buffer and the removed
    element. *)
let buffer_eject_unsafe : type a c. (a, c) buffer -> (a, red) buffer * a
= function
  | B0 -> assert false
  | B1 a -> B0, a
  | B2 (a, b) -> (B1 a), b
  | B3 (a, b, c) -> (B2 (a, b)), c
  | B4 (a, b, c, d) -> (B3 (a, b, c)), d
  | B5 (a, b, c, d, e) -> (B4 (a, b, c, d)), e

(** Ejects an element from a buffer, if the buffer is empty, it returns [None],
    otherwise, it returns an option containing the removed element and the new
    buffer. *)
let buffer_eject : type a c. (a, c) buffer -> ((a, red) buffer * a) option
= function
  | B0  -> None
  | buf -> Some (buffer_eject_unsafe buf)

(** Pushes an element onto a green buffer, returning a yellow one. *)
let green_push
: type a. a -> (a, green) buffer -> (a, yellow) buffer
= fun x buf ->
  match buf with
  | B2 (a, b) -> B3 (x, a, b)
  | B3 (a, b, c) -> B4 (x, a, b, c)

(** Injects an element onto a green buffer, returning a yellow one. *)
let green_inject
: type a. (a, green) buffer -> a -> (a, yellow) buffer
= fun buf x ->
  match buf with
  | B2 (a, b)    -> B3 (a, b, x)
  | B3 (a, b, c) -> B4 (a, b, c, x)

(** Pops an element from a green buffer, returns the removed element and the
    new yellow buffer. *)
let green_pop : type a. (a, green) buffer -> a * (a, yellow) buffer
= function
  | B2 (a, b)    -> a, B1 b
  | B3 (a, b, c) -> a, B2 (b, c)

(** Ejects an element from a green buffer, returns the new yellow buffer and
    the removed element. *)
let green_eject : type a. (a, green) buffer -> (a, yellow) buffer * a
= function
  | B2 (a, b)    -> B1 a, b
  | B3 (a, b, c) -> B2 (a, b), c

(** Pushes an element onto a yellow buffer, and returns the new buffer. *)
let yellow_push : type a. a -> (a, yellow) buffer -> (a, red) buffer
= fun x buf ->
  match buf with
  | B1 a -> B2 (x, a)
  | B2 (a, b) -> B3 (x, a, b)
  | B3 (a, b, c) -> B4 (x, a, b, c)
  | B4 (a, b, c, d) -> B5 (x, a, b, c, d)

(** Injects an element onto a yellow buffer, and returns the new buffer. *)
let yellow_inject : type a. (a, yellow) buffer -> a -> (a, red) buffer
= fun buf x ->
  match buf with
  | B1 a -> B2 (a, x)
  | B2 (a, b) -> B3 (a, b, x)
  | B3 (a, b, c) -> B4 (a, b, c, x)
  | B4 (a, b, c, d) -> B5 (a, b, c, d, x)

(** Pops an element from a yellow buffer, returns the removed element and the
    new buffer. *)
let yellow_pop : type a. (a, yellow) buffer -> a * (a, red) buffer
= fun buf ->
  match buf with
  | B1 a            -> a, B0
  | B2 (a, b)       -> a, (B1  b)
  | B3 (a, b, c)    -> a, (B2 (b, c))
  | B4 (a, b, c, d) -> a, (B3 (b, c, d))

(** Ejects an element from a yellow buffer, returns the new buffer and the
    removed element. *)
let yellow_eject : type a. (a, yellow) buffer -> (a, red) buffer * a
= fun buf ->
  match buf with
  | B1 a            -> B0,             a
  | B2 (a, b)       -> (B1  a),        b
  | B3 (a, b, c)    -> (B2 (a, b)),    c
  | B4 (a, b, c, d) -> (B3 (a, b, c)), d

(** Performs a push then an eject. *)
let prefix_rot : type a c. a -> (a, c) buffer -> (a, c) buffer * a
= fun x buf -> match buf with
  | B0                 -> B0, x
  | B1 a               -> B1  x, a
  | B2 (a, b)          -> B2 (x, a), b
  | B3 (a, b, c)       -> B3 (x, a, b), c
  | B4 (a, b, c, d)    -> B4 (x, a, b, c), d
  | B5 (a, b, c, d, e) -> B5 (x, a, b, c, d), e

(** Performs an inject then a pop. *)
let suffix_rot : type a c. (a, c) buffer -> a -> a * (a, c) buffer
= fun buf x -> match buf with
  | B0                 -> x, B0
  | B1 a               -> a, B1 x
  | B2 (a, b)          -> a, B2 (b, x)
  | B3 (a, b, c)       -> a, B3 (b, c, x)
  | B4 (a, b, c, d)    -> a, B4 (b, c, d, x)
  | B5 (a, b, c, d, e) -> a, B5 (b, c, d, e, x)

(** Create a green buffer by injecting a pair onto an option.*)
let prefix23 opt (b, c) = match opt with
  | None   -> B2 (b, c)
  | Some a -> B3 (a, b, c)

(** Create a green buffer by pushing a pair onto an option. *)
let suffix23 (a, b) opt = match opt with
  | None   -> B2 (a, b)
  | Some c -> B3 (a, b, c)

(** Create a yellow (or green) buffer by pushing an element onto an option. *)
let suffix12 x opt = match opt with
  | None   -> B1 x
  | Some y -> B2 (x, y)

(** Type ['a decompose] helps us describe a 'a buffer. A buffer with 0 or 1
    elements is considered [Underflow], it cannot be green unless we add
    elements. If the buffer is green, it's [Ok]. And if the buffer has 4 or 5
    elements, the buffer [Overflow], we can make it green by removing a pair. *)
type 'a decompose =
  | Underflow : 'a option -> 'a decompose
  | Ok        : ('a, green) buffer -> 'a decompose
  | Overflow  : ('a, green) buffer * ('a * 'a) -> 'a decompose

(** Returns the decomposed version of a buffer. Here, it is a prefix
    decomposition: when the buffer is overflowed, elements at the end are
    removed. *)
let prefix_decompose : type a c. (a, c) buffer -> a decompose
= function
  (* No element, the buffer is underflowed. *)
  | B0   -> Underflow None
  (* One element, the buffer is underflowed. We keep track of the single
      element as an option type. *)
  | B1 x -> Underflow (Some x)
  (* The buffer is green, it's ok. *)
  | (B2 _) as b -> Ok b
  | (B3 _) as b -> Ok b
  (* The buffer is overflowed, we can remove a pair to make it green. *)
  | B4 (a, b, c, d)    -> Overflow (B2 (a, b), (c, d))
  | B5 (a, b, c, d, e) -> Overflow (B3 (a, b, c), (d, e))

(** Returns the decomposed version of a buffer. Here, it is a suffix
    decomposition: when the buffer is overflowed, elements at the beginning are
    removed. *)
let suffix_decompose : type a c. (a, c) buffer -> a decompose
= function
  (* No element, the buffer is underflowed. *)
  | B0   -> Underflow None
  (* One element, the buffer is underflowed. We keep track of the single
      element as an option type. *)
  | B1 x -> Underflow (Some x)
  (* The buffer is green, it's ok. *)
  | (B2 _) as b -> Ok b
  | (B3 _) as b -> Ok b
  (* The buffer is overflowed, we can remove a pair to make it green. *)
  | B4 (a, b, c, d)    -> Overflow (B2 (c, d), (a, b))
  | B5 (a, b, c, d, e) -> Overflow (B3 (c, d, e), (a, b))


(** Type ['a sandwich] helps us to represent a 'a buffer. If a buffer contains
    0 or 1 element, then it is considered alone and can be represented by an
    option type. If it has more elements, we can represent our buffer by a
    smaller one sandwiched between two elements. *)
type 'a sandwich =
  | Alone : 'a option -> 'a sandwich
  | Sandwich : 'a * ('a, _) buffer * 'a -> 'a sandwich

(** Returns the sandwich representation of a buffer. *)
let buffer_unsandwich : type a c. (a, c) buffer -> a sandwich
= function
  | B0 -> Alone None
  | B1 a -> Alone (Some a)
  | B2 (a, b) -> Sandwich (a, B0, b)
  | B3 (a, b, c) -> Sandwich (a, B1 b, c)
  | B4 (a, b, c, d) -> Sandwich (a, B2 (b, c), d)
  | B5 (a, b, c, d, e) -> Sandwich (a, B3 (b, c, d), e)

(** Translates a 'a buffer to a 'a * 'a buffer. A additional option type is
    returned to handle cases where the buffer contains an odd number of
    elements. *)
let buffer_halve : type a c. (a, c) buffer -> a option * (a * a, red) buffer
= function
  | B0                 -> None,   B0
  | B1 a               -> Some a, B0
  | B2 (a, b)          -> None,   (B1 (a, b))
  | B3 (a, b, c)       -> Some a, (B1 (b, c))
  | B4 (a, b, c, d)    -> None,   (B2 ((a, b), (c, d)))
  | B5 (a, b, c, d, e) -> Some a, (B2 ((b, c), (d, e)))

let to_yellow : type a g y. (a, g * y * nored) buffer -> (a, yellow) buffer
= function
  | B1 a -> B1 a
  | B2 (a, b) -> B2 (a, b)
  | B3 (a, b, c) -> B3 (a, b, c)
  | B4 (a, b, c, d) -> B4 (a, b, c, d)

let to_red : type a c. (a, c) buffer -> (a, red) buffer
= function
  | B0 -> B0
  | B1 a -> B1 a
  | B2 (a, b) -> B2 (a, b)
  | B3 (a, b, c) -> B3 (a, b, c)
  | B4 (a, b, c, d) -> B4 (a, b, c, d)
  | B5 (a, b, c, d, e) -> B5 (a, b, c, d, e)

(** Takes any 'a buffer and a green ('a * 'a) one, and rearranges elements
    contained in the two buffers to return one green 'a buffer and a yellow
    ('a * 'a) buffer. The order of elements is preserved. *)
let green_prefix_concat
: type a c.
      (a, c) buffer
  -> (a * a, green) buffer
  -> (a, green) buffer * ((a * a), yellow) buffer
= fun buf1 buf2 ->
  match prefix_decompose buf1 with
  (* If the first one is already green, we have nothing to do. *)
  | Ok buf1 -> buf1, to_yellow buf2
  (* If the first buffer lacks elements, we pop a pair from the second one and
      inject it onto the first one. *)
  | Underflow opt ->
      let ab, buf2 = green_pop buf2 in
      prefix23 opt ab, buf2
  (* If the first buffer has to much elements, we simply push them onto the
      second one. *)
  | Overflow (buf1, ab) ->
      buf1, green_push ab buf2

(** Takes a ('a * 'a) green buffer and any 'a one, and rearranges elements
    contained in the two buffers to return one ('a * 'a) yellow buffer and one
    green 'a buffer. The order of elements is preserved. *)
let green_suffix_concat
: type a c.
      (a * a, green) buffer
  -> (a, c) buffer
  -> ((a * a), yellow) buffer * (a, green) buffer
= fun buf1 buf2 ->
  match suffix_decompose buf2 with
  | Ok buf2 -> to_yellow buf1, buf2
  | Underflow opt ->
      let buf1, ab = green_eject buf1 in
      buf1, suffix23 ab opt
  | Overflow (buf2, ab) ->
      green_inject buf1 ab, buf2

(** Takes any 'a buffer and a yellow ('a * 'a) one, and rearranges elements
    contained in the two buffers to return one green 'a buffer and any ('a * 'a)
    buffer. The order of elements is preserved. *)
let prefix_concat buf1 buf2 =
  match prefix_decompose buf1 with
  (* If the first one is already green, we have nothing to do. *)
  | Ok buf1 ->
      buf1, to_red buf2
  (* If the first buffer lacks elements, we pop a pair from the second one and
      inject it onto the first one. *)
  | Underflow opt ->
      let ab, buf2 = yellow_pop buf2 in
      prefix23 opt ab, buf2
  (* If the first buffer has to much elements, we simply push them onto the
      second one. *)
  | Overflow (buf1, ab) ->
      buf1, yellow_push ab buf2

(** Takes a yellow ('a * 'a) buffer and any 'a one, and rearranges elements
    contained in the two buffers to return any ('a * 'a) buffer and one green
    'a buffer. The order of elements is preserved. *)
let suffix_concat buf1 buf2 =
  (* The reasoning is the same as in the previous case. *)
  match suffix_decompose buf2 with
  | Ok buf2 ->
      to_red buf1, buf2
  | Underflow opt ->
      let buf1, ab = yellow_eject buf1 in
      buf1, suffix23 ab opt
  | Overflow (buf2, ab) ->
      yellow_inject buf1 ab, buf2

(** Takes a prefix buffer, a following buffer (when the next level is composed
    of only one buffer), and a suffix buffer. It allows to rearrange all
    elements contained in those buffers into a green chain. *)
let make_small
= fun prefix1 buf suffix1 ->
  match prefix_decompose prefix1, suffix_decompose suffix1 with
  (* If the prefix and suffix are green, no changes are needed. In practice, this case
      never occurs as we call the function on a red buffer. *)
  | Ok p1, Ok s1 ->
      Chain (G, Packet (p1, Hole, s1), Ending buf)

  (* Only the prefix is green. *)
  | Ok p1, Underflow opt ->
      begin match buffer_eject buf, opt with
      (* The suffix and the following buffer are empty. We can return a chain
          containing only the prefix. *)
      | None, None   -> Ending p1
      (* If the suffix contains one element and the following buffer is empty.
          We simply inject this element in p1. In practice, this case never
          occurs as we call the function on a red buffer. If the prefix is green,
          the suffix must be red, as it is underflowed it is empty. *)
      | None, Some x -> buffer_inject p1 x
      (* If the following buffer is not empty, we can eject elements from it
          and push them onto our suffix. *)
      | Some (rest, cd), _ ->
          Chain (G, Packet (p1, Hole, suffix23 cd opt), Ending rest)
      end

  (* Only the suffix is green. This is symmetrical to the previous case. *)
  | Underflow opt, Ok s1 ->
      begin match buffer_pop buf, opt with
      | None, None   -> Ending s1
      | None, Some x -> buffer_push x s1
      | Some (cd, rest), _ ->
          Chain (G, Packet (prefix23 opt cd, Hole, s1), Ending rest)
      end

  (* Both the prefix and the suffix are underflowed. *)
  | Underflow p1, Underflow s1 ->
      begin match buffer_unsandwich buf with
      (* If the following buffer has enough elements to be sandwich, we can
          use the sandwiching elements and inject/push them onto our prefix/
          suffix. *)
      | Sandwich (ab, rest, cd) ->
          Chain (G, Packet (prefix23 p1 ab, Hole, suffix23 cd s1), Ending rest)
      (* We don't have enough elements in our following buffer, we have to
          treat our result case by case. It correspond to the "No-Buffer Case"
          from Kaplan and Tarjan's paper. *)
      | Alone opt ->
          begin match p1, opt, s1 with
          | None,   None,        None   -> Ending B0
          | Some a, None,        None
          | None,   None,        Some a -> Ending (B1 a)
          | Some a, None,        Some b
          | None,   Some (a, b), None   -> Ending (B2 (a, b))
          | Some a, Some (b, c), None
          | None,   Some (a, b), Some c -> Ending (B3 (a, b, c))
          | Some a, Some (b, c), Some d -> Ending (B4 (a, b, c, d))
          end
      end

  (* If we have an overflowing prefix and a good suffix, we can simply push its
      excess elements onto the following buffer. *)
  | Overflow (p1, ab), Ok s1 ->
      let buf = buffer_push ab buf in
      Chain (G, Packet (p1, Hole, s1), buf)

  (* This is symmetrical to the previous case. *)
  | Ok p1, Overflow (s1, ab) ->
      let buf = buffer_inject buf ab in
      Chain (G, Packet (p1, Hole, s1), buf)

  (* If the prefix is underflowing and the suffix overflowing, we add the
      suffix's excess elements to the following buffer, and retrieve its first
    pair. This pair can be added to the prefix to make it green. *)
  | Underflow opt, Overflow (s1, ab) ->
      let cd, center = suffix_rot buf ab in
      Chain (G, Packet (prefix23 opt cd, Hole, s1), Ending center)

  (* This is symmetrical to the previous case. *)
  | Overflow (p1, ab), Underflow opt ->
      let center, cd = prefix_rot ab buf in
      Chain (G, Packet (p1, Hole, suffix23 cd opt), Ending center)

  (* If both the prefix and the suffix are overflowing, a new level is added,
      all excess elements can be stored in a yellow packet. *)
  | Overflow (p1, ab), Overflow (s1, cd) ->
      let x, rest = buffer_halve buf in
      let p2 = suffix12 ab x in
      Chain (G, Packet (p1, Packet (p2, Hole, B1 cd), s1), Ending rest)

(** Takes a red chain and returns a green one representing the same set. *)
let green_of_red
: type a. (a, red) chain -> (a, green) chain
= function
  (* If our red packet is at the end of the chain, we handle a lot of different
      cases in the make_small function. *)
  | Chain (R, Packet (p1, Hole, s1), Ending buf) ->
      make_small p1 buf s1
  (* If our red packet is followed by a yellow one, we are in the "Two-Buffer
      Case" from Kaplan and Tarjan's paper. *)
  | Chain (R, Packet (p1, Packet (p2, child, s2), s1), chain) ->
      let p1, p2 = prefix_concat p1 (to_yellow p2) in
      let s2, s1 = suffix_concat (to_yellow s2) s1 in
      Chain (G, Packet (p1, Hole, s1), Chain (R, Packet (p2, child, s2), chain))
  (* If our red packet is followed by a green one, we are in the "Two-Buffer
      Case" from Kaplan and Tarjan's paper. *)
  | Chain (R, Packet (p1, Hole, s1), Chain (G, Packet (p2, child, s2), chain)) ->
      let p1, p2 = green_prefix_concat p1 p2 in
      let s2, s1 = green_suffix_concat s2 s1 in
      Chain (G, Packet (p1, Packet (p2, child, s2), s1), chain)

(** Takes a green or red chain, and returns a green one representing
    the same set. *)
let ensure_green
: type a g r. (a, g * noyellow * r) chain -> (a, green) chain
= function
  | Ending buf -> Ending buf
  | Chain (G, x, k) -> Chain (G, x, k)
  | Chain (R, x, k) -> green_of_red (Chain (R, x, k))

(** Takes a yellow packet, [p1], [child], [s1], and a chain [chain]. Returns
    a deque starting with this packet and followed by the green version of
    [chain]. *)
let yellow p1 child s1 chain =
  T (Chain (Y, Packet (to_yellow p1, child, to_yellow s1), ensure_green chain))

(** Takes a red packet, [p1], [child], [s1], and a green chain [chain].
    Returns the green version of the chain made of the red packet followed by
    the green chain. *)
let red p1 child s1 chain =
  T (green_of_red (Chain (R, Packet (to_red p1, child, to_red s1), chain)))

(** Pushes an element on a deque. *)
let push x (T t) = match t with
  | Ending buf -> T (buffer_push x buf)
  | Chain (G, Packet (p1, child, s1), chain) ->
      let p1 = green_push x p1 in
      yellow p1 child s1 chain
  | Chain (Y, Packet (p1, child, s1), chain) ->
      let p1 = yellow_push x p1 in
      red p1 child s1 chain

(** Injects an element on a deque. *)
let inject (T t) x = match t with
  | Ending buf -> T (buffer_inject buf x)
  | Chain (G, Packet (p1, child, s1), chain) ->
      let s1 = green_inject s1 x in
      yellow p1 child s1 chain
  | Chain (Y, Packet (p1, child, s1), chain) ->
      let s1 = yellow_inject s1 x in
      red p1 child s1 chain

(** Pops an element from a deque. If the deque is empty, it returns [None], if
    not, it returns the removed element and the remaining deque. *)
let pop (T t) = match t with
  | Ending buf ->
    begin match buffer_pop buf with
    | None -> None
    | Some (x, buf) -> Some (x, T (Ending buf))
    end
  | Chain (G, Packet (p1, child, s1), chain) ->
    let x, p1 = green_pop p1 in
    Some (x, yellow p1 child s1 chain)
  | Chain (Y, Packet (p1, child, s1), chain) ->
    let x, p1 = yellow_pop p1 in
    Some (x, red p1 child s1 chain)

(** Ejects an element from a deque. If the deque is empty, it returns [None], if
    not, it returns the remaining deque and the removed element. *)
let eject (T t) = match t with
  | Ending buf ->
    begin match buffer_eject buf with
    | None -> None
    | Some (buf, x) -> Some (T (Ending buf), x)
    end
  | Chain (G, Packet (p1, child, s1), chain) ->
    let s1, x = green_eject s1 in
    Some (yellow p1 child s1 chain, x)
  | Chain (Y, Packet (p1, child, s1), chain) ->
    let s1, x = yellow_eject s1 in
    Some (red p1 child s1 chain, x)