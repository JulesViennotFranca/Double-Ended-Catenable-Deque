type ('a, 'color) buffer =
  | B0 :                           ('a, [`red   ]) buffer
  | B1 : 'a                     -> ('a, [`yellow]) buffer
  | B2 : 'a * 'a                -> ('a, [< `green | `yellow]) buffer
  | B3 : 'a * 'a * 'a           -> ('a, [< `green | `yellow]) buffer
  | B4 : 'a * 'a * 'a * 'a      -> ('a, [`yellow]) buffer
  | B5 : 'a * 'a * 'a * 'a * 'a -> ('a, [`red   ]) buffer

type 'a yellow_buffer =
  Yellowish : ('a, [< `green | `yellow]) buffer -> 'a yellow_buffer

type 'a any_buffer =
  Any : ('a, [< `green | `yellow | `red ]) buffer -> 'a any_buffer

type ('a, 'b, 'color) deque =
  | HOLE : ('a, 'a, [`kont]) deque

  | Yellow : ('a, [< `green | `yellow]) buffer
           * ('a * 'a, 'b, [< `yellow | `kont]) deque
           * ('a, [< `green | `yellow]) buffer
          -> ('a, 'b, [`yellow]) deque

  | Green : ('a, [`green]) buffer
          * ('a * 'a, 'b, [< `yellow | `kont]) deque
          * ('a, [`green]) buffer
         -> ('a, 'b, [`green]) deque

  | Red : ('a, [< `green | `yellow | `red]) buffer
        * ('a * 'a, 'b, [< `yellow | `kont]) deque
        * ('a, [< `green | `yellow | `red]) buffer
       -> ('a, 'b, [`red]) deque

type ('a, 'color) kont =
  | Small : ('a, _) buffer -> ('a, [`green]) kont
  | G : ('a, 'b, [`green ]) deque
      * ('b, [< `green | `red]) kont
     -> ('a, [`green ]) kont
  | Y : ('a, 'b, [`yellow]) deque
      * ('b, [`green]) kont
     -> ('a, [`yellow]) kont
  | R : ('a, 'b, [`red]) deque
      * ('b, [`green]) kont
     -> ('a, [`red]) kont

type 'a s = T : ('a, [< `green | `yellow]) kont -> 'a s

let green_prefix_cons
: type a. a -> (a, [`green]) buffer -> (a, [`yellow]) buffer
= fun x buf ->
  match buf with
  | B2 (a, b) -> B3 (x, a, b)
  | B3 (a, b, c) -> B4 (x, a, b, c)

let green_suffix_snoc
: type a. (a, [`green]) buffer -> a -> (a, [`yellow]) buffer
= fun buf x ->
  match buf with
  | B2 (a, b)    -> B3 (a, b, x)
  | B3 (a, b, c) -> B4 (a, b, c, x)

let yellow_prefix_cons : type a. a -> a yellow_buffer -> a any_buffer
= fun x (Yellowish buf) ->
  match buf with
  | B1 a -> Any (B2 (x, a))
  | B2 (a, b) -> Any (B3 (x, a, b))
  | B3 (a, b, c) -> Any (B4 (x, a, b, c))
  | B4 (a, b, c, d) -> Any (B5 (x, a, b, c, d))

let yellow_suffix_snoc : type a. a yellow_buffer -> a -> a any_buffer
= fun (Yellowish buf) x ->
  match buf with
  | B1 a -> Any (B2 (a, x))
  | B2 (a, b) -> Any (B3 (a, b, x))
  | B3 (a, b, c) -> Any (B4 (a, b, c, x))
  | B4 (a, b, c, d) -> Any (B5 (a, b, c, d, x))

let buffer_cons : type a c. a -> (a, c) buffer -> (a, [`green]) kont
= fun x buf ->
  match buf with
  | B0 -> Small (B1 x)
  | B1 a -> Small (B2 (x, a))
  | B2 (a, b) -> Small (B3 (x, a, b))
  | B3 (a, b, c) -> Small (B4 (x, a, b, c))
  | B4 (a, b, c, d) -> Small (B5 (x, a, b, c, d))
  | B5 (a, b, c, d, e) ->
      G (Green (B3 (x, a, b), HOLE, B3 (c, d, e)), Small B0)

let buffer_snoc : type a c. (a, c) buffer -> a -> (a, [`green]) kont
= fun buf x ->
  match buf with
  | B0 -> Small (B1 x)
  | B1 a -> Small (B2 (a, x))
  | B2 (a, b) -> Small (B3 (a, b, x))
  | B3 (a, b, c) -> Small (B4 (a, b, c, x))
  | B4 (a, b, c, d) -> Small (B5 (a, b, c, d, x))
  | B5 (a, b, c, d, e) ->
      G (Green (B3 (a, b, c), HOLE, B3 (d, e, x)), Small B0)


let green_uncons : type a. (a, [`green]) buffer -> a * a yellow_buffer
= function
  | B2 (a, b)    -> a, Yellowish (B1 b)
  | B3 (a, b, c) -> a, Yellowish (B2 (b, c))

let green_unsnoc : type a. (a, [`green]) buffer -> a yellow_buffer * a
= function
  | B2 (a, b)    -> Yellowish (B1 a), b
  | B3 (a, b, c) -> Yellowish (B2 (a, b)), c

let yellow_uncons : type a. a yellow_buffer -> a * a any_buffer
= fun (Yellowish buf) ->
  match buf with
  | B1 a            -> a, Any B0
  | B2 (a, b)       -> a, Any (B1  b)
  | B3 (a, b, c)    -> a, Any (B2 (b, c))
  | B4 (a, b, c, d) -> a, Any (B3 (b, c, d))

let yellow_unsnoc : type a. a yellow_buffer -> a any_buffer * a
= fun (Yellowish buf) ->
  match buf with
  | B1 a            -> Any B0,             a
  | B2 (a, b)       -> Any (B1  a),        b
  | B3 (a, b, c)    -> Any (B2 (a, b)),    c
  | B4 (a, b, c, d) -> Any (B3 (a, b, c)), d

let buffer_uncons_unsafe : type a c. (a, c) buffer -> a * a any_buffer
= function
  | B0 -> assert false
  | (B1 _) as buf -> yellow_uncons (Yellowish buf)
  | (B2 _) as buf -> yellow_uncons (Yellowish buf)
  | (B3 _) as buf -> yellow_uncons (Yellowish buf)
  | (B4 _) as buf -> yellow_uncons (Yellowish buf)
  | B5 (a, b, c, d, e) -> a, Any (B4 (b, c, d, e))

let buffer_unsnoc_unsafe : type a c. (a, c) buffer -> a any_buffer * a
= function
  | B0 -> assert false
  | (B1 _) as buf -> yellow_unsnoc (Yellowish buf)
  | (B2 _) as buf -> yellow_unsnoc (Yellowish buf)
  | (B3 _) as buf -> yellow_unsnoc (Yellowish buf)
  | (B4 _) as buf -> yellow_unsnoc (Yellowish buf)
  | B5 (a, b, c, d, e) -> Any (B4 (a, b, c, d)), e

let buffer_uncons : type a c. (a, c) buffer -> (a * a any_buffer) option
= function
  | B0  -> None
  | buf -> Some (buffer_uncons_unsafe buf)

let buffer_unsnoc : type a c. (a, c) buffer -> (a any_buffer * a) option
= function
  | B0  -> None
  | buf -> Some (buffer_unsnoc_unsafe buf)

let prefix_rot : type a c. a -> (a, c) buffer -> (a, c) buffer * a
= fun x buf -> match buf with
  | B0                 -> B0, x
  | B1 a               -> B1  x, a
  | B2 (a, b)          -> B2 (x, a), b
  | B3 (a, b, c)       -> B3 (x, a, b), c
  | B4 (a, b, c, d)    -> B4 (x, a, b, c), d
  | B5 (a, b, c, d, e) -> B5 (x, a, b, c, d), e

let suffix_rot : type a c. (a, c) buffer -> a -> a * (a, c) buffer
= fun buf x -> match buf with
  | B0                 -> x, B0
  | B1 a               -> a, B1 x
  | B2 (a, b)          -> a, B2 (b, x)
  | B3 (a, b, c)       -> a, B3 (b, c, x)
  | B4 (a, b, c, d)    -> a, B4 (b, c, d, x)
  | B5 (a, b, c, d, e) -> a, B5 (b, c, d, e, x)


type 'a decompose =
  | Underflow : 'a option -> 'a decompose
  | Ok        : ('a, [`green]) buffer -> 'a decompose
  | Overflow  : ('a, [`green]) buffer * ('a * 'a) -> 'a decompose

let prefix_decompose : type a c. (a, c) buffer -> a decompose
= function
  | B0   -> Underflow None
  | B1 x -> Underflow (Some x)
  | (B2 _) as b -> Ok b
  | (B3 _) as b -> Ok b
  | B4 (a, b, c, d)    -> Overflow (B2 (a, b), (c, d))
  | B5 (a, b, c, d, e) -> Overflow (B3 (a, b, c), (d, e))

let suffix_decompose : type a c. (a, c) buffer -> a decompose
= function
  | B0   -> Underflow None
  | B1 x -> Underflow (Some x)
  | (B2 _) as b -> Ok b
  | (B3 _) as b -> Ok b
  | B4 (a, b, c, d)    -> Overflow (B2 (c, d), (a, b))
  | B5 (a, b, c, d, e) -> Overflow (B3 (c, d, e), (a, b))

let prefix23 opt (b, c) = match opt with
  | None   -> B2 (b, c)
  | Some a -> B3 (a, b, c)

let suffix23 (a, b) opt = match opt with
  | None   -> B2 (a, b)
  | Some c -> B3 (a, b, c)

let prefix12 x opt = match opt with
  | None   -> B1 x
  | Some y -> B2 (x, y)

let green_prefix_concat
: type a c.
     (a, c) buffer
  -> (a * a, [`green]) buffer
  -> (a, [`green]) buffer * (a * a) yellow_buffer
= fun buf1 buf2 ->
  match prefix_decompose buf1 with
  | Ok buf1 -> buf1, Yellowish buf2
  | Underflow opt ->
      let ab, buf2 = green_uncons buf2 in
      prefix23 opt ab, buf2
  | Overflow (buf1, ab) ->
      buf1, Yellowish (green_prefix_cons ab buf2)

let green_suffix_concat
: type a c.
     (a * a, [`green]) buffer
  -> (a, c) buffer
  -> (a * a) yellow_buffer * (a, [`green]) buffer
= fun buf1 buf2 ->
  match suffix_decompose buf2 with
  | Ok buf2 -> Yellowish buf1, buf2
  | Underflow opt ->
      let buf1, ab = green_unsnoc buf1 in
      buf1, suffix23 ab opt
  | Overflow (buf2, ab) ->
      Yellowish (green_suffix_snoc buf1 ab), buf2

let prefix_concat buf1 buf2 =
  match prefix_decompose buf1 with
  | Ok buf1 ->
      let Yellowish buf2 = buf2 in
      buf1, Any buf2
  | Underflow opt ->
      let ab, buf2 = yellow_uncons buf2 in
      prefix23 opt ab, buf2
  | Overflow (buf1, ab) ->
      buf1, yellow_prefix_cons ab buf2

let suffix_concat buf1 buf2 =
  match suffix_decompose buf2 with
  | Ok buf2 ->
      let Yellowish buf1 = buf1 in
      Any buf1, buf2
  | Underflow opt ->
      let buf1, ab = yellow_unsnoc buf1 in
      buf1, suffix23 ab opt
  | Overflow (buf2, ab) ->
      yellow_suffix_snoc buf1 ab, buf2


type 'a sandwich =
  | Alone : 'a option -> 'a sandwich
  | Sandwich : 'a * ('a, _) buffer * 'a -> 'a sandwich

let buffer_unsandwich : type a c. (a, c) buffer -> a sandwich
= function
  | B0 -> Alone None
  | B1 a -> Alone (Some a)
  | B2 (a, b) -> Sandwich (a, B0, b)
  | B3 (a, b, c) -> Sandwich (a, B1 b, c)
  | B4 (a, b, c, d) -> Sandwich (a, B2 (b, c), d)
  | B5 (a, b, c, d, e) -> Sandwich (a, B3 (b, c, d), e)

let buffer_halve : type a c. (a, c) buffer -> a option * (a * a) any_buffer
= function
  | B0                 -> None,   Any B0
  | B1 a               -> Some a, Any B0
  | B2 (a, b)          -> None,   Any (B1 (a, b))
  | B3 (a, b, c)       -> Some a, Any (B1 (b, c))
  | B4 (a, b, c, d)    -> None,   Any (B2 ((a, b), (c, d)))
  | B5 (a, b, c, d, e) -> Some a, Any (B2 ((b, c), (d, e)))

let make_small
= fun prefix1 buf suffix1 ->
  match prefix_decompose prefix1, suffix_decompose suffix1 with
  | Ok p1, Ok s1 ->
      G (Green (p1, HOLE, s1), Small buf)

  | Ok p1, Underflow opt ->
      begin match buffer_unsnoc buf, opt with
      | None, None   -> Small p1
      | None, Some x -> buffer_snoc p1 x
      | Some (Any rest, cd), _ ->
          G (Green (p1, HOLE, suffix23 cd opt), Small rest)
      end

  | Underflow opt, Ok s1 ->
      begin match buffer_uncons buf, opt with
      | None, None   -> Small s1
      | None, Some x -> buffer_cons x s1
      | Some (cd, Any rest), _ ->
          G (Green (prefix23 opt cd, HOLE, s1), Small rest)
      end

  | Underflow p1, Underflow s1 ->
      begin match buffer_unsandwich buf with
      | Sandwich (ab, rest, cd) ->
          G (Green (prefix23 p1 ab, HOLE, suffix23 cd s1), Small rest)
      | Alone opt ->
          begin match p1, opt, s1 with
          | None,   None,        None   -> Small B0
          | Some a, None,        None
          | None,   None,        Some a -> Small (B1 a)
          | Some a, None,        Some b
          | None,   Some (a, b), None   -> Small (B2 (a, b))
          | Some a, Some (b, c), None
          | None,   Some (a, b), Some c -> Small (B3 (a, b, c))
          | Some a, Some (b, c), Some d -> Small (B4 (a, b, c, d))
          end
      end

  | Overflow (p1, ab), Ok s1 ->
      let buf = buffer_cons ab buf in
      G (Green (p1, HOLE, s1), buf)

  | Ok p1, Overflow (s1, ab) ->
      let buf = buffer_snoc buf ab in
      G (Green (p1, HOLE, s1), buf)

  | Underflow opt, Overflow (s1, ab) ->
      let cd, center = suffix_rot buf ab in
      G (Green (prefix23 opt cd, HOLE, s1), Small center)

  | Overflow (p1, ab), Underflow opt ->
      let center, cd = prefix_rot ab buf in
      G (Green (p1, HOLE, suffix23 cd opt), Small center)

  | Overflow (p1, ab), Overflow (s1, cd) ->
      let x, Any rest = buffer_halve buf in
      G (Green (p1, Yellow (prefix12 ab x, HOLE, B1 cd), s1), Small rest)

let green_of_red
: type a. (a, [`red]) kont -> (a, [`green]) kont
= function
  | R (Red (p1, HOLE, s1), Small buf) ->
      make_small p1 buf s1
  | R (Red (p1, Yellow (p2, child, s2), s1), kont) ->
      let p1, Any p2 = prefix_concat p1 (Yellowish p2) in
      let Any s2, s1 = suffix_concat (Yellowish s2) s1 in
      G (Green (p1, HOLE, s1), R (Red (p2, child, s2), kont))
  | R (Red (p1, HOLE, s1), G (Green (p2, child, s2), kont)) ->
      let p1, Yellowish p2 = green_prefix_concat p1 p2 in
      let Yellowish s2, s1 = green_suffix_concat s2 s1 in
      G (Green (p1, Yellow (p2, child, s2), s1), kont)

type _ not_yellow = Not_yellow: [< `green | `red] not_yellow

let ensure_green
: type a c. c not_yellow -> (a, c) kont -> (a, [`green]) kont
= fun Not_yellow t ->
  match t with
  | Small buf -> Small buf
  | G (x, k) -> G (x, k)
  | R (x, k) -> green_of_red (R (x, k))

let yellow p1 child s1 kont =
  T (Y (Yellow (p1, child, s1), ensure_green Not_yellow kont))

let red p1 child s1 kont =
  T (green_of_red (R (Red (p1, child, s1), kont)))

let cons x (T t) = match t with
  | Small buf -> T (buffer_cons x buf)
  | G (Green (p1, child, s1), kont) ->
      let p1 = green_prefix_cons x p1 in
      yellow p1 child s1 kont
  | Y (Yellow (p1, child, s1), kont) ->
      let Any p1 = yellow_prefix_cons x (Yellowish p1) in
      red p1 child s1 kont

let snoc (T t) x = match t with
  | Small buf -> T (buffer_snoc buf x)
  | G (Green (p1, child, s1), kont) ->
      let s1 = green_suffix_snoc s1 x in
      yellow p1 child s1 kont
  | Y (Yellow (p1, child, s1), kont) ->
      let Any s1 = yellow_suffix_snoc (Yellowish s1) x in
      red p1 child s1 kont

let uncons_unsafe (T t) = match t with
  | Small buf ->
      let x, Any buf = buffer_uncons_unsafe buf in
      x, T (Small buf)
  | G (Green (p1, child, s1), kont) ->
      let x, Yellowish p1 = green_uncons p1 in
      x, yellow p1 child s1 kont
  | Y (Yellow (p1, child, s1), kont) ->
      let x, Any p1 = yellow_uncons (Yellowish p1) in
      x, red p1 child s1 kont

let unsnoc_unsafe (T t) = match t with
  | Small buf ->
      let Any buf, x = buffer_unsnoc_unsafe buf in
      T (Small buf), x
  | G (Green (p1, child, s1), kont) ->
      let Yellowish s1, x = green_unsnoc s1 in
      yellow p1 child s1 kont, x
  | Y (Yellow (p1, child, s1), kont) ->
      let Any s1, x = yellow_unsnoc (Yellowish s1) in
      red p1 child s1 kont, x


type 'a t = { length : int ; s : 'a s }

let empty = { length = 0 ; s = T (Small B0) }

let is_empty t = t.length = 0

let length t = abs t.length

let rev t = { t with length = - t.length }

let cons x { length = n ; s } =
  if n >= 0
  then { length = n + 1 ; s = cons x s }
  else { length = n - 1 ; s = snoc s x }

and snoc { length = n ; s } x =
  if n >= 0
  then { length = n + 1 ; s = snoc s x }
  else { length = n - 1 ; s = cons x s }

let uncons { length = n ; s } =
  match n with
  | 0 -> None
  | _ when n >= 0 ->
    let x, s = uncons_unsafe s in
    Some (x, { length = n - 1 ; s })
  | _ ->
    let s, x = unsnoc_unsafe s in
    Some (x, { length = n + 1 ; s })

let unsnoc { length = n ; s } =
  match n with
  | 0 -> None
  | _ when n >= 0 ->
      let s, x = unsnoc_unsafe s in
      Some ({ length = n - 1 ; s }, x)
  | _ ->
      let x, s = uncons_unsafe s in
      Some ({ length = n + 1 ; s }, x)

let is_rev t = t.length < 0