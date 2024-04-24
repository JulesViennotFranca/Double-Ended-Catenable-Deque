module Deque = Dequeue.Core

(** A type for suffix buffers. *)
type 'a suffix = 'a Deque.t

(** A type for prefix buffers that need to have at least two elements. *)
type (_, _) prefix =
  | P2 : 'a * 'a                       -> ('a, [`red]) prefix
  | P3 : 'a * 'a * 'a                  -> ('a, [`yellow]) prefix
  | P4 : 'a * 'a * 'a * 'a * 'a suffix -> ('a, [`green]) prefix

(* Types to determine wether it is the end of a packet or not. *)

type is_end = IS_END
type is_not_end = IS_NOT_END

(** A type for packets. *)
type (_, _, _, _) packet =
  | HOLE   : ('a, 'a, [`yellow], is_end) packet
  | Triple : ('a, 'c) prefix
           * ('a pair, 'b, [`yellow], _) packet
           * 'a suffix
          -> ('a, 'b, 'c, is_not_end) packet

(** A type for pairs. *)
and 'a pair =
  Pair : ('a, _) prefix * ('a pair, _) csteque -> 'a pair

(** A type for colored steque. *)
and (_, _) csteque =
  | Suffix : 'a Deque.t -> ('a, [`green]) csteque
  | R  : ('a, 'b, [`red], is_not_end) packet
       * ('b, [`green]) csteque
      -> ('a, [`red]) csteque
  | Y  : ('a, 'b, [`yellow], is_not_end) packet
       * ('b, [`green]) csteque
      -> ('a, [`yellow]) csteque
  | G  : ('a, 'b, [`green ], is_not_end) packet
       * ('b, [< `green | `red]) csteque
      -> ('a, [`green]) csteque
  | Yr : ('a, 'b, [`yellow], is_not_end) packet
       * ('b, [`red]) csteque
      -> ('a, [`orange]) csteque

(** A type for regular steque. *)
and _ t = T : ('a, [< `yellow | `green ]) csteque -> 'a t

(** A type for colored steque where the color decoration is removed. *)
type _ any_csteque = Any_csteque : ('a, _) csteque -> 'a any_csteque

(** The empty colored steque, represented by an empty suffix. *)
let empty_csteque = Suffix Deque.empty

(** The empty steque. *)
let empty = T empty_csteque

(** Tests if a steque is empty. *)
let is_empty = function
  | T (Suffix d) -> Deque.is_empty d
  | _ -> false

(** Takes a green prefix [p], a child colored steque [csteque] and a suffix [s] 
    and returns the green steque (p, csteque, s). *)
let green
: type a c.
  (a, [`green]) prefix -> (a pair, c) csteque -> a suffix -> (a, [`green]) csteque
= fun p csteque s ->
  match csteque with
  | Suffix small -> G (Triple (p, HOLE, s), Suffix small)
  | Y (triple, k) -> G (Triple (p, triple, s), k)
  | Yr (triple, k) -> G (Triple (p, triple, s), k)
  | G (triple, k) -> G (Triple (p, HOLE, s), G (triple, k))
  | R (triple, k) -> G (Triple (p, HOLE, s), R (triple, k))

(** Takes a yellow prefix [p], a child steque [csteque] and a suffix [s] and 
    returns the yellow steque (p, csteque, s). *)
let yellow
: type a.
  (a, [`yellow]) prefix -> (a pair) t -> a suffix -> (a, [`yellow]) csteque
= fun p (T csteque) s ->
  match csteque with
  | Y (child, k)    -> Y (Triple (p, child, s), k)
  | (Suffix _) as k -> Y (Triple (p, HOLE,  s), k)
  | G (g, k)        -> Y (Triple (p, HOLE,  s), G (g, k))

(** Takes a yellow prefix [p], a any steque [csteque] and a suffix [s] and 
    returns the any steque (p, csteque, s). The hidden color of the output 
    steque is either yellow or orange. *)
let orange
: type a. (a, [`yellow]) prefix -> (a pair) any_csteque -> a suffix -> a any_csteque
= fun p (Any_csteque csteque) s ->
  match csteque with
  | Y  (child, k)   -> Any_csteque (Y  (Triple (p, child, s), k))
  | Yr (child, k)   -> Any_csteque (Yr (Triple (p, child, s), k))
  | (G _)      as k -> Any_csteque (Y  (Triple (p, HOLE, s), k))
  | (Suffix _) as k -> Any_csteque (Y  (Triple (p, HOLE, s), k))
  | (R _)      as k -> Any_csteque (Yr (Triple (p, HOLE, s), k))

(** Takes a red prefix [p], a child steque [csteque] and a suffix [s] and
    returns the red steque (p, csteque, s). *)
let red
: type a. (a, [`red]) prefix -> (a pair) t -> a suffix -> (a, [`red]) csteque
= fun p (T csteque) s ->
  match csteque with
  | Y (child, k)    -> R (Triple (p, child, s), k)
  | (Suffix _) as k -> R (Triple (p, HOLE,  s), k)
  | G (g, k)        -> R (Triple (p, HOLE,  s), G (g, k))

(** Pushes onto a green prefix, returns a green one. *)
let green_prefix_push
: type a. a -> (a, [`green]) prefix -> (a, [`green]) prefix
= fun x -> function
  | P4 (a, b, c, d, deq) -> P4 (x, a, b, c, Deque.push d deq)

(** Pushes onto a yellow prefix, returns a green one. *)
let yellow_prefix_push
: type a. a -> (a, [`yellow]) prefix -> (a, [`green]) prefix
= fun x -> function
  | P3 (a, b, c) -> P4 (x, a, b, c, Deque.empty)

(** Pushes onto a red prefix, returns a yellow one. *)
let red_prefix_push
: type a. a -> (a, [`red]) prefix -> (a, [`yellow]) prefix
= fun x -> function
  | P2 (a, b) -> P3 (x, a, b)

(** A type for yellow or green prefix. *)
type _ yg_prefix = Any : ('a, [< `yellow | `green]) prefix -> 'a yg_prefix

(** Pushes onto a prefix, returns a yellow or green one. *)
let prefix_push
: type a c. a -> (a, c) prefix -> a yg_prefix
= fun x p ->
  match p with
  | P2 (a, b) -> Any (P3 (x, a, b))
  | P3 (a, b, c) -> Any (P4 (x, a, b, c, Deque.empty))
  | P4 (a, b, c, d, deq) -> Any (P4 (x, a, b, c, Deque.push d deq))

(** Pushes onto a colored steque and returns a steque. *)
let push'
: type a c. a -> (a, c) csteque -> a t
= fun x t ->
  match t with
  | Suffix s ->
      T (Suffix (Deque.push x s))
  | Yr (Triple (p, child, s), csteque) ->
      let p = yellow_prefix_push x p in
      T (G (Triple (p, child, s), csteque))
  | Y (Triple (p, child, s), csteque) ->
      let p = yellow_prefix_push x p in
      T (G (Triple (p, child, s), csteque))
  | G (Triple (p, child, s), csteque) ->
      let p = green_prefix_push x p in
      T (G (Triple (p, child, s), csteque))
  | R (Triple (p, child, s), csteque) ->
      let p = red_prefix_push x p in
      T (Y (Triple (p, child, s), csteque))

(** Pushes onto any steque. *)
let push_any
: type a. a -> a any_csteque -> a any_csteque
= fun x (Any_csteque t) ->
  let T t = push' x t in
  Any_csteque t

(** Pushes onto any steque and returns a steque. *)
let push_any'
: type a. a -> a any_csteque -> a t
= fun x (Any_csteque t) -> push' x t

(** Pushes onto a steque. *)
let push
: type a. a -> a t -> a t
= fun x (T t) -> push' x t

(** Injects into any steque. *)
let inject_any
: type a. a -> a any_csteque -> a any_csteque
= fun x (Any_csteque t) ->
  match t with
  | Suffix s ->
      Any_csteque (Suffix (Deque.inject s x))
  | Yr (Triple (p, child, s), csteque) ->
      let s = Deque.inject s x in
      Any_csteque (Yr (Triple (p, child, s), csteque))
  | Y (Triple (p, child, s), csteque) ->
      let s = Deque.inject s x in
      Any_csteque (Y (Triple (p, child, s), csteque))
  | G (Triple (p, child, s), csteque) ->
      let s = Deque.inject s x in
      Any_csteque (G (Triple (p, child, s), csteque))
  | R (Triple (p, child, s), csteque) ->
      let s = Deque.inject s x in
      Any_csteque (R (Triple (p, child, s), csteque))

(** Injects into a steque. *)
let inject
: type a. a t -> a -> a t
= fun (T t) x ->
  match t with
  | Suffix s ->
      T (Suffix (Deque.inject s x))
  | Y (Triple (p, child, s), csteque) ->
      let s = Deque.inject s x in
      T (Y (Triple (p, child, s), csteque))
  | G (Triple (p, child, s), csteque) ->
      let s = Deque.inject s x in
      T (G (Triple (p, child, s), csteque))

(** Join a child colored steque [child], a suffix [s] and any steque [ty]. It
    computes case 1 of concatenating two steques: s1 = (_, child, s) and s2 = ty. *)
let join_any
: type a c.
  (a pair, c) csteque -> a suffix -> a any_csteque -> a pair any_csteque * a suffix
= fun child s ty ->
  let child, Any_csteque y =
    match Deque.pop s with
    (* The suffix contains no elements, we do nothing. *)
    | None -> Any_csteque child, ty
    | Some (x, s) ->
        match Deque.pop s with
        (* The suffix contains one element, we push it onto s2. *)
        | None -> Any_csteque child, push_any x ty
        | Some (y, s) ->
            (* The suffix contains more than two elements, we represent it as a 
               prefix ... *)
            let prefix = match Deque.pop s with
              | None ->
                  Pair (P2 (x, y), empty_csteque)
              | Some (z, s) ->
                  match Deque.pop s with
                  | None -> Pair (P3 (x, y, z), empty_csteque)
                  | Some (w, s) ->
                      Pair (P4 (x, y, z, w, s), empty_csteque)
            in
            (* ... and inject (s, empty) into child. *)
            inject_any prefix (Any_csteque child), ty
  in
  (* At this stage, child is the new child of s1 and y is the new form of s2. 
     
     Now we must perform a last operation on child if s2 is a triple, and we 
     can simply return the new child of s1 and the suffix of s2. *)
  match y with
  (* s2 is a suffix, we can return it directly. *)
  | Suffix y_suffix ->
      child, y_suffix
  (* Otherwise, we have to retrieve the prefix and the child of s2, and inject
     the pair (prefix(s2), child(s2)) into child(s1) = child. A lot of cases 
     must be handled but they all do the same thing. *)
  | Y (Triple (y_prefix, Triple (x, y, z), y_suffix), y_csteque) ->
      let y_child = Triple (x, y, z) in
      let yp = Pair (y_prefix, Y (y_child, y_csteque)) in
      inject_any yp child, y_suffix
  | Y (Triple (y_prefix, HOLE, y_suffix), y_csteque) ->
      let yp = Pair (y_prefix, y_csteque) in
      inject_any yp child, y_suffix

  | Yr (Triple (y_prefix, Triple (x, y, z), y_suffix), y_csteque) ->
      let y_child = Triple (x, y, z) in
      let yp = Pair (y_prefix, Yr (y_child, y_csteque)) in
      inject_any yp child, y_suffix
  | Yr (Triple (y_prefix, HOLE, y_suffix), y_csteque) ->
      let yp = Pair (y_prefix, y_csteque) in
      inject_any yp child, y_suffix

  | R (Triple (y_prefix, Triple (x, y, z), y_suffix), y_csteque) ->
      let y_child = Triple (x, y, z) in
      let yp = Pair (y_prefix, Y (y_child, y_csteque)) in
      inject_any yp child, y_suffix
  | R (Triple (y_prefix, HOLE, y_suffix), y_csteque) ->
      let yp = Pair (y_prefix, y_csteque) in
      inject_any yp child, y_suffix

  | G (Triple (y_prefix, Triple (x, y, z), y_suffix), y_csteque) ->
      let y_child = Triple (x, y, z) in
      let Any_csteque y_child = match y_csteque with
        | R (r, k) -> Any_csteque (Yr (y_child, R (r, k)))
        | G (g, k) -> Any_csteque (Y (y_child, G (g, k)))
        | Suffix small -> Any_csteque (Y (y_child, Suffix small))
      in
      let yp = Pair (y_prefix, y_child) in
      inject_any yp child, y_suffix
  | G (Triple (y_prefix, HOLE, y_suffix), y_csteque) ->
      let yp = Pair (y_prefix, y_csteque) in
      inject_any yp child, y_suffix

(** Join a child steque [child], a suffix [s] and any steque [ty]. It computes 
    case 1 of concatenating two steques: s1 = (_, child, s) and s2 = ty. *)
let join_t
: type a. (a pair) t -> a suffix -> a any_csteque -> a pair t * a suffix
= fun child s ty ->
  (* Same code explanations as at [join_any]. *)
  let child, Any_csteque y =
    match Deque.pop s with
    | None -> child, ty
    | Some (x, s) ->
        match Deque.pop s with
        | None -> child, push_any x ty
        | Some (y, s) ->
            let prefix = match Deque.pop s with
              | None -> Pair (P2 (x, y), empty_csteque)
              | Some (z, s) ->
                  match Deque.pop s with
                  | None -> Pair (P3 (x, y, z), empty_csteque)
                  | Some (w, s) -> Pair (P4 (x, y, z, w, s), empty_csteque)
            in
            inject child prefix, ty
  in
  match y with
  | Suffix y_suffix -> child, y_suffix
  | Y (Triple (y_prefix, Triple (x, y, z), y_suffix), y_csteque) ->
      let y_child = Triple (x, y, z) in
      let yp = Pair (y_prefix, Y (y_child, y_csteque)) in
      inject child yp, y_suffix
  | Y (Triple (y_prefix, HOLE, y_suffix), y_csteque) ->
      let yp = Pair (y_prefix, y_csteque) in
      inject child yp, y_suffix

  | G (Triple (y_prefix, Triple (x, y, z), y_suffix), y_csteque) ->
      let y_child = Triple (x, y, z) in
      let Any_csteque y_child = match y_csteque with
        | R (r, k) -> Any_csteque (Yr (y_child, R (r, k)))
        | G (g, k) -> Any_csteque (Y (y_child, G (g, k)))
        | Suffix small -> Any_csteque (Y (y_child, Suffix small))
      in
      let yp = Pair (y_prefix, y_child) in
      inject child yp, y_suffix
  | G (Triple (y_prefix, HOLE, y_suffix), y_csteque) ->
      let yp = Pair (y_prefix, y_csteque) in
      inject child yp, y_suffix

  | Yr (Triple (y_prefix, Triple (x, y, z), y_suffix), y_csteque) ->
      let y_child = Triple (x, y, z) in
      let yp = Pair (y_prefix, Yr (y_child, y_csteque)) in
      inject child yp, y_suffix
  | Yr (Triple (y_prefix, HOLE, y_suffix), y_csteque) ->
      let yp = Pair (y_prefix, y_csteque) in
      inject child yp, y_suffix

  | R (Triple (y_prefix, Triple (x, y, z), y_suffix), y_csteque) ->
      let y_child = Triple (x, y, z) in
      let yp = Pair (y_prefix, Y (y_child, y_csteque)) in
      inject child yp, y_suffix
  | R (Triple (y_prefix, HOLE, y_suffix), y_csteque) ->
      let yp = Pair (y_prefix, y_csteque) in
      inject child yp, y_suffix

(** [c green_or_red] means that [c] is either `green or `red. *)
type _ green_or_red = Green_or_red : [< `green | `red] green_or_red

(** Takes a yellow packet [p] and a green or red steque [csteque], and returns 
    a any steque corresponding to the steque [p ++ csteque]. *)
let split_csteque
: type a b c k.
  c green_or_red -> (a, b, [`yellow], k) packet -> (b, c) csteque -> a any_csteque
= fun green_or_red packet csteque ->
  match packet with
  | HOLE -> Any_csteque csteque
  | Triple (p, c, s) ->
      begin match green_or_red, csteque with
      | _, Suffix t -> Any_csteque (Y (Triple (p, c, s), Suffix t))
      | _, G (t, k) -> Any_csteque (Y (Triple (p, c, s), G (t, k)))
      | _, R (t, k) -> Any_csteque (Yr (Triple (p, c, s), R (t, k)))
      | Green_or_red, _ -> .
      end

(** Takes a yellow packet [p] and a green steque [csteque], and returns a 
    steque corresponding to the steque [p ++ csteque]. *)
let split_green
: type a b k. (a, b, [`yellow], k) packet -> (b, [`green]) csteque -> a t
= fun packet csteque ->
  match packet with
  | HOLE -> T csteque
  | Triple (p, c, s) ->
      begin match csteque with
      | Suffix t -> T (Y (Triple (p, c, s), Suffix t))
      | G (t, k) -> T (Y (Triple (p, c, s), G (t, k)))
      end

(** Takes a yellow packet [p] and a red steque [csteque], and returns any
    steque corresponding to the steque [p ++ csteque]. *)
let split_red
: type a b k. (a, b, [`yellow], k) packet -> (b, [`red]) csteque -> a any_csteque
= fun packet csteque ->
  match packet with
  | HOLE -> Any_csteque csteque
  | Triple (p, c, s) ->
      begin match csteque with
      | R (t, k) -> Any_csteque (Yr (Triple (p, c, s), R (t, k)))
      end

(** A type to represent colored steque either as a suffix [Small s] or as a 
    triple [Parts (p, child, s)]. *)
type _ partition =
  | Small : 'a suffix -> 'a partition
  | Parts : ('a, 'c) prefix * ('a pair, _) csteque * 'a suffix -> 'a partition

(** Takes any steque and returns its partitioned form. *)
let partitioned
: type a. a any_csteque -> a partition
= fun (Any_csteque csteque) ->
  match csteque with
  | Suffix suffix -> Small suffix
  | Y (Triple (p, HOLE, s), k) -> Parts (p, k, s)
  | G (Triple (p, HOLE, s), k) -> Parts (p, k, s)
  | R (Triple (p, HOLE, s), k) -> Parts (p, k, s)
  | Yr (Triple (p, HOLE, s), k) -> Parts (p, k, s)
  | R (Triple (p, Triple (x, y, z), s), k) ->
      Parts (p, Y (Triple (x, y, z), k), s)
  | Y (Triple (p, Triple (x, y, z), s), k) ->
      Parts (p, Y (Triple (x, y, z), k), s)
  | Yr (Triple (p, Triple (x, y, z), s), k) ->
      Parts (p, Yr (Triple (x, y, z), k), s)
  | G (Triple (p, Triple (x, y, z), s), Suffix k) ->
      Parts (p, Y (Triple (x, y, z), Suffix k), s)
  | G (Triple (p, Triple (x, y, z), s), G (g, k)) ->
      Parts (p, Y (Triple (x, y, z), G (g, k)), s)
  | G (Triple (p, Triple (x, y, z), s), R (r, k)) ->
      Parts (p, Yr (Triple (x, y, z), R (r, k)), s)

(** Takes a colored steque [x] and any steque [ty], and returns the any steque 
    being the concatenation of [x] and [ty]. *)
let concat_csteque
: type a c. (a, c) csteque -> a any_csteque -> a any_csteque
= fun x ty ->
  match x with
  (* If our first colored steque is only a suffix, we look at the number of 
     elements it contains. *)
  | Suffix small ->
      begin match Deque.pop small with
      (* No elements, return ty. *)
      | None -> ty
      | Some (x, small) ->
          match Deque.pop small with
          (* One element, push it onto ty. *)
          | None -> push_any x ty
          | Some (y, small) ->
              match Deque.pop small with
              (* Two elements, push them in the right order onto ty. *)
              | None -> push_any x (push_any y ty)
              | Some (z, small) ->
                  match Deque.pop small with
                  (* Three elements, push them in the right order onto ty. *)
                  | None -> push_any x (push_any y (push_any z ty))
                  | Some (w, small) ->
                      (* If we have four or more elements, x can be considered
                         a green prefix. *)
                      let prefix = P4 (x, y, z, w, small) in
                      (* We look wether ty is a suffix or not. *)
                      match partitioned ty with
                      (* If it is the case, we can directly return the green 
                         steque (x, empty, ty) = (prefix, empty, c) here. *)
                      | Small c ->
                          Any_csteque (G (Triple (prefix, HOLE, c), empty_csteque))
                      (* If ty is a triple, its prefix is pushed onto its child 
                         and the final steque is simply (x, child(ty), suffix(ty))
                         = (prefix, child, suffix) here. *)
                      | Parts (p, child, suffix) ->
                          let T child =
                            push_any' (Pair (p, empty_csteque)) (Any_csteque child)
                          in
                          Any_csteque (green prefix child suffix)
      end
  (* Otherwise, we get the child of x with a split function, and use a join 
     function to concatenate the two steques. *)
  | G (Triple (prefix, child, s), csteque) ->
      let Any_csteque child = split_csteque Green_or_red child csteque in
      let Any_csteque rest, suffix = join_any child s ty in
      Any_csteque (green prefix rest suffix)

  | Y (Triple (prefix, child, s), csteque) ->
      let child = split_green child csteque in
      let child, suffix = join_t child s ty in
      Any_csteque (yellow prefix child suffix)

  | Yr (Triple (prefix, child, s), csteque) ->
      let Any_csteque child = split_red child csteque in
      let child, suffix = join_any child s ty in
      orange prefix child suffix

  | R (Triple (prefix, child, s), csteque) ->
      let child = split_green child csteque in
      let child, suffix = join_t child s ty in
      Any_csteque (red prefix child suffix)

(** Translates a steque to any steque. *)
let any_csteque : type a. a t -> a any_csteque
= fun (T t) -> Any_csteque t

(** Concatenates two steques. *)
let concat
: type a. a t -> a t -> a t
= fun (T x) ty ->
  (* Same code explanations as [concat_csteque]. *)
  match x with
  | Suffix small ->
      begin match Deque.pop small with
      | None -> ty
      | Some (x, small) ->
          match Deque.pop small with
          | None -> push x ty
          | Some (y, small) ->
              match Deque.pop small with
              | None -> push x (push y ty)
              | Some (z, small) ->
                  match Deque.pop small with
                  | None -> push x (push y (push z ty))
                  | Some (w, small) ->
                      let prefix = P4 (x, y, z, w, small) in
                      match partitioned (any_csteque ty) with
                      | Small c ->
                          T (G (Triple (prefix, HOLE, c), empty_csteque))
                      | Parts (p, child, suffix) ->
                          let T child =
                            push_any' (Pair (p, empty_csteque)) (Any_csteque child)
                          in
                          T (green prefix child suffix)
      end

  | G (Triple (prefix, child, s), csteque) ->
      let Any_csteque child = split_csteque Green_or_red child csteque in
      let Any_csteque child, suffix = join_any child s (any_csteque ty) in
      T (green prefix child suffix)

  | Y (Triple (prefix, child, s), csteque) ->
      let child = split_green child csteque in
      let child, suffix = join_t child s (any_csteque ty) in
      T (yellow prefix child suffix)

(** Pops a green prefix, returns a yellow or green one. *)
let green_pop
: type a. (a, [`green]) prefix -> a * a yg_prefix
= function
  | P4 (a, b, c, d, deq) ->
      match Deque.pop deq with
      | None -> a, Any (P3 (b, c, d))
      | Some (e, deq) -> a, Any (P4 (b, c, d, e, deq))

(** Pops a yellow prefix, returns a red one. *)
let yellow_pop
: type a. (a, [`yellow]) prefix -> a * (a, [`red]) prefix
= function P3 (a, b, c) -> a, P2 (b, c)

(** Transforms a red steque into a green steque, preserving the set of elements
    it contains. *)
let green_of_red
: type a. (a, [`red]) csteque -> (a, [`green]) csteque
= function
  (* First, we want to see if the child of s (the steque we want to transform)
     is empty or not. *)
  | R (Triple (P2 (a, b), HOLE, s), Suffix small) ->
    begin match Deque.pop small with
    (* If it is the case, we can simply push the two elements of prefix(s) onto
       its suffix, and returns a green suffix steque. *)
    | None -> 
        Suffix (Deque.push a (Deque.push b s))

    (* If not, we can pop a pair from child(s), push the two elements of 
       prefix(s) onto it, and obtain a green prefix. *)
    | Some (Pair (p, s2), small) ->
        let p = match p with
          | P2 (c, d) -> P4 (a, b, c, d, Deque.empty)
          | P3 (c, d, e) -> P4 (a, b, c, d, Deque.push e Deque.empty)
          | P4 (c, d, e, f, deq) ->
              P4 (a, b, c, d, Deque.push e (Deque.push f deq))
        in
        (* Then, to get the child of the final green steque, we concatenate the 
           steque from the poped pair and the rest of child(s). *)
        let Any_csteque child = concat_csteque s2 (Any_csteque (Suffix small)) in
        green p child s
    end

  (* The two cases left do the same thing: pop a pair (p, s2) from child(s), 
     push the two elements of prefix(s) onto p, concatenate s2 and child(s) to 
     form s3, return (p, s3, suffix(s)). *)
  | R (Triple (P2 (a, b), HOLE, s), G (Triple (p, child, s2), k)) ->
      let Pair (p, r), Any yellow_p = green_pop p in
      let p = match p with
        | P2 (c, d) -> P4 (a, b, c, d, Deque.empty)
        | P3 (c, d, e) -> P4 (a, b, c, d, Deque.push e Deque.empty)
        | P4 (c, d, e, f, deq) ->
            P4 (a, b, c, d, Deque.push e (Deque.push f deq))
      in
      let child = match yellow_p, k with
        | P4 (a, b, c, d, deq), k ->
            Any_csteque (G (Triple (P4 (a, b, c, d, deq), child, s2), k))
        | P3 (a, b, c), R (x, k) ->
            Any_csteque (Yr (Triple (P3 (a, b, c), child, s2), R (x, k)))
        | P3 (a, b, c), G (x, k) ->
            Any_csteque (Y (Triple (P3 (a, b, c), child, s2), G (x, k)))
        | P3 (a, b, c), Suffix k ->
            Any_csteque (Y (Triple (P3 (a, b, c), child, s2), Suffix k))
      in
      let Any_csteque child = concat_csteque r child in
      green p child s

  | R (Triple (P2 (a, b), Triple (p, child, s2), s), k) ->
      let Pair (p, r), red_p = yellow_pop p in
      let p = match p with
        | P2 (c, d) -> P4 (a, b, c, d, Deque.empty)
        | P3 (c, d, e) -> P4 (a, b, c, d, Deque.push e Deque.empty)
        | P4 (c, d, e, f, deq) ->
            P4 (a, b, c, d, Deque.push e (Deque.push f deq))
      in
      let child = Any_csteque (R (Triple (red_p, child, s2), k)) in
      let Any_csteque child = concat_csteque r child in
      green p child s

(** [c not_yellow] means that [c] is either `red or `green. (It is the same as 
    green_or_red. )*)
type _ not_yellow = Not_yellow : [< `red | `green ] not_yellow

(** Takes a non-yellow steque and returns its green version. *)
let make_green
: type a c. c not_yellow -> (a, c) csteque -> (a, [`green]) csteque
= fun not_yellow csteque ->
  match not_yellow, csteque with
  | _, Suffix s -> Suffix s
  | _, G (g, k) -> G (g, k)
  | _, R (r, k) -> green_of_red (R (r, k))
  | Not_yellow, _ -> .

(** Pops a steque. *)
let pop
: type a. a t -> (a * a t) option
= fun (T t) ->
  match t with
  (* If our steque is a suffix, we can simply pop the suffix. *)
  | Suffix s ->
      begin match Deque.pop s with
      | None -> None
      | Some (x, s) -> Some (x, T (Suffix s))
      end
  (* If our steque is green, we can end up with a green or yellow steque. *)
  | G (Triple (p, c, s), k) ->
      let x, Any p = green_pop p in
      begin match p with
      (* If the steque is still green, we simply return it. *)
      | (P4 _) as p -> Some (x, T (G (Triple (p, c, s), k)))
      (* If the steque becomes yellow, we must ensure that it is still regular
         by making the following non-yellow child steque green. *)
      | (P3 _) as p ->
          Some (x, T (Y (Triple (p, c, s), make_green Not_yellow k)))
      end
  (* If our steque is yellow, it will become red, we have to make it green in
     order to have a regular steque. *)
  | Y (Triple (p, c, s), k) ->
      let x, p = yellow_pop p in
      Some (x, T (green_of_red (R (Triple (p, c, s), k))))

