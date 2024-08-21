type ones =
  | HOLE
  | One of ones

type 'color t =
  | Null : [`green] t
  | Zero : ones * [< `green | `red] t -> [`green] t
  | One  : ones * [< `green | `red] t -> [`yellow] t
  | Two  : ones * [`green]          t -> [`red] t

type number = T : [< `green | `yellow] t -> number

type _ not_yellow = Not_yellow : [< `green | `red] not_yellow

let ensure_green : type c. c not_yellow -> c t -> [`green]
t
= fun Not_yellow -> function
  | Null -> Null
  | Zero (ones, t) -> Zero (ones, t)
  (* 2 -> 01 *)
  | Two (HOLE, Null) -> Zero (One HOLE, Null)
  (* 20... -> 01... *)
  | Two (HOLE, Zero (ones, t)) -> Zero (One ones, t)
  (* 21... -> 02... *)
  | Two (One ones, t) -> Zero (HOLE, Two (ones, t))

let succ = function
  | T Null -> T (One (HOLE, Null))
  | T (Zero (ones, t)) -> T (One (ones, t))
  | T (One (ones, t)) ->
      T (ensure_green Not_yellow
           (Two (ones, ensure_green Not_yellow t)))