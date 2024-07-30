type 'color packet =
  | Hole   : [`uncolored] packet
  | Green  : [< `yellow | `uncolored] packet -> [`green ] packet
  | Yellow : [< `yellow | `uncolored] packet -> [`yellow] packet
  | Red    : [< `yellow | `uncolored] packet -> [`red   ] packet

type 'color chain =
  | Ending : [`green ] chain
  | Green  : [`green ] packet * [< `green | `red] chain -> [`green ] chain
  | Yellow : [`yellow] packet * [`green] chain -> [`yellow] chain
  | Red    : [`red   ] packet * [`green] chain -> [`red   ] chain

type number = T : [< `green | `yellow] chain -> number

type 'color not_yellow = NotYellow : [< `green | `red] not_yellow

let ensure_green : type c. c not_yellow -> c chain -> [`green] chain =
  fun NotYellow -> function
    | Ending -> Ending
    | Green (pkt, c) -> Green (pkt, c)
    | Red (Red Hole, Ending) -> Green (Green (Yellow Hole), Ending)
    | Red (Red Hole, Green (Green pkt, c)) -> Green (Green (Yellow pkt), c)
    | Red (Red (Yellow pkt), c) -> Green (Green Hole, Red (Red pkt, c))

let incr : number -> number = function
  | T Ending -> T (Yellow (Yellow Hole, Ending))
  | T (Green (Green pkt, c)) ->
    T (Yellow (Yellow pkt, ensure_green NotYellow c))
  | T (Yellow (Yellow pkt, c)) ->
    T (ensure_green NotYellow (Red (Red pkt, c)))