open Color.GYR

type 'color packet =
  | Hole : uncolored packet
  | GDigit : (nogreen * _ * nored) packet -> green  packet
  | YDigit : (nogreen * _ * nored) packet -> yellow packet
  | RDigit : (nogreen * _ * nored) packet -> red    packet

type ('color_pkt, 'color_chain) regularity =
  | G : (green , _ * noyellow * _) regularity
  | Y : (yellow, green) regularity
  | R : (red   , green) regularity

type 'color chain =
  | Empty :                                                 green chain
  | Chain : ('c1, 'c2) regularity * 'c1 packet * 'c2 chain -> 'c1 chain

type number = T : (_ * _ * nored) chain -> number

let green_of_red : red chain -> green chain = function
  | Chain (R, RDigit Hole, Empty) ->
      Chain (G, GDigit (YDigit Hole), Empty)
  | Chain (R, RDigit Hole, Chain (G, GDigit body, c)) ->
      Chain (G, GDigit (YDigit body), c)
  | Chain (R, RDigit (YDigit body), c) ->
      Chain (G, GDigit Hole, Chain (R, RDigit body, c))

let ensure_green : type g r. (g * noyellow * r) chain -> green chain = fun c ->
  match c with
  | Empty           -> Empty
  | Chain (G, _, _) -> c
  | Chain (R, _, _) -> green_of_red c

let succ : number -> number = function
  | T Empty ->
      T (Chain (Y, YDigit Hole, Empty))
  | T (Chain (G, GDigit body, c)) ->
      T (Chain (Y, YDigit body, ensure_green c))
  | T (Chain (Y, YDigit body, c)) ->
      T (green_of_red (Chain (R, RDigit body, c)))