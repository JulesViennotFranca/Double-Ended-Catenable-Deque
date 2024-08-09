open Color.GYR

type 'color packet =
  | Hole : uncolored packet
  | Green_digit  : (nogreen * _ * nored) packet -> green  packet
  | Yellow_digit : (nogreen * _ * nored) packet -> yellow packet
  | Red_digit    : (nogreen * _ * nored) packet -> red    packet

type ('color_pkt, 'color_chain) regularity =
  | G : (green , _ * noyellow * _) regularity
  | Y : (yellow, green) regularity
  | R : (red   , green) regularity

type 'color chain =
  | Ending : green chain
  | Chain : ('c1, 'c2) regularity * 'c1 packet * 'c2 chain -> 'c1 chain

type number = T : (_ * _ * nored) chain -> number

let green_of_red : red chain -> green chain = function
  | Chain (R, Red_digit Hole, Ending) ->
      Chain (G, Green_digit (Yellow_digit Hole), Ending)
  | Chain (R, Red_digit Hole, Chain (G, Green_digit body, c)) ->
      Chain (G, Green_digit (Yellow_digit body), c)
  | Chain (R, Red_digit (Yellow_digit body), c) ->
      Chain (G, Green_digit Hole, Chain (R, Red_digit body, c))

let ensure_green : type g r. (g * noyellow * r) chain -> green chain = function
  | Ending -> Ending
  | Chain (G, _, _) as c -> c
  | Chain (R, _, _) as c -> green_of_red c

let succ : number -> number = function
  | T Ending -> T (Chain (Y, Yellow_digit Hole, Ending))
  | T (Chain (G, Green_digit pkt, c)) ->
    T (Chain (Y, Yellow_digit pkt, ensure_green c))
  | T (Chain (Y, Yellow_digit pkt, c)) ->
    T (green_of_red (Chain (R, Red_digit pkt, c)))