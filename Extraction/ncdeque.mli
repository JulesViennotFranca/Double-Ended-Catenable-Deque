open Datatypes

type green_hue =
| SomeGreen
| NoGreen

type yellow_hue =
| SomeYellow
| NoYellow

type red_hue =
| SomeRed
| NoRed

type color =
| Mix of green_hue * yellow_hue * red_hue

type 'a prodN =
| Coq_prodZ of 'a
| Coq_prodS of nat * 'a prodN * 'a prodN

type 'a buffer =
| B0
| B1 of 'a prodN
| B2 of green_hue * yellow_hue * 'a prodN * 'a prodN
| B3 of green_hue * yellow_hue * 'a prodN * 'a prodN * 'a prodN
| B4 of 'a prodN * 'a prodN * 'a prodN * 'a prodN
| B5 of 'a prodN * 'a prodN * 'a prodN * 'a prodN * 'a prodN

type 'a yellow_buffer =
| Yellowish of green_hue * yellow_hue * 'a buffer

type 'a any_buffer =
| Any of color * 'a buffer

type packet_color =
| PCGreen
| PCYellow of green_hue * yellow_hue * green_hue * yellow_hue
| PCRed of color * color

type 'a packet =
| Hole
| Triple of nat * nat * nat * nat * yellow_hue * color * color * color
   * 'a buffer * 'a packet * 'a buffer * packet_color

val power2 : nat -> nat

type cdeque_color =
| CCGreen of green_hue * red_hue
| CCYellow
| CCRed

type 'a cdeque =
| Small of nat * color * 'a buffer
| Big of nat * nat * nat * nat * nat * color * color * 'a packet * 'a cdeque
   * cdeque_color

val size_option : 'a1 option -> nat

type 'a decompose =
| Underflow of 'a prodN option
| Ok of nat * 'a buffer
| Overflow of nat * 'a buffer * 'a prodN

type 'a sandwich =
| Alone of 'a prodN option
| Sandwich of nat * color * 'a prodN * 'a buffer * 'a prodN

type 'a deque =
| T of green_hue * yellow_hue * 'a cdeque

val prodN_seq : nat -> 'a1 prodN -> 'a1 list

val buffer_seq : nat -> nat -> color -> 'a1 buffer -> 'a1 list

val packet_left_seq : nat -> nat -> nat -> color -> 'a1 packet -> 'a1 list

val packet_right_seq : nat -> nat -> nat -> color -> 'a1 packet -> 'a1 list

val cdeque_seq : nat -> nat -> color -> 'a1 cdeque -> 'a1 list

val deque_seq : nat -> 'a1 deque -> 'a1 list

val map_deque :
  (nat -> 'a1 -> 'a2 list) -> nat -> nat -> 'a1 deque -> 'a2 list

val cempty : nat -> 'a1 cdeque

val empty : 'a1 deque

val green_push : nat -> nat -> 'a1 prodN -> 'a1 buffer -> 'a1 buffer

val green_inject : nat -> nat -> 'a1 buffer -> 'a1 prodN -> 'a1 buffer

val green_pop_obligations_obligation_2 : green_hue

val green_pop_obligations_obligation_3 : yellow_hue

val green_pop :
  nat -> nat -> 'a1 buffer -> ('a1 prodN, 'a1 yellow_buffer) prod

val green_eject_obligations_obligation_2 : green_hue

val green_eject_obligations_obligation_3 : yellow_hue

val green_eject :
  nat -> nat -> 'a1 buffer -> ('a1 yellow_buffer, 'a1 prodN) prod

val yellow_push_obligations_obligation_1 : green_hue

val yellow_push_obligations_obligation_2 : yellow_hue

val yellow_push_obligations_obligation_4 : green_hue -> green_hue

val yellow_push_obligations_obligation_5 : yellow_hue -> yellow_hue

val yellow_push :
  nat -> nat -> 'a1 prodN -> 'a1 yellow_buffer -> 'a1 any_buffer

val yellow_inject_obligations_obligation_1 : green_hue

val yellow_inject_obligations_obligation_2 : yellow_hue

val yellow_inject_obligations_obligation_4 : green_hue -> green_hue

val yellow_inject_obligations_obligation_5 : yellow_hue -> yellow_hue

val yellow_inject :
  nat -> nat -> 'a1 yellow_buffer -> 'a1 prodN -> 'a1 any_buffer

val yellow_pop_obligations_obligation_3 : green_hue -> green_hue

val yellow_pop_obligations_obligation_4 : yellow_hue -> yellow_hue

val yellow_pop_obligations_obligation_6 : green_hue

val yellow_pop_obligations_obligation_7 : yellow_hue

val yellow_pop :
  nat -> nat -> 'a1 yellow_buffer -> ('a1 prodN, 'a1 any_buffer) prod

val yellow_eject_obligations_obligation_3 : green_hue -> green_hue

val yellow_eject_obligations_obligation_4 : yellow_hue -> yellow_hue

val yellow_eject_obligations_obligation_6 : green_hue

val yellow_eject_obligations_obligation_7 : yellow_hue

val yellow_eject :
  nat -> nat -> 'a1 yellow_buffer -> ('a1 any_buffer, 'a1 prodN) prod

val buffer_push_obligations_obligation_2 : green_hue

val buffer_push_obligations_obligation_3 : yellow_hue

val buffer_push_obligations_obligation_5 : green_hue -> green_hue

val buffer_push_obligations_obligation_6 : yellow_hue -> yellow_hue

val buffer_push : nat -> nat -> color -> 'a1 prodN -> 'a1 buffer -> 'a1 cdeque

val buffer_inject_obligations_obligation_2 : green_hue

val buffer_inject_obligations_obligation_3 : yellow_hue

val buffer_inject_obligations_obligation_5 : green_hue -> green_hue

val buffer_inject_obligations_obligation_6 : yellow_hue -> yellow_hue

val buffer_inject :
  nat -> nat -> color -> 'a1 buffer -> 'a1 prodN -> 'a1 cdeque

val buffer_pop :
  nat -> nat -> color -> 'a1 buffer -> ('a1 prodN, 'a1 any_buffer) prod option

val buffer_eject :
  nat -> nat -> color -> 'a1 buffer -> ('a1 any_buffer, 'a1 prodN) prod option

val prefix_rot :
  nat -> nat -> color -> 'a1 prodN -> 'a1 buffer -> ('a1 buffer, 'a1 prodN)
  prod

val suffix_rot :
  nat -> nat -> color -> 'a1 buffer -> 'a1 prodN -> ('a1 prodN, 'a1 buffer)
  prod

val prefix23 :
  nat -> green_hue -> yellow_hue -> 'a1 prodN option -> 'a1 prodN -> 'a1
  buffer

val suffix23 :
  nat -> green_hue -> yellow_hue -> 'a1 prodN -> 'a1 prodN option -> 'a1
  buffer

val suffix12 : nat -> 'a1 prodN -> 'a1 prodN option -> 'a1 buffer

val prefix_decompose : nat -> nat -> color -> 'a1 buffer -> 'a1 decompose

val suffix_decompose : nat -> nat -> color -> 'a1 buffer -> 'a1 decompose

val buffer_unsandwich_obligations_obligation_5 : green_hue

val buffer_unsandwich_obligations_obligation_6 : yellow_hue

val buffer_unsandwich_obligations_obligation_8 : green_hue

val buffer_unsandwich_obligations_obligation_9 : yellow_hue

val buffer_unsandwich : nat -> nat -> color -> 'a1 buffer -> 'a1 sandwich

val buffer_halve_obligations_obligation_5 : green_hue

val buffer_halve_obligations_obligation_6 : yellow_hue

val buffer_halve_obligations_obligation_8 : green_hue

val buffer_halve_obligations_obligation_9 : yellow_hue

val buffer_halve :
  nat -> nat -> color -> 'a1 buffer -> ('a1 prodN option, 'a1 any_buffer) prod

val buffer_translate : nat -> nat -> nat -> color -> 'a1 buffer -> 'a1 buffer

val green_prefix_concat :
  nat -> nat -> nat -> color -> 'a1 buffer -> 'a1 buffer -> ('a1 buffer, 'a1
  yellow_buffer) prod

val green_suffix_concat :
  nat -> nat -> nat -> color -> 'a1 buffer -> 'a1 buffer -> ('a1
  yellow_buffer, 'a1 buffer) prod

val yellow_prefix_concat :
  nat -> nat -> nat -> color -> 'a1 buffer -> 'a1 yellow_buffer -> ('a1
  buffer, 'a1 any_buffer) prod

val yellow_suffix_concat :
  nat -> nat -> nat -> color -> 'a1 yellow_buffer -> 'a1 buffer -> ('a1
  any_buffer, 'a1 buffer) prod

val cdeque_of_opt3_obligations_obligation_2 : green_hue

val cdeque_of_opt3_obligations_obligation_3 : yellow_hue

val cdeque_of_opt3_obligations_obligation_5 : green_hue

val cdeque_of_opt3_obligations_obligation_6 : yellow_hue

val cdeque_of_opt3_obligations_obligation_9 : green_hue

val cdeque_of_opt3_obligations_obligation_10 : yellow_hue

val cdeque_of_opt3_obligations_obligation_12 : green_hue

val cdeque_of_opt3_obligations_obligation_13 : yellow_hue

val cdeque_of_opt3 :
  nat -> 'a1 prodN option -> 'a1 prodN option -> 'a1 prodN option -> 'a1
  cdeque

val cdeque_translate : nat -> nat -> nat -> color -> 'a1 cdeque -> 'a1 cdeque

val make_small :
  nat -> nat -> nat -> nat -> color -> color -> color -> 'a1 buffer -> 'a1
  buffer -> 'a1 buffer -> 'a1 cdeque

val green_of_red : nat -> nat -> 'a1 cdeque -> 'a1 cdeque

val ensure_green :
  nat -> nat -> green_hue -> red_hue -> 'a1 cdeque -> 'a1 cdeque

val make_yellow :
  nat -> nat -> nat -> nat -> nat -> green_hue -> yellow_hue -> yellow_hue ->
  green_hue -> yellow_hue -> green_hue -> red_hue -> 'a1 buffer -> 'a1 packet
  -> 'a1 buffer -> 'a1 cdeque -> 'a1 deque

val make_red :
  nat -> nat -> nat -> nat -> nat -> color -> yellow_hue -> color -> 'a1
  buffer -> 'a1 packet -> 'a1 buffer -> 'a1 cdeque -> 'a1 deque

val deque_translate : nat -> nat -> 'a1 deque -> 'a1 deque

val push : nat -> 'a1 -> 'a1 deque -> 'a1 deque

val inject : nat -> 'a1 deque -> 'a1 -> 'a1 deque

val unsafe_pop : nat -> 'a1 deque -> ('a1, 'a1 deque) prod option

val pop_obligations_obligation_2 : nat -> 'a1 deque -> ('a1, 'a1 deque) prod

val pop : nat -> 'a1 deque -> ('a1, 'a1 deque) prod

val unsafe_eject : nat -> 'a1 deque -> ('a1 deque, 'a1) prod option

val eject_obligations_obligation_2 : nat -> 'a1 deque -> ('a1 deque, 'a1) prod

val eject : nat -> 'a1 deque -> ('a1 deque, 'a1) prod
