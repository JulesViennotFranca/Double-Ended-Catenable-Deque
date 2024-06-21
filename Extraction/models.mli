open Classes
open Datatypes
(* open List *)
(* open Nat *)
open Buffer
open Types

type __ = Obj.t

val path_seq : nat -> kind -> color -> 'a1 path -> 'a1 list

val ne_cdeque_seq : nat -> color -> 'a1 non_empty_cdeque -> 'a1 list

type 'a ne_cdeque_seq_graph =
| Coq_ne_cdeque_seq_graph_equation_1 of nat * green_hue * red_hue * 'a path
| Coq_ne_cdeque_seq_graph_equation_2 of nat * 'a path * 'a path
| Coq_ne_cdeque_seq_graph_equation_3 of nat * color * color * 'a path
   * 'a path

val ne_cdeque_seq_graph_rect :
  (__ -> nat -> green_hue -> red_hue -> __ path -> 'a1) -> (__ -> nat -> __
  path -> __ path -> 'a1) -> (__ -> nat -> color -> color -> __ path -> __
  path -> 'a1) -> nat -> color -> 'a2 non_empty_cdeque -> 'a2 list -> 'a2
  ne_cdeque_seq_graph -> 'a1

val ne_cdeque_seq_graph_correct :
  nat -> color -> 'a1 non_empty_cdeque -> 'a1 ne_cdeque_seq_graph

val ne_cdeque_seq_elim :
  (__ -> nat -> green_hue -> red_hue -> __ path -> 'a1) -> (__ -> nat -> __
  path -> __ path -> 'a1) -> (__ -> nat -> color -> color -> __ path -> __
  path -> 'a1) -> nat -> color -> 'a2 non_empty_cdeque -> 'a1

val coq_FunctionalElimination_ne_cdeque_seq :
  (__ -> nat -> green_hue -> red_hue -> __ path -> __) -> (__ -> nat -> __
  path -> __ path -> __) -> (__ -> nat -> color -> color -> __ path -> __
  path -> __) -> nat -> color -> __ non_empty_cdeque -> __

val coq_FunctionalInduction_ne_cdeque_seq :
  (__ -> nat -> color -> __ non_empty_cdeque -> __ list)
  coq_FunctionalInduction

val cdeque_seq : nat -> color -> 'a1 cdeque -> 'a1 list

type 'a cdeque_seq_graph =
| Coq_cdeque_seq_graph_equation_1 of nat
| Coq_cdeque_seq_graph_equation_2 of nat * green_hue * red_hue
   * 'a non_empty_cdeque

val cdeque_seq_graph_rect :
  (__ -> nat -> 'a1) -> (__ -> nat -> green_hue -> red_hue -> __
  non_empty_cdeque -> 'a1) -> nat -> color -> 'a2 cdeque -> 'a2 list -> 'a2
  cdeque_seq_graph -> 'a1

val cdeque_seq_graph_correct :
  nat -> color -> 'a1 cdeque -> 'a1 cdeque_seq_graph

val cdeque_seq_elim :
  (__ -> nat -> 'a1) -> (__ -> nat -> green_hue -> red_hue -> __
  non_empty_cdeque -> 'a1) -> nat -> color -> 'a2 cdeque -> 'a1

val coq_FunctionalElimination_cdeque_seq :
  (__ -> nat -> __) -> (__ -> nat -> green_hue -> red_hue -> __
  non_empty_cdeque -> __) -> nat -> color -> __ cdeque -> __

val coq_FunctionalInduction_cdeque_seq :
  (__ -> nat -> color -> __ cdeque -> __ list) coq_FunctionalInduction

val stored_triple_seq : nat -> 'a1 stored_triple -> 'a1 list

val buffer_seq : nat -> nat -> 'a1 stored_triple t -> 'a1 list

type 'a buffer_seq_graph =
| Coq_buffer_seq_graph_equation_1 of nat * nat * 'a stored_triple t

val buffer_seq_graph_rect :
  (__ -> nat -> nat -> __ stored_triple t -> 'a1) -> nat -> nat -> 'a2
  stored_triple t -> 'a2 list -> 'a2 buffer_seq_graph -> 'a1

val buffer_seq_graph_correct :
  nat -> nat -> 'a1 stored_triple t -> 'a1 buffer_seq_graph

val buffer_seq_elim :
  (__ -> nat -> nat -> __ stored_triple t -> 'a1) -> nat -> nat -> 'a2
  stored_triple t -> 'a1

val coq_FunctionalElimination_buffer_seq :
  (__ -> nat -> nat -> __ stored_triple t -> __) -> nat -> nat -> __
  stored_triple t -> __

val coq_FunctionalInduction_buffer_seq :
  (__ -> nat -> nat -> __ stored_triple t -> __ list) coq_FunctionalInduction

val path_buffer_seq : nat -> nat -> 'a1 stored_triple t -> 'a1 list

val triple_front_seq :
  nat -> nat -> bool -> kind -> kind -> color -> 'a1 triple -> 'a1 list

val packet_front_seq :
  nat -> nat -> preferred_child -> kind -> 'a1 packet -> 'a1 list

type 'a packet_front_seq_graph =
| Coq_packet_front_seq_graph_equation_1 of nat * nat * preferred_child * 
   kind * bool * yellow_hue * orange_hue * 'a triple
| Coq_packet_front_seq_graph_equation_2 of nat * nat * kind * bool
   * yellow_hue * orange_hue * color * 'a triple * 'a path
| Coq_packet_front_seq_graph_equation_3 of nat * nat * kind * bool
   * yellow_hue * orange_hue * 'a path * 'a triple

val packet_front_seq_graph_rect :
  (__ -> nat -> nat -> preferred_child -> kind -> bool -> yellow_hue ->
  orange_hue -> __ triple -> 'a1) -> (__ -> nat -> nat -> kind -> bool ->
  yellow_hue -> orange_hue -> color -> __ triple -> __ path -> 'a1) -> (__ ->
  nat -> nat -> kind -> bool -> yellow_hue -> orange_hue -> __ path -> __
  triple -> 'a1) -> nat -> nat -> preferred_child -> kind -> 'a2 packet ->
  'a2 list -> 'a2 packet_front_seq_graph -> 'a1

val packet_front_seq_graph_correct :
  nat -> nat -> preferred_child -> kind -> 'a1 packet -> 'a1
  packet_front_seq_graph

val packet_front_seq_elim :
  (__ -> nat -> nat -> preferred_child -> kind -> bool -> yellow_hue ->
  orange_hue -> __ triple -> 'a1) -> (__ -> nat -> nat -> kind -> bool ->
  yellow_hue -> orange_hue -> color -> __ triple -> __ path -> 'a1) -> (__ ->
  nat -> nat -> kind -> bool -> yellow_hue -> orange_hue -> __ path -> __
  triple -> 'a1) -> nat -> nat -> preferred_child -> kind -> 'a2 packet -> 'a1

val coq_FunctionalElimination_packet_front_seq :
  (__ -> nat -> nat -> preferred_child -> kind -> bool -> yellow_hue ->
  orange_hue -> __ triple -> __) -> (__ -> nat -> nat -> kind -> bool ->
  yellow_hue -> orange_hue -> color -> __ triple -> __ path -> __) -> (__ ->
  nat -> nat -> kind -> bool -> yellow_hue -> orange_hue -> __ path -> __
  triple -> __) -> nat -> nat -> preferred_child -> kind -> __ packet -> __

val coq_FunctionalInduction_packet_front_seq :
  (__ -> nat -> nat -> preferred_child -> kind -> __ packet -> __ list)
  coq_FunctionalInduction

val triple_rear_seq :
  nat -> nat -> bool -> kind -> kind -> color -> 'a1 triple -> 'a1 list

val packet_rear_seq :
  nat -> nat -> preferred_child -> kind -> 'a1 packet -> 'a1 list

type 'a packet_rear_seq_graph =
| Coq_packet_rear_seq_graph_equation_1 of nat * nat * preferred_child * 
   kind * bool * yellow_hue * orange_hue * 'a triple
| Coq_packet_rear_seq_graph_equation_2 of nat * nat * kind * bool
   * yellow_hue * orange_hue * color * 'a triple * 'a path
| Coq_packet_rear_seq_graph_equation_3 of nat * nat * kind * bool
   * yellow_hue * orange_hue * 'a path * 'a triple

val packet_rear_seq_graph_rect :
  (__ -> nat -> nat -> preferred_child -> kind -> bool -> yellow_hue ->
  orange_hue -> __ triple -> 'a1) -> (__ -> nat -> nat -> kind -> bool ->
  yellow_hue -> orange_hue -> color -> __ triple -> __ path -> 'a1) -> (__ ->
  nat -> nat -> kind -> bool -> yellow_hue -> orange_hue -> __ path -> __
  triple -> 'a1) -> nat -> nat -> preferred_child -> kind -> 'a2 packet ->
  'a2 list -> 'a2 packet_rear_seq_graph -> 'a1

val packet_rear_seq_graph_correct :
  nat -> nat -> preferred_child -> kind -> 'a1 packet -> 'a1
  packet_rear_seq_graph

val packet_rear_seq_elim :
  (__ -> nat -> nat -> preferred_child -> kind -> bool -> yellow_hue ->
  orange_hue -> __ triple -> 'a1) -> (__ -> nat -> nat -> kind -> bool ->
  yellow_hue -> orange_hue -> color -> __ triple -> __ path -> 'a1) -> (__ ->
  nat -> nat -> kind -> bool -> yellow_hue -> orange_hue -> __ path -> __
  triple -> 'a1) -> nat -> nat -> preferred_child -> kind -> 'a2 packet -> 'a1

val coq_FunctionalElimination_packet_rear_seq :
  (__ -> nat -> nat -> preferred_child -> kind -> bool -> yellow_hue ->
  orange_hue -> __ triple -> __) -> (__ -> nat -> nat -> kind -> bool ->
  yellow_hue -> orange_hue -> color -> __ triple -> __ path -> __) -> (__ ->
  nat -> nat -> kind -> bool -> yellow_hue -> orange_hue -> __ path -> __
  triple -> __) -> nat -> nat -> preferred_child -> kind -> __ packet -> __

val coq_FunctionalInduction_packet_rear_seq :
  (__ -> nat -> nat -> preferred_child -> kind -> __ packet -> __ list)
  coq_FunctionalInduction

val triple_seq :
  nat -> nat -> bool -> kind -> kind -> color -> 'a1 triple -> 'a1 list

type 'a triple_seq_graph =
| Coq_triple_seq_graph_equation_1 of nat * nat * bool * kind * kind * 
   color * 'a triple

val triple_seq_graph_rect :
  (__ -> nat -> nat -> bool -> kind -> kind -> color -> __ triple -> 'a1) ->
  nat -> nat -> bool -> kind -> kind -> color -> 'a2 triple -> 'a2 list ->
  'a2 triple_seq_graph -> 'a1

val triple_seq_graph_correct :
  nat -> nat -> bool -> kind -> kind -> color -> 'a1 triple -> 'a1
  triple_seq_graph

val triple_seq_elim :
  (__ -> nat -> nat -> bool -> kind -> kind -> color -> __ triple -> 'a1) ->
  nat -> nat -> bool -> kind -> kind -> color -> 'a2 triple -> 'a1

val coq_FunctionalElimination_triple_seq :
  (__ -> nat -> nat -> bool -> kind -> kind -> color -> __ triple -> __) ->
  nat -> nat -> bool -> kind -> kind -> color -> __ triple -> __

val coq_FunctionalInduction_triple_seq :
  (__ -> nat -> nat -> bool -> kind -> kind -> color -> __ triple -> __ list)
  coq_FunctionalInduction

val pref_left_seq : nat -> 'a1 pref_left -> 'a1 list

type 'a pref_left_seq_graph =
| Coq_pref_left_seq_graph_equation_1 of nat * nat * kind * green_hue
   * red_hue * 'a packet * 'a triple

val pref_left_seq_graph_rect :
  (__ -> nat -> nat -> kind -> green_hue -> red_hue -> __ packet -> __ triple
  -> 'a1) -> nat -> 'a2 pref_left -> 'a2 list -> 'a2 pref_left_seq_graph ->
  'a1

val pref_left_seq_graph_correct :
  nat -> 'a1 pref_left -> 'a1 pref_left_seq_graph

val pref_left_seq_elim :
  (__ -> nat -> nat -> kind -> green_hue -> red_hue -> __ packet -> __ triple
  -> 'a1) -> nat -> 'a2 pref_left -> 'a1

val coq_FunctionalElimination_pref_left_seq :
  (__ -> nat -> nat -> kind -> green_hue -> red_hue -> __ packet -> __ triple
  -> __) -> nat -> __ pref_left -> __

val coq_FunctionalInduction_pref_left_seq :
  (__ -> nat -> __ pref_left -> __ list) coq_FunctionalInduction

val pref_right_seq : nat -> 'a1 pref_right -> 'a1 list

type 'a pref_right_seq_graph =
| Coq_pref_right_seq_graph_equation_1 of nat * nat * kind * green_hue
   * red_hue * 'a packet * 'a triple

val pref_right_seq_graph_rect :
  (__ -> nat -> nat -> kind -> green_hue -> red_hue -> __ packet -> __ triple
  -> 'a1) -> nat -> 'a2 pref_right -> 'a2 list -> 'a2 pref_right_seq_graph ->
  'a1

val pref_right_seq_graph_correct :
  nat -> 'a1 pref_right -> 'a1 pref_right_seq_graph

val pref_right_seq_elim :
  (__ -> nat -> nat -> kind -> green_hue -> red_hue -> __ packet -> __ triple
  -> 'a1) -> nat -> 'a2 pref_right -> 'a1

val coq_FunctionalElimination_pref_right_seq :
  (__ -> nat -> nat -> kind -> green_hue -> red_hue -> __ packet -> __ triple
  -> __) -> nat -> __ pref_right -> __

val coq_FunctionalInduction_pref_right_seq :
  (__ -> nat -> __ pref_right -> __ list) coq_FunctionalInduction

val buffer_12_seq : nat -> 'a1 buffer_12 -> 'a1 list

type 'a buffer_12_seq_graph =
| Coq_buffer_12_seq_graph_equation_1 of nat * 'a stored_triple
   * 'a stored_triple vector

val buffer_12_seq_graph_rect :
  (__ -> nat -> __ stored_triple -> __ stored_triple vector -> 'a1) -> nat ->
  'a2 buffer_12 -> 'a2 list -> 'a2 buffer_12_seq_graph -> 'a1

val buffer_12_seq_graph_correct :
  nat -> 'a1 buffer_12 -> 'a1 buffer_12_seq_graph

val buffer_12_seq_elim :
  (__ -> nat -> __ stored_triple -> __ stored_triple vector -> 'a1) -> nat ->
  'a2 buffer_12 -> 'a1

val coq_FunctionalElimination_buffer_12_seq :
  (__ -> nat -> __ stored_triple -> __ stored_triple vector -> __) -> nat ->
  __ buffer_12 -> __

val coq_FunctionalInduction_buffer_12_seq :
  (__ -> nat -> __ buffer_12 -> __ list) coq_FunctionalInduction

val path_attempt_seq : nat -> kind -> color -> 'a1 path_attempt -> 'a1 list

type 'a path_attempt_seq_graph =
| Coq_path_attempt_seq_graph_equation_1 of nat * kind * color
   * 'a stored_triple vector
| Coq_path_attempt_seq_graph_equation_2 of nat * kind * color * 'a path
| Coq_path_attempt_seq_graph_equation_3 of nat * kind * color * 'a path

val path_attempt_seq_graph_rect :
  (__ -> nat -> kind -> color -> __ stored_triple vector -> 'a1) -> (__ ->
  nat -> kind -> color -> __ path -> 'a1) -> (__ -> nat -> kind -> color ->
  __ path -> 'a1) -> nat -> kind -> color -> 'a2 path_attempt -> 'a2 list ->
  'a2 path_attempt_seq_graph -> 'a1

val path_attempt_seq_graph_correct :
  nat -> kind -> color -> 'a1 path_attempt -> 'a1 path_attempt_seq_graph

val path_attempt_seq_elim :
  (__ -> nat -> kind -> color -> __ stored_triple vector -> 'a1) -> (__ ->
  nat -> kind -> color -> __ path -> 'a1) -> (__ -> nat -> kind -> color ->
  __ path -> 'a1) -> nat -> kind -> color -> 'a2 path_attempt -> 'a1

val coq_FunctionalElimination_path_attempt_seq :
  (__ -> nat -> kind -> color -> __ stored_triple vector -> __) -> (__ -> nat
  -> kind -> color -> __ path -> __) -> (__ -> nat -> kind -> color -> __
  path -> __) -> nat -> kind -> color -> __ path_attempt -> __

val coq_FunctionalInduction_path_attempt_seq :
  (__ -> nat -> kind -> color -> __ path_attempt -> __ list)
  coq_FunctionalInduction

val path_uncolored_seq : nat -> kind -> 'a1 path_uncolored -> 'a1 list

type 'a path_uncolored_seq_graph =
| Coq_path_uncolored_seq_graph_equation_1 of nat * kind * 'a stored_triple
   * 'a stored_triple * 'a stored_triple * 'a stored_triple
   * 'a stored_triple * 'a stored_triple
| Coq_path_uncolored_seq_graph_equation_2 of nat * kind * color * 'a path

val path_uncolored_seq_graph_rect :
  (__ -> nat -> kind -> __ stored_triple -> __ stored_triple -> __
  stored_triple -> __ stored_triple -> __ stored_triple -> __ stored_triple
  -> 'a1) -> (__ -> nat -> kind -> color -> __ path -> 'a1) -> nat -> kind ->
  'a2 path_uncolored -> 'a2 list -> 'a2 path_uncolored_seq_graph -> 'a1

val path_uncolored_seq_graph_correct :
  nat -> kind -> 'a1 path_uncolored -> 'a1 path_uncolored_seq_graph

val path_uncolored_seq_elim :
  (__ -> nat -> kind -> __ stored_triple -> __ stored_triple -> __
  stored_triple -> __ stored_triple -> __ stored_triple -> __ stored_triple
  -> 'a1) -> (__ -> nat -> kind -> color -> __ path -> 'a1) -> nat -> kind ->
  'a2 path_uncolored -> 'a1

val coq_FunctionalElimination_path_uncolored_seq :
  (__ -> nat -> kind -> __ stored_triple -> __ stored_triple -> __
  stored_triple -> __ stored_triple -> __ stored_triple -> __ stored_triple
  -> __) -> (__ -> nat -> kind -> color -> __ path -> __) -> nat -> kind ->
  __ path_uncolored -> __

val coq_FunctionalInduction_path_uncolored_seq :
  (__ -> nat -> kind -> __ path_uncolored -> __ list) coq_FunctionalInduction

val sdeque_seq : nat -> 'a1 sdeque -> 'a1 list

type 'a sdeque_seq_graph =
| Coq_sdeque_seq_graph_equation_1 of nat * color * 'a cdeque

val sdeque_seq_graph_rect :
  (__ -> nat -> color -> __ cdeque -> 'a1) -> nat -> 'a2 sdeque -> 'a2 list
  -> 'a2 sdeque_seq_graph -> 'a1

val sdeque_seq_graph_correct : nat -> 'a1 sdeque -> 'a1 sdeque_seq_graph

val sdeque_seq_elim :
  (__ -> nat -> color -> __ cdeque -> 'a1) -> nat -> 'a2 sdeque -> 'a1

val coq_FunctionalElimination_sdeque_seq :
  (__ -> nat -> color -> __ cdeque -> __) -> nat -> __ sdeque -> __

val coq_FunctionalInduction_sdeque_seq :
  (__ -> nat -> __ sdeque -> __ list) coq_FunctionalInduction

val unstored_front_seq : nat -> 'a1 unstored -> 'a1 list

type 'a unstored_front_seq_graph =
| Coq_unstored_front_seq_graph_equation_1 of nat * nat * 'a prefix * 'a sdeque

val unstored_front_seq_graph_rect :
  (__ -> nat -> nat -> __ prefix -> __ sdeque -> 'a1) -> nat -> 'a2 unstored
  -> 'a2 list -> 'a2 unstored_front_seq_graph -> 'a1

val unstored_front_seq_graph_correct :
  nat -> 'a1 unstored -> 'a1 unstored_front_seq_graph

val unstored_front_seq_elim :
  (__ -> nat -> nat -> __ prefix -> __ sdeque -> 'a1) -> nat -> 'a2 unstored
  -> 'a1

val coq_FunctionalElimination_unstored_front_seq :
  (__ -> nat -> nat -> __ prefix -> __ sdeque -> __) -> nat -> __ unstored ->
  __

val coq_FunctionalInduction_unstored_front_seq :
  (__ -> nat -> __ unstored -> __ list) coq_FunctionalInduction

val unstored_rear_seq : nat -> 'a1 unstored -> 'a1 list

type 'a unstored_rear_seq_graph =
| Coq_unstored_rear_seq_graph_equation_1 of nat * nat * 'a prefix * 'a sdeque

val unstored_rear_seq_graph_rect :
  (__ -> nat -> nat -> __ prefix -> __ sdeque -> 'a1) -> nat -> 'a2 unstored
  -> 'a2 list -> 'a2 unstored_rear_seq_graph -> 'a1

val unstored_rear_seq_graph_correct :
  nat -> 'a1 unstored -> 'a1 unstored_rear_seq_graph

val unstored_rear_seq_elim :
  (__ -> nat -> nat -> __ prefix -> __ sdeque -> 'a1) -> nat -> 'a2 unstored
  -> 'a1

val coq_FunctionalElimination_unstored_rear_seq :
  (__ -> nat -> nat -> __ prefix -> __ sdeque -> __) -> nat -> __ unstored ->
  __

val coq_FunctionalInduction_unstored_rear_seq :
  (__ -> nat -> __ unstored -> __ list) coq_FunctionalInduction

val sandwich_seq : nat -> 'a1 sandwich -> 'a1 list

type 'a sandwich_seq_graph =
| Coq_sandwich_seq_graph_equation_1 of nat * 'a stored_triple
| Coq_sandwich_seq_graph_equation_2 of nat * 'a stored_triple * 'a sdeque
   * 'a stored_triple

val sandwich_seq_graph_rect :
  (__ -> nat -> __ stored_triple -> 'a1) -> (__ -> nat -> __ stored_triple ->
  __ sdeque -> __ stored_triple -> 'a1) -> nat -> 'a2 sandwich -> 'a2 list ->
  'a2 sandwich_seq_graph -> 'a1

val sandwich_seq_graph_correct : nat -> 'a1 sandwich -> 'a1 sandwich_seq_graph

val sandwich_seq_elim :
  (__ -> nat -> __ stored_triple -> 'a1) -> (__ -> nat -> __ stored_triple ->
  __ sdeque -> __ stored_triple -> 'a1) -> nat -> 'a2 sandwich -> 'a1

val coq_FunctionalElimination_sandwich_seq :
  (__ -> nat -> __ stored_triple -> __) -> (__ -> nat -> __ stored_triple ->
  __ sdeque -> __ stored_triple -> __) -> nat -> __ sandwich -> __

val coq_FunctionalInduction_sandwich_seq :
  (__ -> nat -> __ sandwich -> __ list) coq_FunctionalInduction

val unstored_sandwich_seq : nat -> 'a1 unstored_sandwich -> 'a1 list

type 'a unstored_sandwich_seq_graph =
| Coq_unstored_sandwich_seq_graph_equation_1 of nat * nat * 'a prefix
| Coq_unstored_sandwich_seq_graph_equation_2 of nat * nat * nat * 'a prefix
   * 'a sdeque * 'a suffix

val unstored_sandwich_seq_graph_rect :
  (__ -> nat -> nat -> __ prefix -> 'a1) -> (__ -> nat -> nat -> nat -> __
  prefix -> __ sdeque -> __ suffix -> 'a1) -> nat -> 'a2 unstored_sandwich ->
  'a2 list -> 'a2 unstored_sandwich_seq_graph -> 'a1

val unstored_sandwich_seq_graph_correct :
  nat -> 'a1 unstored_sandwich -> 'a1 unstored_sandwich_seq_graph

val unstored_sandwich_seq_elim :
  (__ -> nat -> nat -> __ prefix -> 'a1) -> (__ -> nat -> nat -> nat -> __
  prefix -> __ sdeque -> __ suffix -> 'a1) -> nat -> 'a2 unstored_sandwich ->
  'a1

val coq_FunctionalElimination_unstored_sandwich_seq :
  (__ -> nat -> nat -> __ prefix -> __) -> (__ -> nat -> nat -> nat -> __
  prefix -> __ sdeque -> __ suffix -> __) -> nat -> __ unstored_sandwich -> __

val coq_FunctionalInduction_unstored_sandwich_seq :
  (__ -> nat -> __ unstored_sandwich -> __ list) coq_FunctionalInduction

val deque_seq : 'a1 deque -> 'a1 list

type 'a deque_seq_graph =
  'a cdeque
  (* singleton inductive, whose constructor was deque_seq_graph_equation_1 *)

val deque_seq_graph_rect :
  (__ -> __ cdeque -> 'a1) -> 'a2 deque -> 'a2 list -> 'a2 deque_seq_graph ->
  'a1

val deque_seq_graph_correct : 'a1 deque -> 'a1 deque_seq_graph

val deque_seq_elim : (__ -> __ cdeque -> 'a1) -> 'a2 deque -> 'a1

val coq_FunctionalElimination_deque_seq :
  (__ -> __ cdeque -> __) -> __ deque -> __

val coq_FunctionalInduction_deque_seq :
  (__ -> __ deque -> __ list) coq_FunctionalInduction
