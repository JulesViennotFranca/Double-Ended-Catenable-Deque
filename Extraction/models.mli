open Classes
open Datatypes
open Buffer
open Types

type __ = Obj.t

val stored_triple_seq : nat -> 'a1 stored_triple -> 'a1 list

val strd_buffer_seq : nat -> nat -> 'a1 stored_triple t -> 'a1 list

val strd_storage_left_seq :
  nat -> kind -> ending -> color -> 'a1 storage -> 'a1 list

val strd_storage_right_seq :
  nat -> kind -> ending -> color -> 'a1 storage -> 'a1 list

val chain_seq :
  nat -> kind -> kind -> ending -> color -> color -> 'a1 chain -> 'a1 list

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

val prefix_seq : nat -> nat -> 'a1 prefix -> 'a1 list

val suffix_seq : nat -> nat -> 'a1 suffix -> 'a1 list

val green_buffer_seq : nat -> 'a1 green_buffer -> 'a1 list

type 'a green_buffer_seq_graph =
| Coq_green_buffer_seq_graph_equation_1 of nat * nat * 'a stored_triple t

val green_buffer_seq_graph_rect :
  (__ -> nat -> nat -> __ stored_triple t -> 'a1) -> nat -> 'a2 green_buffer
  -> 'a2 list -> 'a2 green_buffer_seq_graph -> 'a1

val green_buffer_seq_graph_correct :
  nat -> 'a1 green_buffer -> 'a1 green_buffer_seq_graph

val green_buffer_seq_elim :
  (__ -> nat -> nat -> __ stored_triple t -> 'a1) -> nat -> 'a2 green_buffer
  -> 'a1

val coq_FunctionalElimination_green_buffer_seq :
  (__ -> nat -> nat -> __ stored_triple t -> __) -> nat -> __ green_buffer ->
  __

val coq_FunctionalInduction_green_buffer_seq :
  (__ -> nat -> __ green_buffer -> __ list) coq_FunctionalInduction

val stored_buffer_seq : nat -> 'a1 stored_buffer -> 'a1 list

type 'a stored_buffer_seq_graph =
| Coq_stored_buffer_seq_graph_equation_1 of nat * nat * 'a stored_triple t

val stored_buffer_seq_graph_rect :
  (__ -> nat -> nat -> __ stored_triple t -> 'a1) -> nat -> 'a2 stored_buffer
  -> 'a2 list -> 'a2 stored_buffer_seq_graph -> 'a1

val stored_buffer_seq_graph_correct :
  nat -> 'a1 stored_buffer -> 'a1 stored_buffer_seq_graph

val stored_buffer_seq_elim :
  (__ -> nat -> nat -> __ stored_triple t -> 'a1) -> nat -> 'a2 stored_buffer
  -> 'a1

val coq_FunctionalElimination_stored_buffer_seq :
  (__ -> nat -> nat -> __ stored_triple t -> __) -> nat -> __ stored_buffer
  -> __

val coq_FunctionalInduction_stored_buffer_seq :
  (__ -> nat -> __ stored_buffer -> __ list) coq_FunctionalInduction

val storage_left_seq :
  nat -> kind -> ending -> color -> 'a1 storage -> 'a1 list

type 'a storage_left_seq_graph =
| Coq_storage_left_seq_graph_equation_1 of nat * nat
   * 'a stored_triple prefix'
| Coq_storage_left_seq_graph_equation_2 of nat * nat
   * 'a stored_triple prefix' * 'a stored_triple suffix'
| Coq_storage_left_seq_graph_equation_3 of nat * nat
   * 'a stored_triple prefix' * 'a stored_triple suffix'
| Coq_storage_left_seq_graph_equation_4 of nat * color * nat * nat *
   coloring * 'a stored_triple prefix' * 'a stored_triple suffix'
| Coq_storage_left_seq_graph_equation_5 of nat * color * nat * nat *
   coloring * 'a stored_triple prefix' * 'a stored_triple suffix'
| Coq_storage_left_seq_graph_equation_6 of nat * color * nat * nat *
   coloring * 'a stored_triple prefix' * 'a stored_triple suffix'

val storage_left_seq_graph_rect :
  (__ -> nat -> nat -> __ stored_triple prefix' -> 'a1) -> (__ -> nat -> nat
  -> __ stored_triple prefix' -> __ stored_triple suffix' -> 'a1) -> (__ ->
  nat -> nat -> __ stored_triple prefix' -> __ stored_triple suffix' -> 'a1)
  -> (__ -> nat -> color -> nat -> nat -> coloring -> __ stored_triple
  prefix' -> __ stored_triple suffix' -> 'a1) -> (__ -> nat -> color -> nat
  -> nat -> coloring -> __ stored_triple prefix' -> __ stored_triple suffix'
  -> 'a1) -> (__ -> nat -> color -> nat -> nat -> coloring -> __
  stored_triple prefix' -> __ stored_triple suffix' -> 'a1) -> nat -> kind ->
  ending -> color -> 'a2 storage -> 'a2 list -> 'a2 storage_left_seq_graph ->
  'a1

val storage_left_seq_graph_correct :
  nat -> kind -> ending -> color -> 'a1 storage -> 'a1 storage_left_seq_graph

val storage_left_seq_elim :
  (__ -> nat -> nat -> __ stored_triple prefix' -> 'a1) -> (__ -> nat -> nat
  -> __ stored_triple prefix' -> __ stored_triple suffix' -> 'a1) -> (__ ->
  nat -> nat -> __ stored_triple prefix' -> __ stored_triple suffix' -> 'a1)
  -> (__ -> nat -> color -> nat -> nat -> coloring -> __ stored_triple
  prefix' -> __ stored_triple suffix' -> 'a1) -> (__ -> nat -> color -> nat
  -> nat -> coloring -> __ stored_triple prefix' -> __ stored_triple suffix'
  -> 'a1) -> (__ -> nat -> color -> nat -> nat -> coloring -> __
  stored_triple prefix' -> __ stored_triple suffix' -> 'a1) -> nat -> kind ->
  ending -> color -> 'a2 storage -> 'a1

val coq_FunctionalElimination_storage_left_seq :
  (__ -> nat -> nat -> __ stored_triple prefix' -> __) -> (__ -> nat -> nat
  -> __ stored_triple prefix' -> __ stored_triple suffix' -> __) -> (__ ->
  nat -> nat -> __ stored_triple prefix' -> __ stored_triple suffix' -> __)
  -> (__ -> nat -> color -> nat -> nat -> coloring -> __ stored_triple
  prefix' -> __ stored_triple suffix' -> __) -> (__ -> nat -> color -> nat ->
  nat -> coloring -> __ stored_triple prefix' -> __ stored_triple suffix' ->
  __) -> (__ -> nat -> color -> nat -> nat -> coloring -> __ stored_triple
  prefix' -> __ stored_triple suffix' -> __) -> nat -> kind -> ending ->
  color -> __ storage -> __

val coq_FunctionalInduction_storage_left_seq :
  (__ -> nat -> kind -> ending -> color -> __ storage -> __ list)
  coq_FunctionalInduction

val storage_right_seq :
  nat -> kind -> ending -> color -> 'a1 storage -> 'a1 list

type 'a storage_right_seq_graph =
| Coq_storage_right_seq_graph_equation_1 of nat * nat
   * 'a stored_triple prefix'
| Coq_storage_right_seq_graph_equation_2 of nat * nat
   * 'a stored_triple prefix' * 'a stored_triple suffix'
| Coq_storage_right_seq_graph_equation_3 of nat * nat
   * 'a stored_triple prefix' * 'a stored_triple suffix'
| Coq_storage_right_seq_graph_equation_4 of nat * color * nat * nat
   * coloring * 'a stored_triple prefix' * 'a stored_triple suffix'
| Coq_storage_right_seq_graph_equation_5 of nat * color * nat * nat
   * coloring * 'a stored_triple prefix' * 'a stored_triple suffix'
| Coq_storage_right_seq_graph_equation_6 of nat * color * nat * nat
   * coloring * 'a stored_triple prefix' * 'a stored_triple suffix'

val storage_right_seq_graph_rect :
  (__ -> nat -> nat -> __ stored_triple prefix' -> 'a1) -> (__ -> nat -> nat
  -> __ stored_triple prefix' -> __ stored_triple suffix' -> 'a1) -> (__ ->
  nat -> nat -> __ stored_triple prefix' -> __ stored_triple suffix' -> 'a1)
  -> (__ -> nat -> color -> nat -> nat -> coloring -> __ stored_triple
  prefix' -> __ stored_triple suffix' -> 'a1) -> (__ -> nat -> color -> nat
  -> nat -> coloring -> __ stored_triple prefix' -> __ stored_triple suffix'
  -> 'a1) -> (__ -> nat -> color -> nat -> nat -> coloring -> __
  stored_triple prefix' -> __ stored_triple suffix' -> 'a1) -> nat -> kind ->
  ending -> color -> 'a2 storage -> 'a2 list -> 'a2 storage_right_seq_graph
  -> 'a1

val storage_right_seq_graph_correct :
  nat -> kind -> ending -> color -> 'a1 storage -> 'a1 storage_right_seq_graph

val storage_right_seq_elim :
  (__ -> nat -> nat -> __ stored_triple prefix' -> 'a1) -> (__ -> nat -> nat
  -> __ stored_triple prefix' -> __ stored_triple suffix' -> 'a1) -> (__ ->
  nat -> nat -> __ stored_triple prefix' -> __ stored_triple suffix' -> 'a1)
  -> (__ -> nat -> color -> nat -> nat -> coloring -> __ stored_triple
  prefix' -> __ stored_triple suffix' -> 'a1) -> (__ -> nat -> color -> nat
  -> nat -> coloring -> __ stored_triple prefix' -> __ stored_triple suffix'
  -> 'a1) -> (__ -> nat -> color -> nat -> nat -> coloring -> __
  stored_triple prefix' -> __ stored_triple suffix' -> 'a1) -> nat -> kind ->
  ending -> color -> 'a2 storage -> 'a1

val coq_FunctionalElimination_storage_right_seq :
  (__ -> nat -> nat -> __ stored_triple prefix' -> __) -> (__ -> nat -> nat
  -> __ stored_triple prefix' -> __ stored_triple suffix' -> __) -> (__ ->
  nat -> nat -> __ stored_triple prefix' -> __ stored_triple suffix' -> __)
  -> (__ -> nat -> color -> nat -> nat -> coloring -> __ stored_triple
  prefix' -> __ stored_triple suffix' -> __) -> (__ -> nat -> color -> nat ->
  nat -> coloring -> __ stored_triple prefix' -> __ stored_triple suffix' ->
  __) -> (__ -> nat -> color -> nat -> nat -> coloring -> __ stored_triple
  prefix' -> __ stored_triple suffix' -> __) -> nat -> kind -> ending ->
  color -> __ storage -> __

val coq_FunctionalInduction_storage_right_seq :
  (__ -> nat -> kind -> ending -> color -> __ storage -> __ list)
  coq_FunctionalInduction

val body_left_seq : nat -> nat -> kind -> kind -> 'a1 body -> 'a1 list

type 'a body_left_seq_graph =
| Coq_body_left_seq_graph_equation_1 of nat * kind
| Coq_body_left_seq_graph_equation_2 of nat * nat * kind * kind
   * 'a stored_triple storage' * 'a body * 'a body_left_seq_graph
| Coq_body_left_seq_graph_equation_3 of nat * nat * kind * kind
   * 'a stored_triple storage' * 'a body * 'a body_left_seq_graph
| Coq_body_left_seq_graph_equation_4 of nat * nat * kind * kind * color
   * 'a stored_triple storage' * 'a body * 'a chain * 'a body_left_seq_graph
| Coq_body_left_seq_graph_equation_5 of nat * nat * kind * kind
   * 'a stored_triple storage' * 'a chain * 'a body * 'a body_left_seq_graph

val body_left_seq_graph_rect :
  (__ -> nat -> kind -> 'a1) -> (__ -> nat -> nat -> kind -> kind -> __
  stored_triple storage' -> __ body -> __ body_left_seq_graph -> 'a1 -> 'a1)
  -> (__ -> nat -> nat -> kind -> kind -> __ stored_triple storage' -> __
  body -> __ body_left_seq_graph -> 'a1 -> 'a1) -> (__ -> nat -> nat -> kind
  -> kind -> color -> __ stored_triple storage' -> __ body -> __ chain -> __
  body_left_seq_graph -> 'a1 -> 'a1) -> (__ -> nat -> nat -> kind -> kind ->
  __ stored_triple storage' -> __ chain -> __ body -> __ body_left_seq_graph
  -> 'a1 -> 'a1) -> nat -> nat -> kind -> kind -> 'a2 body -> 'a2 list -> 'a2
  body_left_seq_graph -> 'a1

val body_left_seq_graph_correct :
  nat -> nat -> kind -> kind -> 'a1 body -> 'a1 body_left_seq_graph

val body_left_seq_elim :
  (__ -> nat -> kind -> 'a1) -> (__ -> nat -> nat -> kind -> kind -> __
  stored_triple storage' -> __ body -> 'a1 -> 'a1) -> (__ -> nat -> nat ->
  kind -> kind -> __ stored_triple storage' -> __ body -> 'a1 -> 'a1) -> (__
  -> nat -> nat -> kind -> kind -> color -> __ stored_triple storage' -> __
  body -> __ chain -> 'a1 -> 'a1) -> (__ -> nat -> nat -> kind -> kind -> __
  stored_triple storage' -> __ chain -> __ body -> 'a1 -> 'a1) -> nat -> nat
  -> kind -> kind -> 'a2 body -> 'a1

val coq_FunctionalElimination_body_left_seq :
  (__ -> nat -> kind -> __) -> (__ -> nat -> nat -> kind -> kind -> __
  stored_triple storage' -> __ body -> __ -> __) -> (__ -> nat -> nat -> kind
  -> kind -> __ stored_triple storage' -> __ body -> __ -> __) -> (__ -> nat
  -> nat -> kind -> kind -> color -> __ stored_triple storage' -> __ body ->
  __ chain -> __ -> __) -> (__ -> nat -> nat -> kind -> kind -> __
  stored_triple storage' -> __ chain -> __ body -> __ -> __) -> nat -> nat ->
  kind -> kind -> __ body -> __

val coq_FunctionalInduction_body_left_seq :
  (__ -> nat -> nat -> kind -> kind -> __ body -> __ list)
  coq_FunctionalInduction

val body_right_seq : nat -> nat -> kind -> kind -> 'a1 body -> 'a1 list

type 'a body_right_seq_graph =
| Coq_body_right_seq_graph_equation_1 of nat * kind
| Coq_body_right_seq_graph_equation_2 of nat * nat * kind * kind
   * 'a stored_triple storage' * 'a body * 'a body_right_seq_graph
| Coq_body_right_seq_graph_equation_3 of nat * nat * kind * kind
   * 'a stored_triple storage' * 'a body * 'a body_right_seq_graph
| Coq_body_right_seq_graph_equation_4 of nat * nat * kind * kind * color
   * 'a stored_triple storage' * 'a body * 'a chain * 'a body_right_seq_graph
| Coq_body_right_seq_graph_equation_5 of nat * nat * kind * kind
   * 'a stored_triple storage' * 'a chain * 'a body * 'a body_right_seq_graph

val body_right_seq_graph_rect :
  (__ -> nat -> kind -> 'a1) -> (__ -> nat -> nat -> kind -> kind -> __
  stored_triple storage' -> __ body -> __ body_right_seq_graph -> 'a1 -> 'a1)
  -> (__ -> nat -> nat -> kind -> kind -> __ stored_triple storage' -> __
  body -> __ body_right_seq_graph -> 'a1 -> 'a1) -> (__ -> nat -> nat -> kind
  -> kind -> color -> __ stored_triple storage' -> __ body -> __ chain -> __
  body_right_seq_graph -> 'a1 -> 'a1) -> (__ -> nat -> nat -> kind -> kind ->
  __ stored_triple storage' -> __ chain -> __ body -> __ body_right_seq_graph
  -> 'a1 -> 'a1) -> nat -> nat -> kind -> kind -> 'a2 body -> 'a2 list -> 'a2
  body_right_seq_graph -> 'a1

val body_right_seq_graph_correct :
  nat -> nat -> kind -> kind -> 'a1 body -> 'a1 body_right_seq_graph

val body_right_seq_elim :
  (__ -> nat -> kind -> 'a1) -> (__ -> nat -> nat -> kind -> kind -> __
  stored_triple storage' -> __ body -> 'a1 -> 'a1) -> (__ -> nat -> nat ->
  kind -> kind -> __ stored_triple storage' -> __ body -> 'a1 -> 'a1) -> (__
  -> nat -> nat -> kind -> kind -> color -> __ stored_triple storage' -> __
  body -> __ chain -> 'a1 -> 'a1) -> (__ -> nat -> nat -> kind -> kind -> __
  stored_triple storage' -> __ chain -> __ body -> 'a1 -> 'a1) -> nat -> nat
  -> kind -> kind -> 'a2 body -> 'a1

val coq_FunctionalElimination_body_right_seq :
  (__ -> nat -> kind -> __) -> (__ -> nat -> nat -> kind -> kind -> __
  stored_triple storage' -> __ body -> __ -> __) -> (__ -> nat -> nat -> kind
  -> kind -> __ stored_triple storage' -> __ body -> __ -> __) -> (__ -> nat
  -> nat -> kind -> kind -> color -> __ stored_triple storage' -> __ body ->
  __ chain -> __ -> __) -> (__ -> nat -> nat -> kind -> kind -> __
  stored_triple storage' -> __ chain -> __ body -> __ -> __) -> nat -> nat ->
  kind -> kind -> __ body -> __

val coq_FunctionalInduction_body_right_seq :
  (__ -> nat -> nat -> kind -> kind -> __ body -> __ list)
  coq_FunctionalInduction

val packet_left_seq :
  nat -> nat -> kind -> ending -> color -> 'a1 packet -> 'a1 list

type 'a packet_left_seq_graph =
| Coq_packet_left_seq_graph_equation_1 of nat * nat * kind * ending
   * green_hue * red_hue * kind * 'a body * 'a stored_triple storage'

val packet_left_seq_graph_rect :
  (__ -> nat -> nat -> kind -> ending -> green_hue -> red_hue -> kind -> __
  body -> __ stored_triple storage' -> 'a1) -> nat -> nat -> kind -> ending
  -> color -> 'a2 packet -> 'a2 list -> 'a2 packet_left_seq_graph -> 'a1

val packet_left_seq_graph_correct :
  nat -> nat -> kind -> ending -> color -> 'a1 packet -> 'a1
  packet_left_seq_graph

val packet_left_seq_elim :
  (__ -> nat -> nat -> kind -> ending -> green_hue -> red_hue -> kind -> __
  body -> __ stored_triple storage' -> 'a1) -> nat -> nat -> kind -> ending
  -> color -> 'a2 packet -> 'a1

val coq_FunctionalElimination_packet_left_seq :
  (__ -> nat -> nat -> kind -> ending -> green_hue -> red_hue -> kind -> __
  body -> __ stored_triple storage' -> __) -> nat -> nat -> kind -> ending ->
  color -> __ packet -> __

val coq_FunctionalInduction_packet_left_seq :
  (__ -> nat -> nat -> kind -> ending -> color -> __ packet -> __ list)
  coq_FunctionalInduction

val packet_right_seq :
  nat -> nat -> kind -> ending -> color -> 'a1 packet -> 'a1 list

type 'a packet_right_seq_graph =
| Coq_packet_right_seq_graph_equation_1 of nat * nat * kind * ending
   * green_hue * red_hue * kind * 'a body * 'a stored_triple storage'

val packet_right_seq_graph_rect :
  (__ -> nat -> nat -> kind -> ending -> green_hue -> red_hue -> kind -> __
  body -> __ stored_triple storage' -> 'a1) -> nat -> nat -> kind -> ending
  -> color -> 'a2 packet -> 'a2 list -> 'a2 packet_right_seq_graph -> 'a1

val packet_right_seq_graph_correct :
  nat -> nat -> kind -> ending -> color -> 'a1 packet -> 'a1
  packet_right_seq_graph

val packet_right_seq_elim :
  (__ -> nat -> nat -> kind -> ending -> green_hue -> red_hue -> kind -> __
  body -> __ stored_triple storage' -> 'a1) -> nat -> nat -> kind -> ending
  -> color -> 'a2 packet -> 'a1

val coq_FunctionalElimination_packet_right_seq :
  (__ -> nat -> nat -> kind -> ending -> green_hue -> red_hue -> kind -> __
  body -> __ stored_triple storage' -> __) -> nat -> nat -> kind -> ending ->
  color -> __ packet -> __

val coq_FunctionalInduction_packet_right_seq :
  (__ -> nat -> nat -> kind -> ending -> color -> __ packet -> __ list)
  coq_FunctionalInduction

val ne_chain_seq :
  nat -> kind -> kind -> color -> color -> 'a1 non_ending_chain -> 'a1 list

type 'a ne_chain_seq_graph =
| Coq_ne_chain_seq_graph_equation_1 of nat * kind * kind * color * color
   * ending * 'a chain

val ne_chain_seq_graph_rect :
  (__ -> nat -> kind -> kind -> color -> color -> ending -> __ chain -> 'a1)
  -> nat -> kind -> kind -> color -> color -> 'a2 non_ending_chain -> 'a2
  list -> 'a2 ne_chain_seq_graph -> 'a1

val ne_chain_seq_graph_correct :
  nat -> kind -> kind -> color -> color -> 'a1 non_ending_chain -> 'a1
  ne_chain_seq_graph

val ne_chain_seq_elim :
  (__ -> nat -> kind -> kind -> color -> color -> ending -> __ chain -> 'a1)
  -> nat -> kind -> kind -> color -> color -> 'a2 non_ending_chain -> 'a1

val coq_FunctionalElimination_ne_chain_seq :
  (__ -> nat -> kind -> kind -> color -> color -> ending -> __ chain -> __)
  -> nat -> kind -> kind -> color -> color -> __ non_ending_chain -> __

val coq_FunctionalInduction_ne_chain_seq :
  (__ -> nat -> kind -> kind -> color -> color -> __ non_ending_chain -> __
  list) coq_FunctionalInduction

val triple_seq : nat -> kind -> color -> 'a1 triple -> 'a1 list

type 'a triple_seq_graph =
| Coq_triple_seq_graph_equation_1 of nat * kind * color * kind * ending
   * color * color * color * regularity * 'a storage * 'a chain

val triple_seq_graph_rect :
  (__ -> nat -> kind -> color -> kind -> ending -> color -> color -> color ->
  regularity -> __ storage -> __ chain -> 'a1) -> nat -> kind -> color -> 'a2
  triple -> 'a2 list -> 'a2 triple_seq_graph -> 'a1

val triple_seq_graph_correct :
  nat -> kind -> color -> 'a1 triple -> 'a1 triple_seq_graph

val triple_seq_elim :
  (__ -> nat -> kind -> color -> kind -> ending -> color -> color -> color ->
  regularity -> __ storage -> __ chain -> 'a1) -> nat -> kind -> color -> 'a2
  triple -> 'a1

val coq_FunctionalElimination_triple_seq :
  (__ -> nat -> kind -> color -> kind -> ending -> color -> color -> color ->
  regularity -> __ storage -> __ chain -> __) -> nat -> kind -> color -> __
  triple -> __

val coq_FunctionalInduction_triple_seq :
  (__ -> nat -> kind -> color -> __ triple -> __ list) coq_FunctionalInduction

val lr_triple_seq : nat -> kind -> color -> 'a1 left_right_triple -> 'a1 list

type 'a lr_triple_seq_graph =
| Coq_lr_triple_seq_graph_equation_1 of nat * kind * 'a stored_triple vector
| Coq_lr_triple_seq_graph_equation_2 of nat * kind * color * 'a triple

val lr_triple_seq_graph_rect :
  (__ -> nat -> kind -> __ stored_triple vector -> 'a1) -> (__ -> nat -> kind
  -> color -> __ triple -> 'a1) -> nat -> kind -> color -> 'a2
  left_right_triple -> 'a2 list -> 'a2 lr_triple_seq_graph -> 'a1

val lr_triple_seq_graph_correct :
  nat -> kind -> color -> 'a1 left_right_triple -> 'a1 lr_triple_seq_graph

val lr_triple_seq_elim :
  (__ -> nat -> kind -> __ stored_triple vector -> 'a1) -> (__ -> nat -> kind
  -> color -> __ triple -> 'a1) -> nat -> kind -> color -> 'a2
  left_right_triple -> 'a1

val coq_FunctionalElimination_lr_triple_seq :
  (__ -> nat -> kind -> __ stored_triple vector -> __) -> (__ -> nat -> kind
  -> color -> __ triple -> __) -> nat -> kind -> color -> __
  left_right_triple -> __

val coq_FunctionalInduction_lr_triple_seq :
  (__ -> nat -> kind -> color -> __ left_right_triple -> __ list)
  coq_FunctionalInduction

val six_stored_triple_seq : nat -> 'a1 six_stored_triple -> 'a1 list

type 'a six_stored_triple_seq_graph =
| Coq_six_stored_triple_seq_graph_equation_1 of nat * 'a stored_triple
   * 'a stored_triple * 'a stored_triple * 'a stored_triple
   * 'a stored_triple * 'a stored_triple

val six_stored_triple_seq_graph_rect :
  (__ -> nat -> __ stored_triple -> __ stored_triple -> __ stored_triple ->
  __ stored_triple -> __ stored_triple -> __ stored_triple -> 'a1) -> nat ->
  'a2 six_stored_triple -> 'a2 list -> 'a2 six_stored_triple_seq_graph -> 'a1

val six_stored_triple_seq_graph_correct :
  nat -> 'a1 six_stored_triple -> 'a1 six_stored_triple_seq_graph

val six_stored_triple_seq_elim :
  (__ -> nat -> __ stored_triple -> __ stored_triple -> __ stored_triple ->
  __ stored_triple -> __ stored_triple -> __ stored_triple -> 'a1) -> nat ->
  'a2 six_stored_triple -> 'a1

val coq_FunctionalElimination_six_stored_triple_seq :
  (__ -> nat -> __ stored_triple -> __ stored_triple -> __ stored_triple ->
  __ stored_triple -> __ stored_triple -> __ stored_triple -> __) -> nat ->
  __ six_stored_triple -> __

val coq_FunctionalInduction_six_stored_triple_seq :
  (__ -> nat -> __ six_stored_triple -> __ list) coq_FunctionalInduction

val pt_triple_seq : nat -> kind -> kind -> 'a1 partial_triple -> 'a1 list

type 'a pt_triple_seq_graph =
| Coq_pt_triple_seq_graph_equation_1 of nat * kind
| Coq_pt_triple_seq_graph_equation_2 of nat * kind * 'a six_stored_triple
| Coq_pt_triple_seq_graph_equation_3 of nat * kind * kind * color * 'a triple

val pt_triple_seq_graph_rect :
  (__ -> nat -> kind -> 'a1) -> (__ -> nat -> kind -> __ six_stored_triple ->
  'a1) -> (__ -> nat -> kind -> kind -> color -> __ triple -> 'a1) -> nat ->
  kind -> kind -> 'a2 partial_triple -> 'a2 list -> 'a2 pt_triple_seq_graph
  -> 'a1

val pt_triple_seq_graph_correct :
  nat -> kind -> kind -> 'a1 partial_triple -> 'a1 pt_triple_seq_graph

val pt_triple_seq_elim :
  (__ -> nat -> kind -> 'a1) -> (__ -> nat -> kind -> __ six_stored_triple ->
  'a1) -> (__ -> nat -> kind -> kind -> color -> __ triple -> 'a1) -> nat ->
  kind -> kind -> 'a2 partial_triple -> 'a1

val coq_FunctionalElimination_pt_triple_seq :
  (__ -> nat -> kind -> __) -> (__ -> nat -> kind -> __ six_stored_triple ->
  __) -> (__ -> nat -> kind -> kind -> color -> __ triple -> __) -> nat ->
  kind -> kind -> __ partial_triple -> __

val coq_FunctionalInduction_pt_triple_seq :
  (__ -> nat -> kind -> kind -> __ partial_triple -> __ list)
  coq_FunctionalInduction

val sandwich_seq :
  ('a1 -> 'a3 list) -> ('a2 -> 'a3 list) -> ('a1, 'a2) sandwich -> 'a3 list

type ('a, 'b, 'c) sandwich_seq_graph =
| Coq_sandwich_seq_graph_equation_1 of ('a -> 'c list) * ('b -> 'c list) * 'a
| Coq_sandwich_seq_graph_equation_2 of ('a -> 'c list) * ('b -> 'c list) *
   'a * 'b * 'a

val sandwich_seq_graph_rect :
  (__ -> __ -> __ -> (__ -> __ list) -> (__ -> __ list) -> __ -> 'a1) -> (__
  -> __ -> __ -> (__ -> __ list) -> (__ -> __ list) -> __ -> __ -> __ -> 'a1)
  -> ('a2 -> 'a4 list) -> ('a3 -> 'a4 list) -> ('a2, 'a3) sandwich -> 'a4
  list -> ('a2, 'a3, 'a4) sandwich_seq_graph -> 'a1

val sandwich_seq_graph_correct :
  ('a1 -> 'a3 list) -> ('a2 -> 'a3 list) -> ('a1, 'a2) sandwich -> ('a1, 'a2,
  'a3) sandwich_seq_graph

val sandwich_seq_elim :
  (__ -> __ -> __ -> (__ -> __ list) -> (__ -> __ list) -> __ -> 'a1) -> (__
  -> __ -> __ -> (__ -> __ list) -> (__ -> __ list) -> __ -> __ -> __ -> 'a1)
  -> ('a2 -> 'a4 list) -> ('a3 -> 'a4 list) -> ('a2, 'a3) sandwich -> 'a1

val coq_FunctionalElimination_sandwich_seq :
  (__ -> __ -> __ -> (__ -> __ list) -> (__ -> __ list) -> __ -> __) -> (__
  -> __ -> __ -> (__ -> __ list) -> (__ -> __ list) -> __ -> __ -> __ -> __)
  -> (__ -> __ list) -> (__ -> __ list) -> (__, __) sandwich -> __

val coq_FunctionalInduction_sandwich_seq :
  (__ -> __ -> __ -> (__ -> __ list) -> (__ -> __ list) -> (__, __) sandwich
  -> __ list) coq_FunctionalInduction

val semi_deque_seq : nat -> 'a1 semi_deque -> 'a1 list

type 'a semi_deque_seq_graph =
| Coq_semi_deque_seq_graph_equation_1 of nat * kind * ending * color *
   color * 'a chain

val semi_deque_seq_graph_rect :
  (__ -> nat -> kind -> ending -> color -> color -> __ chain -> 'a1) -> nat
  -> 'a2 semi_deque -> 'a2 list -> 'a2 semi_deque_seq_graph -> 'a1

val semi_deque_seq_graph_correct :
  nat -> 'a1 semi_deque -> 'a1 semi_deque_seq_graph

val semi_deque_seq_elim :
  (__ -> nat -> kind -> ending -> color -> color -> __ chain -> 'a1) -> nat
  -> 'a2 semi_deque -> 'a1

val coq_FunctionalElimination_semi_deque_seq :
  (__ -> nat -> kind -> ending -> color -> color -> __ chain -> __) -> nat ->
  __ semi_deque -> __

val coq_FunctionalInduction_semi_deque_seq :
  (__ -> nat -> __ semi_deque -> __ list) coq_FunctionalInduction

val deque_seq : 'a1 deque -> 'a1 list

type 'a deque_seq_graph =
| Coq_deque_seq_graph_equation_1 of kind * ending * 'a chain

val deque_seq_graph_rect :
  (__ -> kind -> ending -> __ chain -> 'a1) -> 'a2 deque -> 'a2 list -> 'a2
  deque_seq_graph -> 'a1

val deque_seq_graph_correct : 'a1 deque -> 'a1 deque_seq_graph

val deque_seq_elim :
  (__ -> kind -> ending -> __ chain -> 'a1) -> 'a2 deque -> 'a1

val coq_FunctionalElimination_deque_seq :
  (__ -> kind -> ending -> __ chain -> __) -> __ deque -> __

val coq_FunctionalInduction_deque_seq :
  (__ -> __ deque -> __ list) coq_FunctionalInduction
