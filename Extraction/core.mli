open Datatypes
open Buffer
open Types

val push_left_storage_obligations_obligation_2 : nat -> nat

val push_left_storage_obligations_obligation_4 : nat -> nat

val push_left_storage_obligations_obligation_6 : nat -> nat

val push_left_storage_obligations_obligation_8 : nat -> nat

val push_left_storage :
  nat -> ending -> color -> 'a1 stored_triple -> 'a1 storage -> 'a1 storage

val inject_right_storage_obligations_obligation_2 : nat -> nat

val inject_right_storage_obligations_obligation_4 : nat -> nat

val inject_right_storage_obligations_obligation_6 : nat -> nat

val inject_right_storage_obligations_obligation_8 : nat -> nat

val inject_right_storage :
  nat -> ending -> color -> 'a1 storage -> 'a1 stored_triple -> 'a1 storage

val push_only_storage :
  nat -> ending -> color -> 'a1 stored_triple -> 'a1 storage -> 'a1 storage

val inject_only_storage :
  nat -> ending -> color -> 'a1 storage -> 'a1 stored_triple -> 'a1 storage

val push_left_packet :
  nat -> nat -> ending -> color -> 'a1 stored_triple -> 'a1 packet -> 'a1
  packet

val inject_right_packet :
  nat -> nat -> ending -> color -> 'a1 packet -> 'a1 stored_triple -> 'a1
  packet

val push_only_packet :
  nat -> nat -> ending -> color -> 'a1 stored_triple -> 'a1 packet -> 'a1
  packet

val inject_only_packet :
  nat -> nat -> ending -> color -> 'a1 packet -> 'a1 stored_triple -> 'a1
  packet

val single_storage : nat -> 'a1 stored_triple -> 'a1 storage

val single_packet : nat -> 'a1 stored_triple -> 'a1 packet

val single_chain : nat -> 'a1 stored_triple -> 'a1 chain

val push_left_chain :
  nat -> color -> 'a1 stored_triple -> 'a1 chain -> 'a1 chain

val inject_right_chain :
  nat -> color -> 'a1 chain -> 'a1 stored_triple -> 'a1 chain

val push_chain :
  nat -> kind -> ending -> color -> color -> 'a1 stored_triple -> 'a1 chain
  -> 'a1 chain

val inject_chain :
  nat -> kind -> ending -> color -> color -> 'a1 chain -> 'a1 stored_triple
  -> 'a1 chain

val push_ne_chain :
  nat -> kind -> color -> color -> 'a1 stored_triple -> 'a1 non_ending_chain
  -> 'a1 non_ending_chain

val inject_ne_chain :
  nat -> kind -> color -> color -> 'a1 non_ending_chain -> 'a1 stored_triple
  -> 'a1 non_ending_chain

val push_vector :
  nat -> nat -> kind -> color -> color -> 'a1 stored_triple vector -> 'a1
  non_ending_chain -> 'a1 non_ending_chain

val inject_vector :
  nat -> nat -> kind -> color -> color -> 'a1 non_ending_chain -> 'a1
  stored_triple vector -> 'a1 non_ending_chain

val push_semi : nat -> 'a1 stored_triple -> 'a1 semi_deque -> 'a1 semi_deque

val inject_semi : nat -> 'a1 semi_deque -> 'a1 stored_triple -> 'a1 semi_deque

val triple_of_chain : nat -> kind -> color -> 'a1 chain -> 'a1 triple

val chain_of_triple : nat -> kind -> color -> 'a1 triple -> 'a1 chain

val left_of_only : nat -> color -> 'a1 triple -> 'a1 left_right_triple

val right_of_only : nat -> color -> 'a1 triple -> 'a1 left_right_triple

val make_stored_suffix :
  nat -> nat -> nat -> kind -> ending -> color -> color -> 'a1 suffix -> 'a1
  prefix -> 'a1 chain -> 'a1 suffix -> ('a1 stored_triple, 'a1 suffix) prod

val make_prefix_stored :
  nat -> nat -> nat -> kind -> ending -> color -> color -> 'a1 prefix -> 'a1
  chain -> 'a1 suffix -> 'a1 prefix -> ('a1 prefix, 'a1 stored_triple) prod

val stored_of_right :
  nat -> nat -> color -> 'a1 suffix -> 'a1 triple -> ('a1 stored_triple, 'a1
  suffix) prod

val stored_of_left :
  nat -> nat -> color -> 'a1 triple -> 'a1 prefix -> ('a1 prefix, 'a1
  stored_triple) prod

val left_of_pair_obligations_obligation_1 : nat -> nat

val left_of_pair :
  nat -> color -> color -> 'a1 triple -> 'a1 triple -> 'a1 triple

val right_of_pair_obligations_obligation_1 : nat -> nat

val right_of_pair :
  nat -> color -> color -> 'a1 triple -> 'a1 triple -> 'a1 triple

val make_left :
  nat -> kind -> ending -> color -> color -> 'a1 chain -> 'a1
  left_right_triple

val make_right :
  nat -> kind -> ending -> color -> color -> 'a1 chain -> 'a1
  left_right_triple

val concat_semi : nat -> 'a1 semi_deque -> 'a1 semi_deque -> 'a1 semi_deque

val orange_reg : nat -> kind -> color -> 'a1 chain -> regularity

val pop_left_green_obligations_obligation_3 : nat -> nat

val pop_left_green_obligations_obligation_5 : nat -> nat

val pop_left_green_obligations_obligation_7 : nat -> nat

val pop_left_green_obligations_obligation_9 : nat -> nat

val pop_left_green :
  nat -> 'a1 triple -> ('a1 stored_triple, 'a1 partial_triple) prod

val eject_right_green_obligations_obligation_3 : nat -> nat

val eject_right_green_obligations_obligation_5 : nat -> nat

val eject_right_green_obligations_obligation_7 : nat -> nat

val eject_right_green_obligations_obligation_9 : nat -> nat

val eject_right_green :
  nat -> 'a1 triple -> ('a1 partial_triple, 'a1 stored_triple) prod

val pop_only_green :
  nat -> 'a1 triple -> ('a1 stored_triple, 'a1 partial_triple) prod

val eject_only_green :
  nat -> 'a1 triple -> ('a1 partial_triple, 'a1 stored_triple) prod

val sandwich_only_green :
  nat -> 'a1 triple -> ('a1 stored_triple, 'a1 partial_triple) sandwich

val adapt_to_prefix : nat -> nat -> nat -> color -> coloring -> coloring

val only_of_right :
  nat -> color -> 'a1 six_stored_triple -> 'a1 triple -> 'a1 triple

val adapt_to_suffix : nat -> nat -> nat -> color -> coloring -> coloring

val only_of_left :
  nat -> color -> 'a1 triple -> 'a1 six_stored_triple -> 'a1 triple

val pop_pair_green :
  nat -> 'a1 chain -> ('a1 stored_triple, 'a1 semi_deque) prod

val eject_pair_green :
  nat -> 'a1 chain -> ('a1 semi_deque, 'a1 stored_triple) prod

val sandwich_pair_green :
  nat -> 'a1 chain -> ('a1 stored_triple, 'a1 semi_deque) sandwich

val pop_green :
  nat -> kind -> 'a1 chain -> ('a1 stored_triple, 'a1 semi_deque) prod

val eject_green :
  nat -> kind -> 'a1 chain -> ('a1 semi_deque, 'a1 stored_triple) prod

val sandwich_green :
  nat -> kind -> 'a1 chain -> ('a1 stored_triple, 'a1 semi_deque) sandwich

val make_green_prefix :
  nat -> nat -> nat -> 'a1 prefix -> 'a1 prefix -> 'a1 semi_deque -> ('a1
  green_buffer, 'a1 semi_deque) prod

val make_green_suffix :
  nat -> nat -> nat -> 'a1 semi_deque -> 'a1 suffix -> 'a1 suffix -> ('a1
  semi_deque, 'a1 green_buffer) prod

val extract_prefix :
  nat -> 'a1 stored_triple -> 'a1 semi_deque -> ('a1 stored_buffer, 'a1
  semi_deque) prod

val extract_suffix :
  nat -> 'a1 semi_deque -> 'a1 stored_triple -> ('a1 semi_deque, 'a1
  stored_buffer) prod

val ensure_green_prefix :
  nat -> nat -> kind -> 'a1 prefix -> 'a1 chain -> ('a1 green_buffer, 'a1
  semi_deque) prod

val ensure_green_suffix :
  nat -> nat -> kind -> 'a1 chain -> 'a1 suffix -> ('a1 semi_deque, 'a1
  green_buffer) prod

val ensure_green_left_obligations_obligation_2 : nat -> nat

val ensure_green_left :
  nat -> nat -> kind -> kind -> 'a1 body -> 'a1 storage -> 'a1 chain -> 'a1
  chain

val ensure_green_right_obligations_obligation_2 : nat -> nat

val ensure_green_right :
  nat -> nat -> kind -> kind -> 'a1 body -> 'a1 storage -> 'a1 chain -> 'a1
  chain

val make_green_only :
  nat -> nat -> kind -> nat -> nat -> 'a1 body -> 'a1 prefix -> 'a1
  semi_deque -> 'a1 prefix -> 'a1 chain

val ensure_green_only :
  nat -> nat -> kind -> kind -> 'a1 body -> 'a1 storage -> 'a1 chain -> 'a1
  chain

val ensure_green_obligations_obligation_4 : nat -> nat

val ensure_green_obligations_obligation_6 : nat -> nat

val ensure_green :
  nat -> kind -> kind -> ending -> color -> color -> 'a1 chain -> 'a1 chain
