open Datatypes
(* open Nat *)
open Buffer
open Types

val push_only_triple :
  nat -> nat -> kind -> color -> 'a1 stored_triple -> 'a1 only_triple -> 'a1
  only_triple

val inject_only_triple :
  nat -> nat -> kind -> color -> 'a1 only_triple -> 'a1 stored_triple -> 'a1
  only_triple

val push_only_path : nat -> color -> 'a1 stored_triple -> 'a1 path -> 'a1 path

val inject_only_path :
  nat -> color -> 'a1 path -> 'a1 stored_triple -> 'a1 path

val push_left_triple :
  nat -> nat -> kind -> color -> 'a1 stored_triple -> 'a1 left_triple -> 'a1
  left_triple

val inject_right_triple :
  nat -> nat -> kind -> color -> 'a1 right_triple -> 'a1 stored_triple -> 'a1
  right_triple

val push_left_path : nat -> color -> 'a1 stored_triple -> 'a1 path -> 'a1 path

val inject_right_path :
  nat -> color -> 'a1 path -> 'a1 stored_triple -> 'a1 path

val push_ne_cdeque :
  nat -> color -> 'a1 stored_triple -> 'a1 non_empty_cdeque -> 'a1
  non_empty_cdeque

val inject_ne_cdeque :
  nat -> color -> 'a1 non_empty_cdeque -> 'a1 stored_triple -> 'a1
  non_empty_cdeque

val single_triple : nat -> 'a1 stored_triple -> 'a1 triple

val only_single : nat -> 'a1 stored_triple -> 'a1 non_empty_cdeque

val single : nat -> 'a1 stored_triple -> 'a1 cdeque

val push_cdeque :
  nat -> color -> 'a1 stored_triple -> 'a1 cdeque -> 'a1 cdeque

val inject_cdeque :
  nat -> color -> 'a1 cdeque -> 'a1 stored_triple -> 'a1 cdeque

val push_semi : nat -> 'a1 stored_triple -> 'a1 sdeque -> 'a1 sdeque

val inject_semi : nat -> 'a1 sdeque -> 'a1 stored_triple -> 'a1 sdeque

val push_vector :
  nat -> nat -> color -> 'a1 stored_triple vector -> 'a1 cdeque -> 'a1 cdeque

val inject_vector :
  nat -> nat -> color -> 'a1 cdeque -> 'a1 stored_triple vector -> 'a1 cdeque

val to_pref_left : nat -> color -> 'a1 non_empty_cdeque -> 'a1 pref_left

val to_pref_right :
  nat -> nat -> nat -> kind -> 'a1 packet -> 'a1 triple -> 'a1 pref_right

val no_pref :
  nat -> nat -> nat -> kind -> 'a1 packet -> 'a1 triple -> 'a1
  non_empty_cdeque

val make_child :
  nat -> nat -> nat -> preferred_child -> kind -> green_hue -> red_hue -> 'a1
  packet -> 'a1 triple -> 'a1 sdeque

val push_child :
  nat -> nat -> nat -> preferred_child -> kind -> green_hue -> red_hue -> 'a1
  stored_triple -> 'a1 packet -> 'a1 triple -> ('a1 packet, 'a1 triple) prod

val inject_child :
  nat -> nat -> nat -> preferred_child -> kind -> green_hue -> red_hue -> 'a1
  packet -> 'a1 triple -> 'a1 stored_triple -> ('a1 packet, 'a1 triple) prod

val stored_left :
  nat -> nat -> color -> 'a1 prefix -> 'a1 cdeque -> 'a1 suffix -> 'a1
  buffer_12 -> ('a1 prefix, 'a1 stored_triple) prod

val stored_right :
  nat -> nat -> color -> 'a1 buffer_12 -> 'a1 prefix -> 'a1 cdeque -> 'a1
  suffix -> ('a1 stored_triple, 'a1 suffix) prod

val extract_stored_left :
  nat -> color -> 'a1 path -> 'a1 buffer_12 -> ('a1 suffix, 'a1
  stored_triple) prod

val extract_stored_right :
  nat -> color -> 'a1 buffer_12 -> 'a1 path -> ('a1 stored_triple, 'a1
  suffix) prod

val left_of_pair : nat -> color -> color -> 'a1 path -> 'a1 path -> 'a1 path

val right_of_pair : nat -> color -> color -> 'a1 path -> 'a1 path -> 'a1 path

val left_of_only : nat -> color -> 'a1 path -> 'a1 path_attempt

val right_of_only : nat -> color -> 'a1 path -> 'a1 path_attempt

val make_left : nat -> color -> 'a1 cdeque -> 'a1 path_attempt

val make_right : nat -> color -> 'a1 cdeque -> 'a1 path_attempt

val concat_semi : nat -> 'a1 sdeque -> 'a1 sdeque -> 'a1 sdeque

val semi_of_left :
  nat -> color -> 'a1 path -> 'a1 stored_triple -> 'a1 stored_triple -> 'a1
  stored_triple -> 'a1 stored_triple -> 'a1 stored_triple -> 'a1
  stored_triple -> 'a1 sdeque

val semi_of_right :
  nat -> color -> 'a1 stored_triple -> 'a1 stored_triple -> 'a1 stored_triple
  -> 'a1 stored_triple -> 'a1 stored_triple -> 'a1 stored_triple -> 'a1 path
  -> 'a1 sdeque

val pop_green_left :
  nat -> 'a1 path -> ('a1 stored_triple, 'a1 path_uncolored) prod

val eject_green_right :
  nat -> 'a1 path -> ('a1 path_uncolored, 'a1 stored_triple) prod

val pop_green :
  nat -> 'a1 non_empty_cdeque -> ('a1 stored_triple, 'a1 sdeque) prod

val eject_green :
  nat -> 'a1 non_empty_cdeque -> ('a1 sdeque, 'a1 stored_triple) prod

val pop_stored : nat -> 'a1 non_empty_cdeque -> 'a1 unstored

val eject_stored : nat -> 'a1 non_empty_cdeque -> 'a1 unstored

val unsandwich_green : nat -> 'a1 non_empty_cdeque -> 'a1 sandwich

val unsandwich_stored : nat -> 'a1 non_empty_cdeque -> 'a1 unstored_sandwich

val only_small : nat -> nat -> nat -> 'a1 prefix -> 'a1 suffix -> 'a1 triple

val only_green :
  nat -> nat -> nat -> 'a1 prefix -> 'a1 sdeque -> 'a1 suffix -> 'a1 triple

val green_of_red_only : nat -> 'a1 triple -> 'a1 triple

val green_of_red_left : nat -> 'a1 triple -> 'a1 triple

val green_of_red_right : nat -> 'a1 triple -> 'a1 triple

val ensure_green :
  nat -> kind -> green_hue -> red_hue -> 'a1 triple -> 'a1 triple

val ensure_green_path : nat -> kind -> color -> 'a1 path -> 'a1 path

val ensure_green_cdeque :
  nat -> color -> 'a1 non_empty_cdeque -> 'a1 non_empty_cdeque

val regular_of_semi : 'a1 sdeque -> 'a1 deque
