open Datatypes
open Buffer

type preferred_child =
| Preferred_left
| Preferred_right

type kind =
| Only
| Left
| Right

type green_hue =
| SomeGreen
| NoGreen

type yellow_hue =
| SomeYellow
| NoYellow

type orange_hue =
| SomeOrange
| NoOrange

type red_hue =
| SomeRed
| NoRed

type color =
| Mix of green_hue * yellow_hue * orange_hue * red_hue

type 'a prefix' = 'a t

type 'a suffix' = 'a t

type small_triple_sizes =
| Only_small_sizes of nat
| Left_small_sizes of nat
| Right_small_sizes of nat

type big_triple_sizes =
| Only_big_sizes of nat * nat
| Left_big_sizes of nat
| Right_big_sizes of nat

type 'a stored_triple =
| ST_ground of 'a
| ST_small of nat * nat * 'a stored_triple prefix'
| ST_triple of nat * nat * nat * color * 'a stored_triple prefix' * 'a cdeque
   * 'a stored_triple suffix'
and 'a triple =
| Hole of nat * kind
| Small of nat * nat * nat * kind * 'a stored_triple prefix'
   * 'a stored_triple suffix' * small_triple_sizes
| Green of nat * nat * nat * kind * green_hue * red_hue
   * 'a stored_triple prefix' * 'a non_empty_cdeque
   * 'a stored_triple suffix' * big_triple_sizes
| Yellow of nat * nat * nat * nat * kind * kind * 'a stored_triple prefix'
   * 'a packet * 'a stored_triple suffix' * big_triple_sizes
| Orange of nat * nat * nat * nat * kind * kind * 'a stored_triple prefix'
   * 'a packet * 'a stored_triple suffix' * big_triple_sizes
| Red of nat * nat * nat * kind * 'a stored_triple prefix'
   * 'a non_empty_cdeque * 'a stored_triple suffix' * big_triple_sizes
and 'a packet =
| Only_child of nat * nat * bool * kind * yellow_hue * orange_hue
   * preferred_child * 'a triple
| Left_child of nat * nat * bool * kind * yellow_hue * orange_hue * color
   * 'a triple * 'a path
| Right_child of nat * nat * bool * kind * yellow_hue * orange_hue * 
   'a path * 'a triple
and 'a path =
| Children of nat * nat * nat * bool * kind * kind * green_hue * yellow_hue
   * orange_hue * red_hue * 'a triple * 'a triple
and 'a non_empty_cdeque =
| Only_path of nat * green_hue * red_hue * 'a path
| Pair_green of nat * 'a path * 'a path
| Pair_red of nat * color * color * 'a path * 'a path
and 'a cdeque =
| Empty of nat
| NonEmpty of nat * green_hue * red_hue * 'a non_empty_cdeque

type 'a prefix = 'a stored_triple prefix'

type 'a suffix = 'a stored_triple suffix'

type 'a only_triple = 'a triple

type 'a left_triple = 'a triple

type 'a right_triple = 'a triple

type 'a pref_left =
| Pref_left of nat * nat * kind * green_hue * red_hue * 'a packet * 'a triple

type 'a pref_right =
| Pref_right of nat * nat * kind * green_hue * red_hue * 'a packet * 'a triple

type 'a buffer_12 = ('a stored_triple, 'a stored_triple vector) prod

type 'a path_attempt =
| ZeroSix of kind * color * 'a stored_triple vector
| Ok of kind * color * 'a path
| Any of kind * color * 'a path

type 'a path_uncolored =
| Six of 'a stored_triple * 'a stored_triple * 'a stored_triple
   * 'a stored_triple * 'a stored_triple * 'a stored_triple
| AnyColor of color * 'a path

type 'a sdeque =
| Sd of color * 'a cdeque

type 'a unstored =
| Unstored of nat * 'a prefix * 'a sdeque

type 'a sandwich =
| Alone of 'a stored_triple
| Sandwich of 'a stored_triple * 'a sdeque * 'a stored_triple

type 'a unstored_sandwich =
| Unstored_alone of nat * 'a prefix
| Unstored_sandwich of nat * nat * 'a prefix * 'a sdeque * 'a suffix

type 'a deque = 'a cdeque
  (* singleton inductive, whose constructor was T *)
