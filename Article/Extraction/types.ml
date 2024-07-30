open Datatypes
open Buffer

type ending =
| Is_end
| Not_end

type kind =
| Pair
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

type coloring =
| G of nat * nat
| Y of nat * nat
| O of nat * nat
| R of nat * nat

type 'a storage' =
| Only_end of nat * 'a prefix'
| Left_end of nat * 'a prefix' * 'a suffix'
| Right_end of nat * 'a prefix' * 'a suffix'
| Only_st of nat * nat * color * coloring * 'a prefix' * 'a suffix'
| Left_st of nat * nat * color * coloring * 'a prefix' * 'a suffix'
| Right_st of nat * nat * color * coloring * 'a prefix' * 'a suffix'

type chain_regularity =
| Green_chain of color * color
| Red_chain

type 'a stored_triple =
| Ground of 'a
| Small of nat * nat * 'a stored_triple suffix'
| Big of nat * nat * nat * kind * ending * color * color
   * 'a stored_triple prefix' * 'a chain * 'a stored_triple suffix'
and 'a body =
| Hole of nat * kind
| Only_yellow of nat * nat * kind * kind * 'a stored_triple storage' * 'a body
| Only_orange of nat * nat * kind * kind * 'a stored_triple storage' * 'a body
| Pair_yellow of nat * nat * kind * kind * color * 'a stored_triple storage'
   * 'a body * 'a chain
| Pair_orange of nat * nat * kind * kind * 'a stored_triple storage'
   * 'a chain * 'a body
and 'a packet =
| Packet of nat * nat * kind * kind * ending * green_hue * red_hue * 
   'a body * 'a stored_triple storage'
and 'a chain =
| Empty of nat
| Only_chain of nat * nat * kind * kind * ending * color * color * color
   * chain_regularity * 'a packet * 'a chain
| Pair_chain of nat * color * color * 'a chain * 'a chain

type 'a prefix = 'a stored_triple prefix'

type 'a suffix = 'a stored_triple suffix'

type 'a green_buffer =
| Gbuf of nat * 'a stored_triple t

type 'a stored_buffer =
| Sbuf of nat * 'a stored_triple t

type 'a storage = 'a stored_triple storage'

type 'x non_ending_chain =
| NE_chain of nat * kind * kind * ending * color * color * 'x chain

type regularity =
| Green of kind * ending * color * color
| Yellow of kind * color * color
| OrangeO of color
| OrangeP of color
| Red of kind * ending

type 'x triple =
| Triple of nat * kind * kind * ending * color * color * color * color
   * regularity * 'x storage * 'x chain

type 'x left_right_triple =
| Not_enough of nat * kind * 'x stored_triple vector
| Ok_lrt of nat * kind * color * 'x triple

type 'a six_stored_triple =
  ((((('a stored_triple, 'a stored_triple) prod, 'a stored_triple) prod, 'a
  stored_triple) prod, 'a stored_triple) prod, 'a stored_triple) prod

type 'x partial_triple =
| Zero_element of nat * kind
| Six_elements of nat * kind * 'x six_stored_triple
| Ok_pt of nat * kind * kind * color * 'x triple

type ('x0, 'x) sandwich =
| Alone of 'x0
| Sandwich of 'x0 * 'x * 'x0

type 'x semi_deque =
| Semi of nat * kind * ending * color * color * 'x chain

type 'x deque =
| T of kind * ending * 'x chain
