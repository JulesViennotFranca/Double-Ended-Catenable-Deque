open Classes
open Datatypes
open Buffer
open Types

type __ = Obj.t

module D :
 sig
  val empty : 'a1 deque

  type 'a empty_graph =
  | Coq_empty_graph_equation_1

  val empty_graph_rect : (__ -> 'a1) -> 'a2 deque -> 'a2 empty_graph -> 'a1

  val empty_graph_correct : 'a1 empty_graph

  val empty_elim : (__ -> 'a1) -> 'a1

  val coq_FunctionalElimination_empty : (__ -> __) -> __

  val coq_FunctionalInduction_empty : (__ -> __ deque) coq_FunctionalInduction

  val push_clause_1 :
    'a1 -> kind -> ending -> 'a1 chain -> 'a1 chain -> 'a1 deque

  val push : 'a1 -> 'a1 deque -> 'a1 deque

  type 'a push_graph =
  | Coq_push_graph_refinement_1 of 'a * kind * ending * 'a chain
     * 'a push_clause_1_graph
  and 'a push_clause_1_graph =
  | Coq_push_clause_1_graph_equation_1 of 'a * kind * ending * 'a chain
     * 'a chain

  val push_clause_1_graph_mut :
    (__ -> __ -> kind -> ending -> __ chain -> __ push_clause_1_graph -> 'a2
    -> 'a1) -> (__ -> __ -> kind -> ending -> __ chain -> __ chain -> __ ->
    'a2) -> 'a3 -> kind -> ending -> 'a3 chain -> 'a3 chain -> 'a3 deque ->
    'a3 push_clause_1_graph -> 'a2

  val push_graph_mut :
    (__ -> __ -> kind -> ending -> __ chain -> __ push_clause_1_graph -> 'a2
    -> 'a1) -> (__ -> __ -> kind -> ending -> __ chain -> __ chain -> __ ->
    'a2) -> 'a3 -> 'a3 deque -> 'a3 deque -> 'a3 push_graph -> 'a1

  val push_graph_rect :
    (__ -> __ -> kind -> ending -> __ chain -> __ push_clause_1_graph -> 'a2
    -> 'a1) -> (__ -> __ -> kind -> ending -> __ chain -> __ chain -> __ ->
    'a2) -> 'a3 -> 'a3 deque -> 'a3 deque -> 'a3 push_graph -> 'a1

  val push_graph_correct : 'a1 -> 'a1 deque -> 'a1 push_graph

  val push_elim :
    (__ -> __ -> kind -> ending -> __ chain -> __ chain -> __ -> __ -> 'a1)
    -> 'a2 -> 'a2 deque -> 'a1

  val coq_FunctionalElimination_push :
    (__ -> __ -> kind -> ending -> __ chain -> __ chain -> __ -> __ -> __) ->
    __ -> __ deque -> __

  val coq_FunctionalInduction_push :
    (__ -> __ -> __ deque -> __ deque) coq_FunctionalInduction

  val inject_clause_1 :
    kind -> ending -> 'a1 chain -> 'a1 -> 'a1 chain -> 'a1 deque

  val inject : 'a1 deque -> 'a1 -> 'a1 deque

  type 'a inject_graph =
  | Coq_inject_graph_refinement_1 of kind * ending * 'a chain * 'a
     * 'a inject_clause_1_graph
  and 'a inject_clause_1_graph =
  | Coq_inject_clause_1_graph_equation_1 of kind * ending * 'a chain *
     'a * 'a chain

  val inject_clause_1_graph_mut :
    (__ -> kind -> ending -> __ chain -> __ -> __ inject_clause_1_graph ->
    'a2 -> 'a1) -> (__ -> kind -> ending -> __ chain -> __ -> __ chain -> __
    -> 'a2) -> kind -> ending -> 'a3 chain -> 'a3 -> 'a3 chain -> 'a3 deque
    -> 'a3 inject_clause_1_graph -> 'a2

  val inject_graph_mut :
    (__ -> kind -> ending -> __ chain -> __ -> __ inject_clause_1_graph ->
    'a2 -> 'a1) -> (__ -> kind -> ending -> __ chain -> __ -> __ chain -> __
    -> 'a2) -> 'a3 deque -> 'a3 -> 'a3 deque -> 'a3 inject_graph -> 'a1

  val inject_graph_rect :
    (__ -> kind -> ending -> __ chain -> __ -> __ inject_clause_1_graph ->
    'a2 -> 'a1) -> (__ -> kind -> ending -> __ chain -> __ -> __ chain -> __
    -> 'a2) -> 'a3 deque -> 'a3 -> 'a3 deque -> 'a3 inject_graph -> 'a1

  val inject_graph_correct : 'a1 deque -> 'a1 -> 'a1 inject_graph

  val inject_elim :
    (__ -> kind -> ending -> __ chain -> __ -> __ chain -> __ -> __ -> 'a1)
    -> 'a2 deque -> 'a2 -> 'a1

  val coq_FunctionalElimination_inject :
    (__ -> kind -> ending -> __ chain -> __ -> __ chain -> __ -> __ -> __) ->
    __ deque -> __ -> __

  val coq_FunctionalInduction_inject :
    (__ -> __ deque -> __ -> __ deque) coq_FunctionalInduction

  val concat_clause_1_clause_1 :
    kind -> ending -> 'a1 chain -> 'a1 stored_triple vector -> kind -> ending
    -> 'a1 chain -> 'a1 non_ending_chain -> 'a1 deque

  val concat_clause_1_clause_2_clause_1 :
    kind -> ending -> 'a1 chain -> 'a1 triple -> kind -> ending -> 'a1 chain
    -> 'a1 stored_triple vector -> 'a1 non_ending_chain -> 'a1 deque

  val concat_clause_1_clause_2_clause_2_clause_1 :
    kind -> ending -> 'a1 chain -> 'a1 triple -> 'a1 chain -> kind -> ending
    -> 'a1 chain -> 'a1 triple -> 'a1 chain -> 'a1 deque

  val concat_clause_1_clause_2_clause_2 :
    kind -> ending -> 'a1 chain -> 'a1 triple -> 'a1 chain -> kind -> ending
    -> 'a1 chain -> 'a1 triple -> 'a1 deque

  val concat_clause_1_clause_2 :
    kind -> ending -> 'a1 chain -> 'a1 triple -> kind -> ending -> 'a1 chain
    -> 'a1 left_right_triple -> 'a1 deque

  val concat_clause_1 :
    kind -> ending -> 'a1 chain -> 'a1 left_right_triple -> kind -> ending ->
    'a1 chain -> 'a1 deque

  val concat : 'a1 deque -> 'a1 deque -> 'a1 deque

  type 'a concat_graph =
  | Coq_concat_graph_refinement_1 of kind * ending * 'a chain * kind *
     ending * 'a chain * 'a concat_clause_1_graph
  and 'a concat_clause_1_graph =
  | Coq_concat_clause_1_graph_refinement_1 of kind * ending * 'a chain
     * 'a stored_triple vector * kind * ending * 'a chain
     * 'a concat_clause_1_clause_1_graph
  | Coq_concat_clause_1_graph_refinement_2 of kind * ending * 'a chain
     * 'a triple * kind * ending * 'a chain
     * 'a concat_clause_1_clause_2_graph
  and 'a0 concat_clause_1_clause_1_graph =
  | Coq_concat_clause_1_clause_1_graph_equation_1 of kind * ending
     * 'a0 chain * 'a0 stored_triple vector * kind * ending * 'a0 chain
     * ending * 'a0 chain
  and 'a1 concat_clause_1_clause_2_graph =
  | Coq_concat_clause_1_clause_2_graph_refinement_1 of kind * ending
     * 'a1 chain * 'a1 triple * kind * ending * 'a1 chain
     * 'a1 stored_triple vector * 'a1 concat_clause_1_clause_2_clause_1_graph
  | Coq_concat_clause_1_clause_2_graph_refinement_2 of kind * ending
     * 'a1 chain * 'a1 triple * kind * ending * 'a1 chain * 'a1 triple
     * 'a1 concat_clause_1_clause_2_clause_2_graph
  and 'a concat_clause_1_clause_2_clause_1_graph =
  | Coq_concat_clause_1_clause_2_clause_1_graph_equation_1 of kind *
     ending * 'a chain * 'a triple * kind * ending * 'a chain
     * 'a stored_triple vector * ending * 'a chain
  and 'a0 concat_clause_1_clause_2_clause_2_graph =
  | Coq_concat_clause_1_clause_2_clause_2_graph_refinement_1 of kind *
     ending * 'a0 chain * 'a0 triple * 'a0 chain * kind * ending * 'a0 chain
     * 'a0 triple * 'a0 concat_clause_1_clause_2_clause_2_clause_1_graph
  and 'a0 concat_clause_1_clause_2_clause_2_clause_1_graph =
  | Coq_concat_clause_1_clause_2_clause_2_clause_1_graph_equation_1 of
     kind * ending * 'a0 chain * 'a0 triple * 'a0 chain * kind * ending
     * 'a0 chain * 'a0 triple * 'a0 chain

  val concat_clause_1_clause_2_clause_2_clause_1_graph_mut :
    (__ -> kind -> ending -> __ chain -> kind -> ending -> __ chain -> __
    concat_clause_1_graph -> 'a2 -> 'a1) -> (__ -> kind -> ending -> __ chain
    -> __ stored_triple vector -> __ -> kind -> ending -> __ chain -> __
    concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> kind -> ending ->
    __ chain -> __ triple -> __ -> kind -> ending -> __ chain -> __
    concat_clause_1_clause_2_graph -> 'a4 -> 'a2) -> (__ -> kind -> ending ->
    __ chain -> __ stored_triple vector -> __ -> kind -> ending -> __ chain
    -> ending -> __ chain -> __ -> 'a3) -> (__ -> kind -> ending -> __ chain
    -> __ triple -> __ -> kind -> ending -> __ chain -> __ stored_triple
    vector -> __ -> __ concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4)
    -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind -> ending
    -> __ chain -> __ triple -> __ -> __
    concat_clause_1_clause_2_clause_2_graph -> 'a6 -> 'a4) -> (__ -> kind ->
    ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain -> __
    stored_triple vector -> ending -> __ chain -> __ -> __ -> 'a5) -> (__ ->
    kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> kind ->
    ending -> __ chain -> __ triple -> __ -> __
    concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 -> 'a6) -> (__ ->
    kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ -> kind
    -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ -> 'a7) ->
    kind -> ending -> 'a8 chain -> 'a8 triple -> 'a8 chain -> kind -> ending
    -> 'a8 chain -> 'a8 triple -> 'a8 chain -> 'a8 deque -> 'a8
    concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7

  val concat_clause_1_clause_2_clause_2_graph_mut :
    (__ -> kind -> ending -> __ chain -> kind -> ending -> __ chain -> __
    concat_clause_1_graph -> 'a2 -> 'a1) -> (__ -> kind -> ending -> __ chain
    -> __ stored_triple vector -> __ -> kind -> ending -> __ chain -> __
    concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> kind -> ending ->
    __ chain -> __ triple -> __ -> kind -> ending -> __ chain -> __
    concat_clause_1_clause_2_graph -> 'a4 -> 'a2) -> (__ -> kind -> ending ->
    __ chain -> __ stored_triple vector -> __ -> kind -> ending -> __ chain
    -> ending -> __ chain -> __ -> 'a3) -> (__ -> kind -> ending -> __ chain
    -> __ triple -> __ -> kind -> ending -> __ chain -> __ stored_triple
    vector -> __ -> __ concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4)
    -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind -> ending
    -> __ chain -> __ triple -> __ -> __
    concat_clause_1_clause_2_clause_2_graph -> 'a6 -> 'a4) -> (__ -> kind ->
    ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain -> __
    stored_triple vector -> ending -> __ chain -> __ -> __ -> 'a5) -> (__ ->
    kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> kind ->
    ending -> __ chain -> __ triple -> __ -> __
    concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 -> 'a6) -> (__ ->
    kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ -> kind
    -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ -> 'a7) ->
    kind -> ending -> 'a8 chain -> 'a8 triple -> 'a8 chain -> kind -> ending
    -> 'a8 chain -> 'a8 triple -> 'a8 deque -> 'a8
    concat_clause_1_clause_2_clause_2_graph -> 'a6

  val concat_clause_1_clause_2_clause_1_graph_mut :
    (__ -> kind -> ending -> __ chain -> kind -> ending -> __ chain -> __
    concat_clause_1_graph -> 'a2 -> 'a1) -> (__ -> kind -> ending -> __ chain
    -> __ stored_triple vector -> __ -> kind -> ending -> __ chain -> __
    concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> kind -> ending ->
    __ chain -> __ triple -> __ -> kind -> ending -> __ chain -> __
    concat_clause_1_clause_2_graph -> 'a4 -> 'a2) -> (__ -> kind -> ending ->
    __ chain -> __ stored_triple vector -> __ -> kind -> ending -> __ chain
    -> ending -> __ chain -> __ -> 'a3) -> (__ -> kind -> ending -> __ chain
    -> __ triple -> __ -> kind -> ending -> __ chain -> __ stored_triple
    vector -> __ -> __ concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4)
    -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind -> ending
    -> __ chain -> __ triple -> __ -> __
    concat_clause_1_clause_2_clause_2_graph -> 'a6 -> 'a4) -> (__ -> kind ->
    ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain -> __
    stored_triple vector -> ending -> __ chain -> __ -> __ -> 'a5) -> (__ ->
    kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> kind ->
    ending -> __ chain -> __ triple -> __ -> __
    concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 -> 'a6) -> (__ ->
    kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ -> kind
    -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ -> 'a7) ->
    kind -> ending -> 'a8 chain -> 'a8 triple -> kind -> ending -> 'a8 chain
    -> 'a8 stored_triple vector -> 'a8 non_ending_chain -> 'a8 deque -> 'a8
    concat_clause_1_clause_2_clause_1_graph -> 'a5

  val concat_clause_1_clause_2_graph_mut :
    (__ -> kind -> ending -> __ chain -> kind -> ending -> __ chain -> __
    concat_clause_1_graph -> 'a2 -> 'a1) -> (__ -> kind -> ending -> __ chain
    -> __ stored_triple vector -> __ -> kind -> ending -> __ chain -> __
    concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> kind -> ending ->
    __ chain -> __ triple -> __ -> kind -> ending -> __ chain -> __
    concat_clause_1_clause_2_graph -> 'a4 -> 'a2) -> (__ -> kind -> ending ->
    __ chain -> __ stored_triple vector -> __ -> kind -> ending -> __ chain
    -> ending -> __ chain -> __ -> 'a3) -> (__ -> kind -> ending -> __ chain
    -> __ triple -> __ -> kind -> ending -> __ chain -> __ stored_triple
    vector -> __ -> __ concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4)
    -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind -> ending
    -> __ chain -> __ triple -> __ -> __
    concat_clause_1_clause_2_clause_2_graph -> 'a6 -> 'a4) -> (__ -> kind ->
    ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain -> __
    stored_triple vector -> ending -> __ chain -> __ -> __ -> 'a5) -> (__ ->
    kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> kind ->
    ending -> __ chain -> __ triple -> __ -> __
    concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 -> 'a6) -> (__ ->
    kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ -> kind
    -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ -> 'a7) ->
    kind -> ending -> 'a8 chain -> 'a8 triple -> kind -> ending -> 'a8 chain
    -> 'a8 left_right_triple -> 'a8 deque -> 'a8
    concat_clause_1_clause_2_graph -> 'a4

  val concat_clause_1_clause_1_graph_mut :
    (__ -> kind -> ending -> __ chain -> kind -> ending -> __ chain -> __
    concat_clause_1_graph -> 'a2 -> 'a1) -> (__ -> kind -> ending -> __ chain
    -> __ stored_triple vector -> __ -> kind -> ending -> __ chain -> __
    concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> kind -> ending ->
    __ chain -> __ triple -> __ -> kind -> ending -> __ chain -> __
    concat_clause_1_clause_2_graph -> 'a4 -> 'a2) -> (__ -> kind -> ending ->
    __ chain -> __ stored_triple vector -> __ -> kind -> ending -> __ chain
    -> ending -> __ chain -> __ -> 'a3) -> (__ -> kind -> ending -> __ chain
    -> __ triple -> __ -> kind -> ending -> __ chain -> __ stored_triple
    vector -> __ -> __ concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4)
    -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind -> ending
    -> __ chain -> __ triple -> __ -> __
    concat_clause_1_clause_2_clause_2_graph -> 'a6 -> 'a4) -> (__ -> kind ->
    ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain -> __
    stored_triple vector -> ending -> __ chain -> __ -> __ -> 'a5) -> (__ ->
    kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> kind ->
    ending -> __ chain -> __ triple -> __ -> __
    concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 -> 'a6) -> (__ ->
    kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ -> kind
    -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ -> 'a7) ->
    kind -> ending -> 'a8 chain -> 'a8 stored_triple vector -> kind -> ending
    -> 'a8 chain -> 'a8 non_ending_chain -> 'a8 deque -> 'a8
    concat_clause_1_clause_1_graph -> 'a3

  val concat_clause_1_graph_mut :
    (__ -> kind -> ending -> __ chain -> kind -> ending -> __ chain -> __
    concat_clause_1_graph -> 'a2 -> 'a1) -> (__ -> kind -> ending -> __ chain
    -> __ stored_triple vector -> __ -> kind -> ending -> __ chain -> __
    concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> kind -> ending ->
    __ chain -> __ triple -> __ -> kind -> ending -> __ chain -> __
    concat_clause_1_clause_2_graph -> 'a4 -> 'a2) -> (__ -> kind -> ending ->
    __ chain -> __ stored_triple vector -> __ -> kind -> ending -> __ chain
    -> ending -> __ chain -> __ -> 'a3) -> (__ -> kind -> ending -> __ chain
    -> __ triple -> __ -> kind -> ending -> __ chain -> __ stored_triple
    vector -> __ -> __ concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4)
    -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind -> ending
    -> __ chain -> __ triple -> __ -> __
    concat_clause_1_clause_2_clause_2_graph -> 'a6 -> 'a4) -> (__ -> kind ->
    ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain -> __
    stored_triple vector -> ending -> __ chain -> __ -> __ -> 'a5) -> (__ ->
    kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> kind ->
    ending -> __ chain -> __ triple -> __ -> __
    concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 -> 'a6) -> (__ ->
    kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ -> kind
    -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ -> 'a7) ->
    kind -> ending -> 'a8 chain -> 'a8 left_right_triple -> kind -> ending ->
    'a8 chain -> 'a8 deque -> 'a8 concat_clause_1_graph -> 'a2

  val concat_graph_mut :
    (__ -> kind -> ending -> __ chain -> kind -> ending -> __ chain -> __
    concat_clause_1_graph -> 'a2 -> 'a1) -> (__ -> kind -> ending -> __ chain
    -> __ stored_triple vector -> __ -> kind -> ending -> __ chain -> __
    concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> kind -> ending ->
    __ chain -> __ triple -> __ -> kind -> ending -> __ chain -> __
    concat_clause_1_clause_2_graph -> 'a4 -> 'a2) -> (__ -> kind -> ending ->
    __ chain -> __ stored_triple vector -> __ -> kind -> ending -> __ chain
    -> ending -> __ chain -> __ -> 'a3) -> (__ -> kind -> ending -> __ chain
    -> __ triple -> __ -> kind -> ending -> __ chain -> __ stored_triple
    vector -> __ -> __ concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4)
    -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind -> ending
    -> __ chain -> __ triple -> __ -> __
    concat_clause_1_clause_2_clause_2_graph -> 'a6 -> 'a4) -> (__ -> kind ->
    ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain -> __
    stored_triple vector -> ending -> __ chain -> __ -> __ -> 'a5) -> (__ ->
    kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> kind ->
    ending -> __ chain -> __ triple -> __ -> __
    concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 -> 'a6) -> (__ ->
    kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ -> kind
    -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ -> 'a7) -> 'a8
    deque -> 'a8 deque -> 'a8 deque -> 'a8 concat_graph -> 'a1

  val concat_graph_rect :
    (__ -> kind -> ending -> __ chain -> kind -> ending -> __ chain -> __
    concat_clause_1_graph -> 'a2 -> 'a1) -> (__ -> kind -> ending -> __ chain
    -> __ stored_triple vector -> __ -> kind -> ending -> __ chain -> __
    concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> kind -> ending ->
    __ chain -> __ triple -> __ -> kind -> ending -> __ chain -> __
    concat_clause_1_clause_2_graph -> 'a4 -> 'a2) -> (__ -> kind -> ending ->
    __ chain -> __ stored_triple vector -> __ -> kind -> ending -> __ chain
    -> ending -> __ chain -> __ -> 'a3) -> (__ -> kind -> ending -> __ chain
    -> __ triple -> __ -> kind -> ending -> __ chain -> __ stored_triple
    vector -> __ -> __ concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4)
    -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind -> ending
    -> __ chain -> __ triple -> __ -> __
    concat_clause_1_clause_2_clause_2_graph -> 'a6 -> 'a4) -> (__ -> kind ->
    ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain -> __
    stored_triple vector -> ending -> __ chain -> __ -> __ -> 'a5) -> (__ ->
    kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> kind ->
    ending -> __ chain -> __ triple -> __ -> __
    concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 -> 'a6) -> (__ ->
    kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ -> kind
    -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ -> 'a7) -> 'a8
    deque -> 'a8 deque -> 'a8 deque -> 'a8 concat_graph -> 'a1

  val concat_graph_correct : 'a1 deque -> 'a1 deque -> 'a1 concat_graph

  val concat_elim :
    (__ -> kind -> ending -> __ chain -> __ stored_triple vector -> __ ->
    kind -> ending -> __ chain -> ending -> __ chain -> __ -> __ -> __ ->
    'a1) -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind ->
    ending -> __ chain -> __ stored_triple vector -> ending -> __ chain -> __
    -> __ -> __ -> __ -> __ -> 'a1) -> (__ -> kind -> ending -> __ chain ->
    __ triple -> __ chain -> __ -> __ -> kind -> ending -> __ chain -> __
    triple -> __ chain -> __ -> __ -> __ -> __ -> __ -> __ -> 'a1) -> 'a2
    deque -> 'a2 deque -> 'a1

  val coq_FunctionalElimination_concat :
    (__ -> kind -> ending -> __ chain -> __ stored_triple vector -> __ ->
    kind -> ending -> __ chain -> ending -> __ chain -> __ -> __ -> __ -> __)
    -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind -> ending
    -> __ chain -> __ stored_triple vector -> ending -> __ chain -> __ -> __
    -> __ -> __ -> __ -> __) -> (__ -> kind -> ending -> __ chain -> __
    triple -> __ chain -> __ -> __ -> kind -> ending -> __ chain -> __ triple
    -> __ chain -> __ -> __ -> __ -> __ -> __ -> __ -> __) -> __ deque -> __
    deque -> __

  val coq_FunctionalInduction_concat :
    (__ -> __ deque -> __ deque -> __ deque) coq_FunctionalInduction

  val pop_clause_2_clause_1 :
    kind -> 'a1 chain -> 'a1 -> kind -> ending -> color -> color -> 'a1 chain
    -> 'a1 chain -> ('a1, 'a1 deque) prod option

  val pop_clause_2 :
    kind -> 'a1 chain -> ('a1 stored_triple, 'a1 semi_deque) prod -> ('a1,
    'a1 deque) prod option

  val pop : 'a1 deque -> ('a1, 'a1 deque) prod option

  type 'a pop_graph =
  | Coq_pop_graph_equation_1
  | Coq_pop_graph_refinement_2 of kind * 'a chain * 'a pop_clause_2_graph
  and 'a pop_clause_2_graph =
  | Coq_pop_clause_2_graph_refinement_1 of kind * 'a chain * 'a * kind
     * ending * color * color * 'a chain * 'a pop_clause_2_clause_1_graph
  and 'a0 pop_clause_2_clause_1_graph =
  | Coq_pop_clause_2_clause_1_graph_equation_1 of kind * 'a0 chain *
     'a0 * kind * ending * color * color * 'a0 chain * 'a0 chain

  val pop_clause_2_clause_1_graph_mut :
    (__ -> 'a1) -> (__ -> kind -> __ chain -> __ pop_clause_2_graph -> 'a2 ->
    'a1) -> (__ -> kind -> __ chain -> __ -> kind -> ending -> color -> color
    -> __ chain -> __ -> __ pop_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__
    -> kind -> __ chain -> __ -> kind -> ending -> color -> color -> __ chain
    -> __ chain -> __ -> __ -> 'a3) -> kind -> 'a4 chain -> 'a4 -> kind ->
    ending -> color -> color -> 'a4 chain -> 'a4 chain -> ('a4, 'a4 deque)
    prod option -> 'a4 pop_clause_2_clause_1_graph -> 'a3

  val pop_clause_2_graph_mut :
    (__ -> 'a1) -> (__ -> kind -> __ chain -> __ pop_clause_2_graph -> 'a2 ->
    'a1) -> (__ -> kind -> __ chain -> __ -> kind -> ending -> color -> color
    -> __ chain -> __ -> __ pop_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__
    -> kind -> __ chain -> __ -> kind -> ending -> color -> color -> __ chain
    -> __ chain -> __ -> __ -> 'a3) -> kind -> 'a4 chain -> ('a4
    stored_triple, 'a4 semi_deque) prod -> ('a4, 'a4 deque) prod option ->
    'a4 pop_clause_2_graph -> 'a2

  val pop_graph_mut :
    (__ -> 'a1) -> (__ -> kind -> __ chain -> __ pop_clause_2_graph -> 'a2 ->
    'a1) -> (__ -> kind -> __ chain -> __ -> kind -> ending -> color -> color
    -> __ chain -> __ -> __ pop_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__
    -> kind -> __ chain -> __ -> kind -> ending -> color -> color -> __ chain
    -> __ chain -> __ -> __ -> 'a3) -> 'a4 deque -> ('a4, 'a4 deque) prod
    option -> 'a4 pop_graph -> 'a1

  val pop_graph_rect :
    (__ -> 'a1) -> (__ -> kind -> __ chain -> __ pop_clause_2_graph -> 'a2 ->
    'a1) -> (__ -> kind -> __ chain -> __ -> kind -> ending -> color -> color
    -> __ chain -> __ -> __ pop_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__
    -> kind -> __ chain -> __ -> kind -> ending -> color -> color -> __ chain
    -> __ chain -> __ -> __ -> 'a3) -> 'a4 deque -> ('a4, 'a4 deque) prod
    option -> 'a4 pop_graph -> 'a1

  val pop_graph_correct : 'a1 deque -> 'a1 pop_graph

  val pop_elim :
    (__ -> 'a1) -> (__ -> kind -> __ chain -> __ -> kind -> ending -> color
    -> color -> __ chain -> __ chain -> __ -> __ -> __ -> __ -> 'a1) -> 'a2
    deque -> 'a1

  val coq_FunctionalElimination_pop :
    (__ -> __) -> (__ -> kind -> __ chain -> __ -> kind -> ending -> color ->
    color -> __ chain -> __ chain -> __ -> __ -> __ -> __ -> __) -> __ deque
    -> __

  val coq_FunctionalInduction_pop :
    (__ -> __ deque -> (__, __ deque) prod option) coq_FunctionalInduction

  val eject_clause_2_clause_1 :
    kind -> 'a1 chain -> kind -> ending -> color -> color -> 'a1 chain -> 'a1
    chain -> 'a1 -> ('a1 deque, 'a1) prod option

  val eject_clause_2 :
    kind -> 'a1 chain -> ('a1 semi_deque, 'a1 stored_triple) prod -> ('a1
    deque, 'a1) prod option

  val eject : 'a1 deque -> ('a1 deque, 'a1) prod option

  type 'a eject_graph =
  | Coq_eject_graph_equation_1
  | Coq_eject_graph_refinement_2 of kind * 'a chain * 'a eject_clause_2_graph
  and 'a eject_clause_2_graph =
  | Coq_eject_clause_2_graph_refinement_1 of kind * 'a chain * kind *
     ending * color * color * 'a chain * 'a * 'a eject_clause_2_clause_1_graph
  and 'a0 eject_clause_2_clause_1_graph =
  | Coq_eject_clause_2_clause_1_graph_equation_1 of kind * 'a0 chain *
     kind * ending * color * color * 'a0 chain * 'a0 chain * 'a0

  val eject_clause_2_clause_1_graph_mut :
    (__ -> 'a1) -> (__ -> kind -> __ chain -> __ eject_clause_2_graph -> 'a2
    -> 'a1) -> (__ -> kind -> __ chain -> kind -> ending -> color -> color ->
    __ chain -> __ -> __ -> __ eject_clause_2_clause_1_graph -> 'a3 -> 'a2)
    -> (__ -> kind -> __ chain -> kind -> ending -> color -> color -> __
    chain -> __ chain -> __ -> __ -> __ -> 'a3) -> kind -> 'a4 chain -> kind
    -> ending -> color -> color -> 'a4 chain -> 'a4 chain -> 'a4 -> ('a4
    deque, 'a4) prod option -> 'a4 eject_clause_2_clause_1_graph -> 'a3

  val eject_clause_2_graph_mut :
    (__ -> 'a1) -> (__ -> kind -> __ chain -> __ eject_clause_2_graph -> 'a2
    -> 'a1) -> (__ -> kind -> __ chain -> kind -> ending -> color -> color ->
    __ chain -> __ -> __ -> __ eject_clause_2_clause_1_graph -> 'a3 -> 'a2)
    -> (__ -> kind -> __ chain -> kind -> ending -> color -> color -> __
    chain -> __ chain -> __ -> __ -> __ -> 'a3) -> kind -> 'a4 chain -> ('a4
    semi_deque, 'a4 stored_triple) prod -> ('a4 deque, 'a4) prod option ->
    'a4 eject_clause_2_graph -> 'a2

  val eject_graph_mut :
    (__ -> 'a1) -> (__ -> kind -> __ chain -> __ eject_clause_2_graph -> 'a2
    -> 'a1) -> (__ -> kind -> __ chain -> kind -> ending -> color -> color ->
    __ chain -> __ -> __ -> __ eject_clause_2_clause_1_graph -> 'a3 -> 'a2)
    -> (__ -> kind -> __ chain -> kind -> ending -> color -> color -> __
    chain -> __ chain -> __ -> __ -> __ -> 'a3) -> 'a4 deque -> ('a4 deque,
    'a4) prod option -> 'a4 eject_graph -> 'a1

  val eject_graph_rect :
    (__ -> 'a1) -> (__ -> kind -> __ chain -> __ eject_clause_2_graph -> 'a2
    -> 'a1) -> (__ -> kind -> __ chain -> kind -> ending -> color -> color ->
    __ chain -> __ -> __ -> __ eject_clause_2_clause_1_graph -> 'a3 -> 'a2)
    -> (__ -> kind -> __ chain -> kind -> ending -> color -> color -> __
    chain -> __ chain -> __ -> __ -> __ -> 'a3) -> 'a4 deque -> ('a4 deque,
    'a4) prod option -> 'a4 eject_graph -> 'a1

  val eject_graph_correct : 'a1 deque -> 'a1 eject_graph

  val eject_elim :
    (__ -> 'a1) -> (__ -> kind -> __ chain -> kind -> ending -> color ->
    color -> __ chain -> __ chain -> __ -> __ -> __ -> __ -> __ -> 'a1) ->
    'a2 deque -> 'a1

  val coq_FunctionalElimination_eject :
    (__ -> __) -> (__ -> kind -> __ chain -> kind -> ending -> color -> color
    -> __ chain -> __ chain -> __ -> __ -> __ -> __ -> __ -> __) -> __ deque
    -> __

  val coq_FunctionalInduction_eject :
    (__ -> __ deque -> (__ deque, __) prod option) coq_FunctionalInduction
 end
