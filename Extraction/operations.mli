open Classes
open Datatypes
open Buffer
(* open Core *)
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

  val push_clause_1 : 'a1 -> 'a1 cdeque -> 'a1 cdeque -> 'a1 deque

  val push : 'a1 -> 'a1 deque -> 'a1 deque

  type 'a push_graph =
  | Coq_push_graph_refinement_1 of 'a * 'a cdeque * 'a push_clause_1_graph
  and 'a push_clause_1_graph =
  | Coq_push_clause_1_graph_equation_1 of 'a * 'a cdeque * 'a cdeque

  val push_clause_1_graph_mut :
    (__ -> __ -> __ cdeque -> __ push_clause_1_graph -> 'a2 -> 'a1) -> (__ ->
    __ -> __ cdeque -> __ cdeque -> __ -> 'a2) -> 'a3 -> 'a3 cdeque -> 'a3
    cdeque -> 'a3 deque -> 'a3 push_clause_1_graph -> 'a2

  val push_graph_mut :
    (__ -> __ -> __ cdeque -> __ push_clause_1_graph -> 'a2 -> 'a1) -> (__ ->
    __ -> __ cdeque -> __ cdeque -> __ -> 'a2) -> 'a3 -> 'a3 deque -> 'a3
    deque -> 'a3 push_graph -> 'a1

  val push_graph_rect :
    (__ -> __ -> __ cdeque -> __ push_clause_1_graph -> 'a2 -> 'a1) -> (__ ->
    __ -> __ cdeque -> __ cdeque -> __ -> 'a2) -> 'a3 -> 'a3 deque -> 'a3
    deque -> 'a3 push_graph -> 'a1

  val push_graph_correct : 'a1 -> 'a1 deque -> 'a1 push_graph

  val push_elim :
    (__ -> __ -> __ cdeque -> __ cdeque -> __ -> __ -> 'a1) -> 'a2 -> 'a2
    deque -> 'a1

  val coq_FunctionalElimination_push :
    (__ -> __ -> __ cdeque -> __ cdeque -> __ -> __ -> __) -> __ -> __ deque
    -> __

  val coq_FunctionalInduction_push :
    (__ -> __ -> __ deque -> __ deque) coq_FunctionalInduction

  val inject_clause_1 : 'a1 cdeque -> 'a1 -> 'a1 cdeque -> 'a1 deque

  val inject : 'a1 deque -> 'a1 -> 'a1 deque

  type 'a inject_graph =
  | Coq_inject_graph_refinement_1 of 'a cdeque * 'a * 'a inject_clause_1_graph
  and 'a inject_clause_1_graph =
  | Coq_inject_clause_1_graph_equation_1 of 'a cdeque * 'a * 'a cdeque

  val inject_clause_1_graph_mut :
    (__ -> __ cdeque -> __ -> __ inject_clause_1_graph -> 'a2 -> 'a1) -> (__
    -> __ cdeque -> __ -> __ cdeque -> __ -> 'a2) -> 'a3 cdeque -> 'a3 -> 'a3
    cdeque -> 'a3 deque -> 'a3 inject_clause_1_graph -> 'a2

  val inject_graph_mut :
    (__ -> __ cdeque -> __ -> __ inject_clause_1_graph -> 'a2 -> 'a1) -> (__
    -> __ cdeque -> __ -> __ cdeque -> __ -> 'a2) -> 'a3 deque -> 'a3 -> 'a3
    deque -> 'a3 inject_graph -> 'a1

  val inject_graph_rect :
    (__ -> __ cdeque -> __ -> __ inject_clause_1_graph -> 'a2 -> 'a1) -> (__
    -> __ cdeque -> __ -> __ cdeque -> __ -> 'a2) -> 'a3 deque -> 'a3 -> 'a3
    deque -> 'a3 inject_graph -> 'a1

  val inject_graph_correct : 'a1 deque -> 'a1 -> 'a1 inject_graph

  val inject_elim :
    (__ -> __ cdeque -> __ -> __ cdeque -> __ -> __ -> 'a1) -> 'a2 deque ->
    'a2 -> 'a1

  val coq_FunctionalElimination_inject :
    (__ -> __ cdeque -> __ -> __ cdeque -> __ -> __ -> __) -> __ deque -> __
    -> __

  val coq_FunctionalInduction_inject :
    (__ -> __ deque -> __ -> __ deque) coq_FunctionalInduction

  val concat_clause_1_clause_1 :
    'a1 cdeque -> 'a1 stored_triple vector -> 'a1 cdeque -> 'a1 cdeque -> 'a1
    deque

  val concat_clause_1_clause_2_clause_1 :
    'a1 cdeque -> 'a1 path -> 'a1 cdeque -> 'a1 stored_triple vector -> 'a1
    cdeque -> 'a1 deque

  val concat_clause_1_clause_2 :
    'a1 cdeque -> 'a1 path -> 'a1 cdeque -> 'a1 path_attempt -> 'a1 deque

  val concat_clause_1 :
    'a1 cdeque -> 'a1 path_attempt -> 'a1 cdeque -> 'a1 deque

  val concat : 'a1 deque -> 'a1 deque -> 'a1 deque

  type 'a concat_graph =
  | Coq_concat_graph_refinement_1 of 'a cdeque * 'a cdeque
     * 'a concat_clause_1_graph
  and 'a concat_clause_1_graph =
  | Coq_concat_clause_1_graph_refinement_1 of 'a cdeque
     * 'a stored_triple vector * 'a cdeque * 'a concat_clause_1_clause_1_graph
  | Coq_concat_clause_1_graph_refinement_2 of 'a cdeque * 'a path * 'a cdeque
     * 'a concat_clause_1_clause_2_graph
  and 'a concat_clause_1_clause_1_graph =
  | Coq_concat_clause_1_clause_1_graph_equation_1 of 'a cdeque
     * 'a stored_triple vector * 'a cdeque * 'a cdeque
  and 'a concat_clause_1_clause_2_graph =
  | Coq_concat_clause_1_clause_2_graph_refinement_1 of 'a cdeque * 'a path
     * 'a cdeque * 'a stored_triple vector
     * 'a concat_clause_1_clause_2_clause_1_graph
  | Coq_concat_clause_1_clause_2_graph_equation_2 of 'a cdeque * 'a path
     * 'a cdeque * 'a path
  and 'a concat_clause_1_clause_2_clause_1_graph =
  | Coq_concat_clause_1_clause_2_clause_1_graph_equation_1 of 'a cdeque
     * 'a path * 'a cdeque * 'a stored_triple vector * 'a cdeque

  val concat_clause_1_clause_2_clause_1_graph_mut :
    (__ -> __ cdeque -> __ cdeque -> __ concat_clause_1_graph -> 'a2 -> 'a1)
    -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque -> __
    concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __ cdeque -> __
    path -> __ -> __ cdeque -> __ concat_clause_1_clause_2_graph -> 'a4 ->
    'a2) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque ->
    __ cdeque -> __ -> 'a3) -> (__ -> __ cdeque -> __ path -> __ -> __ cdeque
    -> __ stored_triple vector -> __ -> __
    concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> __
    cdeque -> __ path -> __ -> __ cdeque -> __ path -> __ -> 'a4) -> (__ ->
    __ cdeque -> __ path -> __ -> __ cdeque -> __ stored_triple vector -> __
    cdeque -> __ -> __ -> 'a5) -> 'a6 cdeque -> 'a6 path -> 'a6 cdeque -> 'a6
    stored_triple vector -> 'a6 cdeque -> 'a6 deque -> 'a6
    concat_clause_1_clause_2_clause_1_graph -> 'a5

  val concat_clause_1_clause_2_graph_mut :
    (__ -> __ cdeque -> __ cdeque -> __ concat_clause_1_graph -> 'a2 -> 'a1)
    -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque -> __
    concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __ cdeque -> __
    path -> __ -> __ cdeque -> __ concat_clause_1_clause_2_graph -> 'a4 ->
    'a2) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque ->
    __ cdeque -> __ -> 'a3) -> (__ -> __ cdeque -> __ path -> __ -> __ cdeque
    -> __ stored_triple vector -> __ -> __
    concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> __
    cdeque -> __ path -> __ -> __ cdeque -> __ path -> __ -> 'a4) -> (__ ->
    __ cdeque -> __ path -> __ -> __ cdeque -> __ stored_triple vector -> __
    cdeque -> __ -> __ -> 'a5) -> 'a6 cdeque -> 'a6 path -> 'a6 cdeque -> 'a6
    path_attempt -> 'a6 deque -> 'a6 concat_clause_1_clause_2_graph -> 'a4

  val concat_clause_1_clause_1_graph_mut :
    (__ -> __ cdeque -> __ cdeque -> __ concat_clause_1_graph -> 'a2 -> 'a1)
    -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque -> __
    concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __ cdeque -> __
    path -> __ -> __ cdeque -> __ concat_clause_1_clause_2_graph -> 'a4 ->
    'a2) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque ->
    __ cdeque -> __ -> 'a3) -> (__ -> __ cdeque -> __ path -> __ -> __ cdeque
    -> __ stored_triple vector -> __ -> __
    concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> __
    cdeque -> __ path -> __ -> __ cdeque -> __ path -> __ -> 'a4) -> (__ ->
    __ cdeque -> __ path -> __ -> __ cdeque -> __ stored_triple vector -> __
    cdeque -> __ -> __ -> 'a5) -> 'a6 cdeque -> 'a6 stored_triple vector ->
    'a6 cdeque -> 'a6 cdeque -> 'a6 deque -> 'a6
    concat_clause_1_clause_1_graph -> 'a3

  val concat_clause_1_graph_mut :
    (__ -> __ cdeque -> __ cdeque -> __ concat_clause_1_graph -> 'a2 -> 'a1)
    -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque -> __
    concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __ cdeque -> __
    path -> __ -> __ cdeque -> __ concat_clause_1_clause_2_graph -> 'a4 ->
    'a2) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque ->
    __ cdeque -> __ -> 'a3) -> (__ -> __ cdeque -> __ path -> __ -> __ cdeque
    -> __ stored_triple vector -> __ -> __
    concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> __
    cdeque -> __ path -> __ -> __ cdeque -> __ path -> __ -> 'a4) -> (__ ->
    __ cdeque -> __ path -> __ -> __ cdeque -> __ stored_triple vector -> __
    cdeque -> __ -> __ -> 'a5) -> 'a6 cdeque -> 'a6 path_attempt -> 'a6
    cdeque -> 'a6 deque -> 'a6 concat_clause_1_graph -> 'a2

  val concat_graph_mut :
    (__ -> __ cdeque -> __ cdeque -> __ concat_clause_1_graph -> 'a2 -> 'a1)
    -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque -> __
    concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __ cdeque -> __
    path -> __ -> __ cdeque -> __ concat_clause_1_clause_2_graph -> 'a4 ->
    'a2) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque ->
    __ cdeque -> __ -> 'a3) -> (__ -> __ cdeque -> __ path -> __ -> __ cdeque
    -> __ stored_triple vector -> __ -> __
    concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> __
    cdeque -> __ path -> __ -> __ cdeque -> __ path -> __ -> 'a4) -> (__ ->
    __ cdeque -> __ path -> __ -> __ cdeque -> __ stored_triple vector -> __
    cdeque -> __ -> __ -> 'a5) -> 'a6 deque -> 'a6 deque -> 'a6 deque -> 'a6
    concat_graph -> 'a1

  val concat_graph_rect :
    (__ -> __ cdeque -> __ cdeque -> __ concat_clause_1_graph -> 'a2 -> 'a1)
    -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque -> __
    concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __ cdeque -> __
    path -> __ -> __ cdeque -> __ concat_clause_1_clause_2_graph -> 'a4 ->
    'a2) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque ->
    __ cdeque -> __ -> 'a3) -> (__ -> __ cdeque -> __ path -> __ -> __ cdeque
    -> __ stored_triple vector -> __ -> __
    concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> __
    cdeque -> __ path -> __ -> __ cdeque -> __ path -> __ -> 'a4) -> (__ ->
    __ cdeque -> __ path -> __ -> __ cdeque -> __ stored_triple vector -> __
    cdeque -> __ -> __ -> 'a5) -> 'a6 deque -> 'a6 deque -> 'a6 deque -> 'a6
    concat_graph -> 'a1

  val concat_graph_correct : 'a1 deque -> 'a1 deque -> 'a1 concat_graph

  val concat_elim :
    (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque -> __
    cdeque -> __ -> __ -> __ -> 'a1) -> (__ -> __ cdeque -> __ path -> __ ->
    __ cdeque -> __ path -> __ -> __ -> __ -> 'a1) -> (__ -> __ cdeque -> __
    path -> __ -> __ cdeque -> __ stored_triple vector -> __ cdeque -> __ ->
    __ -> __ -> __ -> __ -> 'a1) -> 'a2 deque -> 'a2 deque -> 'a1

  val coq_FunctionalElimination_concat :
    (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque -> __
    cdeque -> __ -> __ -> __ -> __) -> (__ -> __ cdeque -> __ path -> __ ->
    __ cdeque -> __ path -> __ -> __ -> __ -> __) -> (__ -> __ cdeque -> __
    path -> __ -> __ cdeque -> __ stored_triple vector -> __ cdeque -> __ ->
    __ -> __ -> __ -> __ -> __) -> __ deque -> __ deque -> __

  val coq_FunctionalInduction_concat :
    (__ -> __ deque -> __ deque -> __ deque) coq_FunctionalInduction

  val pop_clause_2_clause_1 :
    'a1 non_empty_cdeque -> 'a1 -> 'a1 sdeque -> 'a1 deque -> ('a1, 'a1
    deque) prod option

  val pop_clause_2 :
    'a1 non_empty_cdeque -> ('a1 stored_triple, 'a1 sdeque) prod -> ('a1, 'a1
    deque) prod option

  val pop : 'a1 deque -> ('a1, 'a1 deque) prod option

  type 'a pop_graph =
  | Coq_pop_graph_equation_1
  | Coq_pop_graph_refinement_2 of 'a non_empty_cdeque * 'a pop_clause_2_graph
  and 'a pop_clause_2_graph =
  | Coq_pop_clause_2_graph_refinement_1 of 'a non_empty_cdeque * 'a
     * 'a sdeque * 'a pop_clause_2_clause_1_graph
  and 'a pop_clause_2_clause_1_graph =
  | Coq_pop_clause_2_clause_1_graph_equation_1 of 'a non_empty_cdeque * 
     'a * 'a sdeque * 'a deque

  val pop_clause_2_clause_1_graph_mut :
    (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ pop_clause_2_graph -> 'a2
    -> 'a1) -> (__ -> __ non_empty_cdeque -> __ -> __ sdeque -> __ -> __
    pop_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __ non_empty_cdeque
    -> __ -> __ sdeque -> __ deque -> __ -> __ -> 'a3) -> 'a4
    non_empty_cdeque -> 'a4 -> 'a4 sdeque -> 'a4 deque -> ('a4, 'a4 deque)
    prod option -> 'a4 pop_clause_2_clause_1_graph -> 'a3

  val pop_clause_2_graph_mut :
    (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ pop_clause_2_graph -> 'a2
    -> 'a1) -> (__ -> __ non_empty_cdeque -> __ -> __ sdeque -> __ -> __
    pop_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __ non_empty_cdeque
    -> __ -> __ sdeque -> __ deque -> __ -> __ -> 'a3) -> 'a4
    non_empty_cdeque -> ('a4 stored_triple, 'a4 sdeque) prod -> ('a4, 'a4
    deque) prod option -> 'a4 pop_clause_2_graph -> 'a2

  val pop_graph_mut :
    (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ pop_clause_2_graph -> 'a2
    -> 'a1) -> (__ -> __ non_empty_cdeque -> __ -> __ sdeque -> __ -> __
    pop_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __ non_empty_cdeque
    -> __ -> __ sdeque -> __ deque -> __ -> __ -> 'a3) -> 'a4 deque -> ('a4,
    'a4 deque) prod option -> 'a4 pop_graph -> 'a1

  val pop_graph_rect :
    (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ pop_clause_2_graph -> 'a2
    -> 'a1) -> (__ -> __ non_empty_cdeque -> __ -> __ sdeque -> __ -> __
    pop_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __ non_empty_cdeque
    -> __ -> __ sdeque -> __ deque -> __ -> __ -> 'a3) -> 'a4 deque -> ('a4,
    'a4 deque) prod option -> 'a4 pop_graph -> 'a1

  val pop_graph_correct : 'a1 deque -> 'a1 pop_graph

  val pop_elim :
    (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ -> __ sdeque -> __ deque
    -> __ -> __ -> __ -> __ -> 'a1) -> 'a2 deque -> 'a1

  val coq_FunctionalElimination_pop :
    (__ -> __) -> (__ -> __ non_empty_cdeque -> __ -> __ sdeque -> __ deque
    -> __ -> __ -> __ -> __ -> __) -> __ deque -> __

  val coq_FunctionalInduction_pop :
    (__ -> __ deque -> (__, __ deque) prod option) coq_FunctionalInduction

  val eject_clause_2_clause_1 :
    'a1 non_empty_cdeque -> 'a1 sdeque -> 'a1 deque -> 'a1 -> ('a1 deque,
    'a1) prod option

  val eject_clause_2 :
    'a1 non_empty_cdeque -> ('a1 sdeque, 'a1 stored_triple) prod -> ('a1
    deque, 'a1) prod option

  val eject : 'a1 deque -> ('a1 deque, 'a1) prod option

  type 'a eject_graph =
  | Coq_eject_graph_equation_1
  | Coq_eject_graph_refinement_2 of 'a non_empty_cdeque
     * 'a eject_clause_2_graph
  and 'a eject_clause_2_graph =
  | Coq_eject_clause_2_graph_refinement_1 of 'a non_empty_cdeque * 'a sdeque
     * 'a * 'a eject_clause_2_clause_1_graph
  and 'a eject_clause_2_clause_1_graph =
  | Coq_eject_clause_2_clause_1_graph_equation_1 of 'a non_empty_cdeque
     * 'a sdeque * 'a deque * 'a

  val eject_clause_2_clause_1_graph_mut :
    (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ eject_clause_2_graph ->
    'a2 -> 'a1) -> (__ -> __ non_empty_cdeque -> __ sdeque -> __ -> __ -> __
    eject_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __
    non_empty_cdeque -> __ sdeque -> __ deque -> __ -> __ -> __ -> 'a3) ->
    'a4 non_empty_cdeque -> 'a4 sdeque -> 'a4 deque -> 'a4 -> ('a4 deque,
    'a4) prod option -> 'a4 eject_clause_2_clause_1_graph -> 'a3

  val eject_clause_2_graph_mut :
    (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ eject_clause_2_graph ->
    'a2 -> 'a1) -> (__ -> __ non_empty_cdeque -> __ sdeque -> __ -> __ -> __
    eject_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __
    non_empty_cdeque -> __ sdeque -> __ deque -> __ -> __ -> __ -> 'a3) ->
    'a4 non_empty_cdeque -> ('a4 sdeque, 'a4 stored_triple) prod -> ('a4
    deque, 'a4) prod option -> 'a4 eject_clause_2_graph -> 'a2

  val eject_graph_mut :
    (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ eject_clause_2_graph ->
    'a2 -> 'a1) -> (__ -> __ non_empty_cdeque -> __ sdeque -> __ -> __ -> __
    eject_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __
    non_empty_cdeque -> __ sdeque -> __ deque -> __ -> __ -> __ -> 'a3) ->
    'a4 deque -> ('a4 deque, 'a4) prod option -> 'a4 eject_graph -> 'a1

  val eject_graph_rect :
    (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ eject_clause_2_graph ->
    'a2 -> 'a1) -> (__ -> __ non_empty_cdeque -> __ sdeque -> __ -> __ -> __
    eject_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __
    non_empty_cdeque -> __ sdeque -> __ deque -> __ -> __ -> __ -> 'a3) ->
    'a4 deque -> ('a4 deque, 'a4) prod option -> 'a4 eject_graph -> 'a1

  val eject_graph_correct : 'a1 deque -> 'a1 eject_graph

  val eject_elim :
    (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ sdeque -> __ deque -> __
    -> __ -> __ -> __ -> __ -> 'a1) -> 'a2 deque -> 'a1

  val coq_FunctionalElimination_eject :
    (__ -> __) -> (__ -> __ non_empty_cdeque -> __ sdeque -> __ deque -> __
    -> __ -> __ -> __ -> __ -> __) -> __ deque -> __

  val coq_FunctionalInduction_eject :
    (__ -> __ deque -> (__ deque, __) prod option) coq_FunctionalInduction
 end
