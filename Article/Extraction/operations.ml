open Datatypes
open Buffer
open Core
open Types

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module D =
 struct
  (** val empty : 'a1 deque **)

  let empty =
    T (Only, Is_end, (Empty Datatypes.O))

  type 'a empty_graph =
  | Coq_empty_graph_equation_1

  (** val empty_graph_rect :
      (__ -> 'a1) -> 'a2 deque -> 'a2 empty_graph -> 'a1 **)

  let empty_graph_rect f _ _ =
    f __

  (** val empty_graph_correct : 'a1 empty_graph **)

  let empty_graph_correct =
    Coq_empty_graph_equation_1

  (** val empty_elim : (__ -> 'a1) -> 'a1 **)

  let empty_elim f =
    f __

  (** val coq_FunctionalElimination_empty : (__ -> __) -> __ **)

  let coq_FunctionalElimination_empty =
    empty_elim

  (** val coq_FunctionalInduction_empty :
      (__ -> __ deque) coq_FunctionalInduction **)

  let coq_FunctionalInduction_empty =
    Obj.magic (fun _ -> empty_graph_correct)

  (** val push_clause_1 :
      'a1 -> kind -> ending -> 'a1 chain -> 'a1 chain -> 'a1 deque **)

  let push_clause_1 _ pk _ _ refine =
    T (pk, Not_end, refine)

  (** val push : 'a1 -> 'a1 deque -> 'a1 deque **)

  let push x = function
  | T (pk, e, c) ->
    T (pk, Not_end,
      (push_chain Datatypes.O pk e (Mix (SomeGreen, NoYellow, NoOrange,
        NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Ground x) c))

  type 'a push_graph =
  | Coq_push_graph_refinement_1 of 'a * kind * ending * 'a chain
     * 'a push_clause_1_graph
  and 'a push_clause_1_graph =
  | Coq_push_clause_1_graph_equation_1 of 'a * kind * ending * 'a chain
     * 'a chain

  (** val push_clause_1_graph_mut :
      (__ -> __ -> kind -> ending -> __ chain -> __ push_clause_1_graph ->
      'a2 -> 'a1) -> (__ -> __ -> kind -> ending -> __ chain -> __ chain ->
      __ -> 'a2) -> 'a3 -> kind -> ending -> 'a3 chain -> 'a3 chain -> 'a3
      deque -> 'a3 push_clause_1_graph -> 'a2 **)

  let push_clause_1_graph_mut _ f0 _ _ _ _ _ _ = function
  | Coq_push_clause_1_graph_equation_1 (x, pk, e, c, c') ->
    Obj.magic f0 __ x pk e c c' __

  (** val push_graph_mut :
      (__ -> __ -> kind -> ending -> __ chain -> __ push_clause_1_graph ->
      'a2 -> 'a1) -> (__ -> __ -> kind -> ending -> __ chain -> __ chain ->
      __ -> 'a2) -> 'a3 -> 'a3 deque -> 'a3 deque -> 'a3 push_graph -> 'a1 **)

  let push_graph_mut f f0 x d s p =
    let rec f1 _ _ _ = function
    | Coq_push_graph_refinement_1 (x0, pk, e, c, hind) ->
      Obj.magic f __ x0 pk e c hind
        (f2 __ x0 pk e c
          (push_chain Datatypes.O pk e (Mix (SomeGreen, NoYellow, NoOrange,
            NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Ground x0)
            c) (T (pk, Not_end,
          (push_chain Datatypes.O pk e (Mix (SomeGreen, NoYellow, NoOrange,
            NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Ground x0)
            c))) hind)
    and f2 _ _ _ _ _ _ _ = function
    | Coq_push_clause_1_graph_equation_1 (x0, pk, e, c, c') ->
      Obj.magic f0 __ x0 pk e c c' __
    in f1 x d s p

  (** val push_graph_rect :
      (__ -> __ -> kind -> ending -> __ chain -> __ push_clause_1_graph ->
      'a2 -> 'a1) -> (__ -> __ -> kind -> ending -> __ chain -> __ chain ->
      __ -> 'a2) -> 'a3 -> 'a3 deque -> 'a3 deque -> 'a3 push_graph -> 'a1 **)

  let push_graph_rect =
    push_graph_mut

  (** val push_graph_correct : 'a1 -> 'a1 deque -> 'a1 push_graph **)

  let push_graph_correct x = function
  | T (pk, e, c) ->
    Coq_push_graph_refinement_1 (x, pk, e, c,
      (let refine =
         push_chain Datatypes.O pk e (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Ground x) c
       in
       Coq_push_clause_1_graph_equation_1 (x, pk, e, c, refine)))

  (** val push_elim :
      (__ -> __ -> kind -> ending -> __ chain -> __ chain -> __ -> __ -> 'a1)
      -> 'a2 -> 'a2 deque -> 'a1 **)

  let push_elim f0 x d =
    push_graph_mut (fun _ _ _ _ _ _ x0 -> x0 __) f0 x d (push x d)
      (push_graph_correct x d)

  (** val coq_FunctionalElimination_push :
      (__ -> __ -> kind -> ending -> __ chain -> __ chain -> __ -> __ -> __)
      -> __ -> __ deque -> __ **)

  let coq_FunctionalElimination_push =
    push_elim

  (** val coq_FunctionalInduction_push :
      (__ -> __ -> __ deque -> __ deque) coq_FunctionalInduction **)

  let coq_FunctionalInduction_push =
    Obj.magic (fun _ -> push_graph_correct)

  (** val inject_clause_1 :
      kind -> ending -> 'a1 chain -> 'a1 -> 'a1 chain -> 'a1 deque **)

  let inject_clause_1 pk _ _ _ refine =
    T (pk, Not_end, refine)

  (** val inject : 'a1 deque -> 'a1 -> 'a1 deque **)

  let inject d x =
    let T (pk, e, c) = d in
    T (pk, Not_end,
    (inject_chain Datatypes.O pk e (Mix (SomeGreen, NoYellow, NoOrange,
      NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c (Ground x)))

  type 'a inject_graph =
  | Coq_inject_graph_refinement_1 of kind * ending * 'a chain * 'a
     * 'a inject_clause_1_graph
  and 'a inject_clause_1_graph =
  | Coq_inject_clause_1_graph_equation_1 of kind * ending * 'a chain *
     'a * 'a chain

  (** val inject_clause_1_graph_mut :
      (__ -> kind -> ending -> __ chain -> __ -> __ inject_clause_1_graph ->
      'a2 -> 'a1) -> (__ -> kind -> ending -> __ chain -> __ -> __ chain ->
      __ -> 'a2) -> kind -> ending -> 'a3 chain -> 'a3 -> 'a3 chain -> 'a3
      deque -> 'a3 inject_clause_1_graph -> 'a2 **)

  let inject_clause_1_graph_mut _ f0 _ _ _ _ _ _ = function
  | Coq_inject_clause_1_graph_equation_1 (pk, e, c, x, c') ->
    Obj.magic f0 __ pk e c x c' __

  (** val inject_graph_mut :
      (__ -> kind -> ending -> __ chain -> __ -> __ inject_clause_1_graph ->
      'a2 -> 'a1) -> (__ -> kind -> ending -> __ chain -> __ -> __ chain ->
      __ -> 'a2) -> 'a3 deque -> 'a3 -> 'a3 deque -> 'a3 inject_graph -> 'a1 **)

  let inject_graph_mut f f0 d x s i =
    let rec f1 _ _ _ = function
    | Coq_inject_graph_refinement_1 (pk, e, c, x0, hind) ->
      Obj.magic f __ pk e c x0 hind
        (f2 __ pk e c x0
          (inject_chain Datatypes.O pk e (Mix (SomeGreen, NoYellow, NoOrange,
            NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c (Ground
            x0)) (T (pk, Not_end,
          (inject_chain Datatypes.O pk e (Mix (SomeGreen, NoYellow, NoOrange,
            NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c (Ground
            x0)))) hind)
    and f2 _ _ _ _ _ _ _ = function
    | Coq_inject_clause_1_graph_equation_1 (pk, e, c, x0, c') ->
      Obj.magic f0 __ pk e c x0 c' __
    in f1 d x s i

  (** val inject_graph_rect :
      (__ -> kind -> ending -> __ chain -> __ -> __ inject_clause_1_graph ->
      'a2 -> 'a1) -> (__ -> kind -> ending -> __ chain -> __ -> __ chain ->
      __ -> 'a2) -> 'a3 deque -> 'a3 -> 'a3 deque -> 'a3 inject_graph -> 'a1 **)

  let inject_graph_rect =
    inject_graph_mut

  (** val inject_graph_correct : 'a1 deque -> 'a1 -> 'a1 inject_graph **)

  let inject_graph_correct d x =
    let T (pk, e, c) = d in
    Coq_inject_graph_refinement_1 (pk, e, c, x,
    (let refine =
       inject_chain Datatypes.O pk e (Mix (SomeGreen, NoYellow, NoOrange,
         NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c (Ground x)
     in
     Coq_inject_clause_1_graph_equation_1 (pk, e, c, x, refine)))

  (** val inject_elim :
      (__ -> kind -> ending -> __ chain -> __ -> __ chain -> __ -> __ -> 'a1)
      -> 'a2 deque -> 'a2 -> 'a1 **)

  let inject_elim f0 d x =
    inject_graph_mut (fun _ _ _ _ _ _ x0 -> x0 __) f0 d x (inject d x)
      (inject_graph_correct d x)

  (** val coq_FunctionalElimination_inject :
      (__ -> kind -> ending -> __ chain -> __ -> __ chain -> __ -> __ -> __)
      -> __ deque -> __ -> __ **)

  let coq_FunctionalElimination_inject =
    inject_elim

  (** val coq_FunctionalInduction_inject :
      (__ -> __ deque -> __ -> __ deque) coq_FunctionalInduction **)

  let coq_FunctionalInduction_inject =
    Obj.magic (fun _ -> inject_graph_correct)

  (** val concat_clause_1_clause_1 :
      kind -> ending -> 'a1 chain -> 'a1 stored_triple vector -> kind ->
      ending -> 'a1 chain -> 'a1 non_ending_chain -> 'a1 deque **)

  let concat_clause_1_clause_1 _ _ _ _ _ _ _ = function
  | NE_chain (_, pk, _, e, _, _, c) -> T (pk, e, c)

  (** val concat_clause_1_clause_2_clause_1 :
      kind -> ending -> 'a1 chain -> 'a1 triple -> kind -> ending -> 'a1
      chain -> 'a1 stored_triple vector -> 'a1 non_ending_chain -> 'a1 deque **)

  let concat_clause_1_clause_2_clause_1 _ _ _ _ _ _ _ _ = function
  | NE_chain (_, pk, _, e, _, _, c) -> T (pk, e, c)

  (** val concat_clause_1_clause_2_clause_2_clause_1 :
      kind -> ending -> 'a1 chain -> 'a1 triple -> 'a1 chain -> kind ->
      ending -> 'a1 chain -> 'a1 triple -> 'a1 chain -> 'a1 deque **)

  let concat_clause_1_clause_2_clause_2_clause_1 _ _ _ _ refine _ _ _ _ refine0 =
    T (Pair, Not_end, (Pair_chain (Datatypes.O, (Mix (SomeGreen, NoYellow,
      NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
      refine, refine0)))

  (** val concat_clause_1_clause_2_clause_2 :
      kind -> ending -> 'a1 chain -> 'a1 triple -> 'a1 chain -> kind ->
      ending -> 'a1 chain -> 'a1 triple -> 'a1 deque **)

  let concat_clause_1_clause_2_clause_2 _ _ _ _ refine _ _ _ tr =
    T (Pair, Not_end, (Pair_chain (Datatypes.O, (Mix (SomeGreen, NoYellow,
      NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
      refine,
      (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow, NoOrange,
        NoRed)) tr))))

  (** val concat_clause_1_clause_2 :
      kind -> ending -> 'a1 chain -> 'a1 triple -> kind -> ending -> 'a1
      chain -> 'a1 left_right_triple -> 'a1 deque **)

  let concat_clause_1_clause_2 pk e c1 tl _ _ _ = function
  | Not_enough (_, _, v) ->
    let NE_chain (_, pk0, _, e0, _, _, c) =
      inject_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk (Mix
        (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen, NoYellow,
        NoOrange, NoRed)) (NE_chain (Datatypes.O, pk, Only, e, (Mix
        (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
        NoOrange, NoRed)), c1)) v
    in
    T (pk0, e0, c)
  | Ok_lrt (_, _, _, t) ->
    T (Pair, Not_end, (Pair_chain (Datatypes.O, (Mix (SomeGreen, NoYellow,
      NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
      (chain_of_triple Datatypes.O Left (Mix (SomeGreen, NoYellow, NoOrange,
        NoRed)) tl),
      (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow, NoOrange,
        NoRed)) t))))

  (** val concat_clause_1 :
      kind -> ending -> 'a1 chain -> 'a1 left_right_triple -> kind -> ending
      -> 'a1 chain -> 'a1 deque **)

  let concat_clause_1 pk e c1 refine pk0 e0 c2 =
    match refine with
    | Not_enough (_, _, v) ->
      let NE_chain (_, pk1, _, e1, _, _, c) =
        push_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk0 (Mix
          (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen, NoYellow,
          NoOrange, NoRed)) v (NE_chain (Datatypes.O, pk0, Only, e0, (Mix
          (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
          NoOrange, NoRed)), c2))
      in
      T (pk1, e1, c)
    | Ok_lrt (_, _, _, t) ->
      (match make_right Datatypes.O pk0 e0 (Mix (SomeGreen, NoYellow,
               NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
               c2 with
       | Not_enough (_, _, v) ->
         let NE_chain (_, pk1, _, e1, _, _, c) =
           inject_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk
             (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen,
             NoYellow, NoOrange, NoRed)) (NE_chain (Datatypes.O, pk, Only, e,
             (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
             NoYellow, NoOrange, NoRed)), c1)) v
         in
         T (pk1, e1, c)
       | Ok_lrt (_, _, _, t0) ->
         T (Pair, Not_end, (Pair_chain (Datatypes.O, (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
           NoRed)),
           (chain_of_triple Datatypes.O Left (Mix (SomeGreen, NoYellow,
             NoOrange, NoRed)) t),
           (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
             NoOrange, NoRed)) t0)))))

  (** val concat : 'a1 deque -> 'a1 deque -> 'a1 deque **)

  let concat d1 d2 =
    let T (pk, e, c) = d1 in
    let T (pk0, e0, c0) = d2 in
    (match make_left Datatypes.O pk e (Mix (SomeGreen, NoYellow, NoOrange,
             NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c with
     | Not_enough (_, _, v) ->
       let NE_chain (_, pk1, _, e1, _, _, c1) =
         push_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk0 (Mix
           (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen, NoYellow,
           NoOrange, NoRed)) v (NE_chain (Datatypes.O, pk0, Only, e0, (Mix
           (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
           NoYellow, NoOrange, NoRed)), c0))
       in
       T (pk1, e1, c1)
     | Ok_lrt (_, _, _, t) ->
       (match make_right Datatypes.O pk0 e0 (Mix (SomeGreen, NoYellow,
                NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
                NoRed)) c0 with
        | Not_enough (_, _, v) ->
          let NE_chain (_, pk1, _, e1, _, _, c1) =
            inject_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk
              (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen,
              NoYellow, NoOrange, NoRed)) (NE_chain (Datatypes.O, pk, Only,
              e, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
              (SomeGreen, NoYellow, NoOrange, NoRed)), c)) v
          in
          T (pk1, e1, c1)
        | Ok_lrt (_, _, _, t0) ->
          T (Pair, Not_end, (Pair_chain (Datatypes.O, (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
            NoRed)),
            (chain_of_triple Datatypes.O Left (Mix (SomeGreen, NoYellow,
              NoOrange, NoRed)) t),
            (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
              NoOrange, NoRed)) t0))))))

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

  (** val concat_clause_1_clause_2_clause_2_clause_1_graph_mut :
      (__ -> kind -> ending -> __ chain -> kind -> ending -> __ chain -> __
      concat_clause_1_graph -> 'a2 -> 'a1) -> (__ -> kind -> ending -> __
      chain -> __ stored_triple vector -> __ -> kind -> ending -> __ chain ->
      __ concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> kind ->
      ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain ->
      __ concat_clause_1_clause_2_graph -> 'a4 -> 'a2) -> (__ -> kind ->
      ending -> __ chain -> __ stored_triple vector -> __ -> kind -> ending
      -> __ chain -> ending -> __ chain -> __ -> 'a3) -> (__ -> kind ->
      ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain ->
      __ stored_triple vector -> __ -> __
      concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> kind
      -> ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain
      -> __ triple -> __ -> __ concat_clause_1_clause_2_clause_2_graph -> 'a6
      -> 'a4) -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind
      -> ending -> __ chain -> __ stored_triple vector -> ending -> __ chain
      -> __ -> __ -> 'a5) -> (__ -> kind -> ending -> __ chain -> __ triple
      -> __ chain -> __ -> kind -> ending -> __ chain -> __ triple -> __ ->
      __ concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 -> 'a6) ->
      (__ -> kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __
      -> kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ ->
      'a7) -> kind -> ending -> 'a8 chain -> 'a8 triple -> 'a8 chain -> kind
      -> ending -> 'a8 chain -> 'a8 triple -> 'a8 chain -> 'a8 deque -> 'a8
      concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 **)

  let concat_clause_1_clause_2_clause_2_clause_1_graph_mut _ _ _ _ _ _ _ _ f7 _ _ _ _ _ _ _ _ _ _ _ = function
  | Coq_concat_clause_1_clause_2_clause_2_clause_1_graph_equation_1 (
      pk, e, c1, tl, cl, pk0, e0, c2, tr, cr) ->
    Obj.magic f7 __ pk e c1 tl cl __ __ pk0 e0 c2 tr cr __ __

  (** val concat_clause_1_clause_2_clause_2_graph_mut :
      (__ -> kind -> ending -> __ chain -> kind -> ending -> __ chain -> __
      concat_clause_1_graph -> 'a2 -> 'a1) -> (__ -> kind -> ending -> __
      chain -> __ stored_triple vector -> __ -> kind -> ending -> __ chain ->
      __ concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> kind ->
      ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain ->
      __ concat_clause_1_clause_2_graph -> 'a4 -> 'a2) -> (__ -> kind ->
      ending -> __ chain -> __ stored_triple vector -> __ -> kind -> ending
      -> __ chain -> ending -> __ chain -> __ -> 'a3) -> (__ -> kind ->
      ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain ->
      __ stored_triple vector -> __ -> __
      concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> kind
      -> ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain
      -> __ triple -> __ -> __ concat_clause_1_clause_2_clause_2_graph -> 'a6
      -> 'a4) -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind
      -> ending -> __ chain -> __ stored_triple vector -> ending -> __ chain
      -> __ -> __ -> 'a5) -> (__ -> kind -> ending -> __ chain -> __ triple
      -> __ chain -> __ -> kind -> ending -> __ chain -> __ triple -> __ ->
      __ concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 -> 'a6) ->
      (__ -> kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __
      -> kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ ->
      'a7) -> kind -> ending -> 'a8 chain -> 'a8 triple -> 'a8 chain -> kind
      -> ending -> 'a8 chain -> 'a8 triple -> 'a8 deque -> 'a8
      concat_clause_1_clause_2_clause_2_graph -> 'a6 **)

  let concat_clause_1_clause_2_clause_2_graph_mut f f0 f1 f2 f3 f4 f5 f6 f7 pk e c1 tl refine pk0 e0 c2 tr s c =
    let rec _f8 _ _ _ _ = function
    | Coq_concat_graph_refinement_1 (pk1, e1, c3, pk2, e2, c4, hind) ->
      f __ pk1 e1 c3 pk2 e2 c4 hind
        (_f9 __ pk1 e1 c3
          (make_left Datatypes.O pk1 e1 (Mix (SomeGreen, NoYellow, NoOrange,
            NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c3) pk2 e2
          c4
          (match make_left Datatypes.O pk1 e1 (Mix (SomeGreen, NoYellow,
                   NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
                   NoRed)) c3 with
           | Not_enough (_, _, v) ->
             let NE_chain (_, pk3, _, e3, _, _, c5) =
               push_vector Datatypes.O (S (S (S (S (S (S Datatypes.O))))))
                 pk2 (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix
                 (SomeGreen, NoYellow, NoOrange, NoRed)) v (NE_chain
                 (Datatypes.O, pk2, Only, e2, (Mix (SomeGreen, NoYellow,
                 NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
                 NoRed)), c4))
             in
             T (pk3, e3, c5)
           | Ok_lrt (_, _, _, t) ->
             (match make_right Datatypes.O pk2 e2 (Mix (SomeGreen, NoYellow,
                      NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
                      NoRed)) c4 with
              | Not_enough (_, _, v) ->
                let NE_chain (_, pk3, _, e3, _, _, c5) =
                  inject_vector Datatypes.O (S (S (S (S (S (S
                    Datatypes.O)))))) pk1 (Mix (SomeGreen, NoYellow,
                    NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
                    NoRed)) (NE_chain (Datatypes.O, pk1, Only, e1, (Mix
                    (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
                    NoYellow, NoOrange, NoRed)), c3)) v
                in
                T (pk3, e3, c5)
              | Ok_lrt (_, _, _, t0) ->
                T (Pair, Not_end, (Pair_chain (Datatypes.O, (Mix (SomeGreen,
                  NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
                  NoOrange, NoRed)),
                  (chain_of_triple Datatypes.O Left (Mix (SomeGreen,
                    NoYellow, NoOrange, NoRed)) t),
                  (chain_of_triple Datatypes.O Right (Mix (SomeGreen,
                    NoYellow, NoOrange, NoRed)) t0)))))) hind)
    and _f9 _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_graph_refinement_1 (pk1, e1, c3, v, pk2, e2, c4,
                                              hind) ->
      f0 __ pk1 e1 c3 v __ pk2 e2 c4 hind
        (_f10 __ pk1 e1 c3 v __ pk2 e2 c4
          (push_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk2
            (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)) v (NE_chain (Datatypes.O, pk2, Only,
            e2, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
            (SomeGreen, NoYellow, NoOrange, NoRed)), c4)))
          (let NE_chain (_, pk3, _, e3, _, _, c5) =
             push_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk2
               (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)) v (NE_chain (Datatypes.O, pk2,
               Only, e2, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
               (SomeGreen, NoYellow, NoOrange, NoRed)), c4))
           in
           T (pk3, e3, c5)) hind)
    | Coq_concat_clause_1_graph_refinement_2 (pk1, e1, c3, tl0, pk2, e2, c4,
                                              hind) ->
      f1 __ pk1 e1 c3 tl0 __ pk2 e2 c4 hind
        (_f11 __ pk1 e1 c3 tl0 __ pk2 e2 c4
          (make_right Datatypes.O pk2 e2 (Mix (SomeGreen, NoYellow, NoOrange,
            NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c4)
          (match make_right Datatypes.O pk2 e2 (Mix (SomeGreen, NoYellow,
                   NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
                   NoRed)) c4 with
           | Not_enough (_, _, v) ->
             let NE_chain (_, pk3, _, e3, _, _, c5) =
               inject_vector Datatypes.O (S (S (S (S (S (S Datatypes.O))))))
                 pk1 (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix
                 (SomeGreen, NoYellow, NoOrange, NoRed)) (NE_chain
                 (Datatypes.O, pk1, Only, e1, (Mix (SomeGreen, NoYellow,
                 NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
                 NoRed)), c3)) v
             in
             T (pk3, e3, c5)
           | Ok_lrt (_, _, _, t) ->
             T (Pair, Not_end, (Pair_chain (Datatypes.O, (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
               NoOrange, NoRed)),
               (chain_of_triple Datatypes.O Left (Mix (SomeGreen, NoYellow,
                 NoOrange, NoRed)) tl0),
               (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
                 NoOrange, NoRed)) t))))) hind)
    and _f10 _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_1_graph_equation_1 (pk1, e1, c3, v, pk2, e2,
                                                     c4, e3, c5) ->
      f2 __ pk1 e1 c3 v __ pk2 e2 c4 e3 c5 __
    and _f11 _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_graph_refinement_1 (pk1, e1, c3, tl0, pk2,
                                                       e2, c4, v, hind) ->
      f3 __ pk1 e1 c3 tl0 __ pk2 e2 c4 v __ hind
        (_f12 __ pk1 e1 c3 tl0 __ pk2 e2 c4 v
          (inject_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk1
            (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)) (NE_chain (Datatypes.O, pk1, Only,
            e1, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
            (SomeGreen, NoYellow, NoOrange, NoRed)), c3)) v) __
          (let NE_chain (_, pk3, _, e3, _, _, c5) =
             inject_vector Datatypes.O (S (S (S (S (S (S Datatypes.O))))))
               pk1 (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix
               (SomeGreen, NoYellow, NoOrange, NoRed)) (NE_chain
               (Datatypes.O, pk1, Only, e1, (Mix (SomeGreen, NoYellow,
               NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
               NoRed)), c3)) v
           in
           T (pk3, e3, c5)) hind)
    | Coq_concat_clause_1_clause_2_graph_refinement_2 (pk1, e1, c3, tl0, pk2,
                                                       e2, c4, tr0, hind) ->
      f4 __ pk1 e1 c3 tl0 __ pk2 e2 c4 tr0 __ hind
        (Obj.magic f13 pk1 e1 c3 tl0
          (chain_of_triple Datatypes.O Left (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tl0) pk2 e2 c4 tr0 (T (Pair, Not_end,
          (Pair_chain (Datatypes.O, (Mix (SomeGreen, NoYellow, NoOrange,
          NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
          (chain_of_triple Datatypes.O Left (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tl0),
          (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tr0))))) hind)
    and _f12 _ _ _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_clause_1_graph_equation_1 (pk1, e1, c3,
                                                              tl0, pk2, e2,
                                                              c4, v, e4, c5) ->
      f5 __ pk1 e1 c3 tl0 __ pk2 e2 c4 v e4 c5 __ __
    and f13 _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_clause_2_graph_refinement_1 (pk1, e1, c3,
                                                                tl0, refine0,
                                                                pk2, e2, c4,
                                                                tr0, hind) ->
      Obj.magic f6 __ pk1 e1 c3 tl0 refine0 __ pk2 e2 c4 tr0 __ hind
        (f14 __ pk1 e1 c3 tl0 refine0 __ pk2 e2 c4 tr0
          (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tr0) __ (T (Pair, Not_end, (Pair_chain
          (Datatypes.O, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
          (SomeGreen, NoYellow, NoOrange, NoRed)), refine0,
          (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tr0))))) hind)
    and f14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_clause_2_clause_1_graph_equation_1 (
        pk1, e1, c3, tl0, cl, pk2, e2, c4, tr0, cr) ->
      Obj.magic f7 __ pk1 e1 c3 tl0 cl __ __ pk2 e2 c4 tr0 cr __ __
    in f13 pk e c1 tl refine pk0 e0 c2 tr s c

  (** val concat_clause_1_clause_2_clause_1_graph_mut :
      (__ -> kind -> ending -> __ chain -> kind -> ending -> __ chain -> __
      concat_clause_1_graph -> 'a2 -> 'a1) -> (__ -> kind -> ending -> __
      chain -> __ stored_triple vector -> __ -> kind -> ending -> __ chain ->
      __ concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> kind ->
      ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain ->
      __ concat_clause_1_clause_2_graph -> 'a4 -> 'a2) -> (__ -> kind ->
      ending -> __ chain -> __ stored_triple vector -> __ -> kind -> ending
      -> __ chain -> ending -> __ chain -> __ -> 'a3) -> (__ -> kind ->
      ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain ->
      __ stored_triple vector -> __ -> __
      concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> kind
      -> ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain
      -> __ triple -> __ -> __ concat_clause_1_clause_2_clause_2_graph -> 'a6
      -> 'a4) -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind
      -> ending -> __ chain -> __ stored_triple vector -> ending -> __ chain
      -> __ -> __ -> 'a5) -> (__ -> kind -> ending -> __ chain -> __ triple
      -> __ chain -> __ -> kind -> ending -> __ chain -> __ triple -> __ ->
      __ concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 -> 'a6) ->
      (__ -> kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __
      -> kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ ->
      'a7) -> kind -> ending -> 'a8 chain -> 'a8 triple -> kind -> ending ->
      'a8 chain -> 'a8 stored_triple vector -> 'a8 non_ending_chain -> 'a8
      deque -> 'a8 concat_clause_1_clause_2_clause_1_graph -> 'a5 **)

  let concat_clause_1_clause_2_clause_1_graph_mut _ _ _ _ _ _ f5 _ _ _ _ _ _ _ _ _ _ _ _ = function
  | Coq_concat_clause_1_clause_2_clause_1_graph_equation_1 (pk1, e, c1, tl,
                                                            pk0, e0, c2, v,
                                                            e4, c3) ->
    Obj.magic f5 __ pk1 e c1 tl __ pk0 e0 c2 v e4 c3 __ __

  (** val concat_clause_1_clause_2_graph_mut :
      (__ -> kind -> ending -> __ chain -> kind -> ending -> __ chain -> __
      concat_clause_1_graph -> 'a2 -> 'a1) -> (__ -> kind -> ending -> __
      chain -> __ stored_triple vector -> __ -> kind -> ending -> __ chain ->
      __ concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> kind ->
      ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain ->
      __ concat_clause_1_clause_2_graph -> 'a4 -> 'a2) -> (__ -> kind ->
      ending -> __ chain -> __ stored_triple vector -> __ -> kind -> ending
      -> __ chain -> ending -> __ chain -> __ -> 'a3) -> (__ -> kind ->
      ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain ->
      __ stored_triple vector -> __ -> __
      concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> kind
      -> ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain
      -> __ triple -> __ -> __ concat_clause_1_clause_2_clause_2_graph -> 'a6
      -> 'a4) -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind
      -> ending -> __ chain -> __ stored_triple vector -> ending -> __ chain
      -> __ -> __ -> 'a5) -> (__ -> kind -> ending -> __ chain -> __ triple
      -> __ chain -> __ -> kind -> ending -> __ chain -> __ triple -> __ ->
      __ concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 -> 'a6) ->
      (__ -> kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __
      -> kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ ->
      'a7) -> kind -> ending -> 'a8 chain -> 'a8 triple -> kind -> ending ->
      'a8 chain -> 'a8 left_right_triple -> 'a8 deque -> 'a8
      concat_clause_1_clause_2_graph -> 'a4 **)

  let concat_clause_1_clause_2_graph_mut f f0 f1 f2 f3 f4 f5 f6 f7 pk e c1 tl pk0 e0 c2 refine s c =
    let rec _f8 _ _ _ _ = function
    | Coq_concat_graph_refinement_1 (pk1, e1, c3, pk2, e2, c4, hind) ->
      f __ pk1 e1 c3 pk2 e2 c4 hind
        (_f9 __ pk1 e1 c3
          (make_left Datatypes.O pk1 e1 (Mix (SomeGreen, NoYellow, NoOrange,
            NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c3) pk2 e2
          c4
          (match make_left Datatypes.O pk1 e1 (Mix (SomeGreen, NoYellow,
                   NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
                   NoRed)) c3 with
           | Not_enough (_, _, v) ->
             let NE_chain (_, pk3, _, e3, _, _, c5) =
               push_vector Datatypes.O (S (S (S (S (S (S Datatypes.O))))))
                 pk2 (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix
                 (SomeGreen, NoYellow, NoOrange, NoRed)) v (NE_chain
                 (Datatypes.O, pk2, Only, e2, (Mix (SomeGreen, NoYellow,
                 NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
                 NoRed)), c4))
             in
             T (pk3, e3, c5)
           | Ok_lrt (_, _, _, t) ->
             (match make_right Datatypes.O pk2 e2 (Mix (SomeGreen, NoYellow,
                      NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
                      NoRed)) c4 with
              | Not_enough (_, _, v) ->
                let NE_chain (_, pk3, _, e3, _, _, c5) =
                  inject_vector Datatypes.O (S (S (S (S (S (S
                    Datatypes.O)))))) pk1 (Mix (SomeGreen, NoYellow,
                    NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
                    NoRed)) (NE_chain (Datatypes.O, pk1, Only, e1, (Mix
                    (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
                    NoYellow, NoOrange, NoRed)), c3)) v
                in
                T (pk3, e3, c5)
              | Ok_lrt (_, _, _, t0) ->
                T (Pair, Not_end, (Pair_chain (Datatypes.O, (Mix (SomeGreen,
                  NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
                  NoOrange, NoRed)),
                  (chain_of_triple Datatypes.O Left (Mix (SomeGreen,
                    NoYellow, NoOrange, NoRed)) t),
                  (chain_of_triple Datatypes.O Right (Mix (SomeGreen,
                    NoYellow, NoOrange, NoRed)) t0)))))) hind)
    and _f9 _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_graph_refinement_1 (pk1, e1, c3, v, pk2, e2, c4,
                                              hind) ->
      f0 __ pk1 e1 c3 v __ pk2 e2 c4 hind
        (_f10 __ pk1 e1 c3 v __ pk2 e2 c4
          (push_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk2
            (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)) v (NE_chain (Datatypes.O, pk2, Only,
            e2, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
            (SomeGreen, NoYellow, NoOrange, NoRed)), c4)))
          (let NE_chain (_, pk3, _, e3, _, _, c5) =
             push_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk2
               (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)) v (NE_chain (Datatypes.O, pk2,
               Only, e2, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
               (SomeGreen, NoYellow, NoOrange, NoRed)), c4))
           in
           T (pk3, e3, c5)) hind)
    | Coq_concat_clause_1_graph_refinement_2 (pk1, e1, c3, tl0, pk2, e2, c4,
                                              hind) ->
      f1 __ pk1 e1 c3 tl0 __ pk2 e2 c4 hind
        (Obj.magic f11 pk1 e1 c3 tl0 pk2 e2 c4
          (make_right Datatypes.O pk2 e2 (Mix (SomeGreen, NoYellow, NoOrange,
            NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c4)
          (match make_right Datatypes.O pk2 e2 (Mix (SomeGreen, NoYellow,
                   NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
                   NoRed)) c4 with
           | Not_enough (_, _, v) ->
             let NE_chain (_, pk3, _, e3, _, _, c5) =
               inject_vector Datatypes.O (S (S (S (S (S (S Datatypes.O))))))
                 pk1 (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix
                 (SomeGreen, NoYellow, NoOrange, NoRed)) (NE_chain
                 (Datatypes.O, pk1, Only, e1, (Mix (SomeGreen, NoYellow,
                 NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
                 NoRed)), c3)) v
             in
             T (pk3, e3, c5)
           | Ok_lrt (_, _, _, t) ->
             T (Pair, Not_end, (Pair_chain (Datatypes.O, (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
               NoOrange, NoRed)),
               (chain_of_triple Datatypes.O Left (Mix (SomeGreen, NoYellow,
                 NoOrange, NoRed)) tl0),
               (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
                 NoOrange, NoRed)) t))))) hind)
    and _f10 _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_1_graph_equation_1 (pk1, e1, c3, v, pk2, e2,
                                                     c4, e3, c5) ->
      f2 __ pk1 e1 c3 v __ pk2 e2 c4 e3 c5 __
    and f11 _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_graph_refinement_1 (pk1, e1, c3, tl0, pk2,
                                                       e2, c4, v, hind) ->
      Obj.magic f3 __ pk1 e1 c3 tl0 __ pk2 e2 c4 v __ hind
        (f12 __ pk1 e1 c3 tl0 __ pk2 e2 c4 v
          (inject_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk1
            (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)) (NE_chain (Datatypes.O, pk1, Only,
            e1, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
            (SomeGreen, NoYellow, NoOrange, NoRed)), c3)) v) __
          (let NE_chain (_, pk3, _, e3, _, _, c5) =
             inject_vector Datatypes.O (S (S (S (S (S (S Datatypes.O))))))
               pk1 (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix
               (SomeGreen, NoYellow, NoOrange, NoRed)) (NE_chain
               (Datatypes.O, pk1, Only, e1, (Mix (SomeGreen, NoYellow,
               NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
               NoRed)), c3)) v
           in
           T (pk3, e3, c5)) hind)
    | Coq_concat_clause_1_clause_2_graph_refinement_2 (pk1, e1, c3, tl0, pk2,
                                                       e2, c4, tr, hind) ->
      Obj.magic f4 __ pk1 e1 c3 tl0 __ pk2 e2 c4 tr __ hind
        (f13 __ pk1 e1 c3 tl0
          (chain_of_triple Datatypes.O Left (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tl0) __ pk2 e2 c4 tr __ (T (Pair, Not_end,
          (Pair_chain (Datatypes.O, (Mix (SomeGreen, NoYellow, NoOrange,
          NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
          (chain_of_triple Datatypes.O Left (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tl0),
          (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tr))))) hind)
    and f12 _ _ _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_clause_1_graph_equation_1 (pk1, e1, c3,
                                                              tl0, pk2, e2,
                                                              c4, v, e4, c5) ->
      Obj.magic f5 __ pk1 e1 c3 tl0 __ pk2 e2 c4 v e4 c5 __ __
    and f13 _ _ _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_clause_2_graph_refinement_1 (pk1, e1, c3,
                                                                tl0, refine0,
                                                                pk2, e2, c4,
                                                                tr, hind) ->
      Obj.magic f6 __ pk1 e1 c3 tl0 refine0 __ pk2 e2 c4 tr __ hind
        (f14 __ pk1 e1 c3 tl0 refine0 __ pk2 e2 c4 tr
          (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tr) __ (T (Pair, Not_end, (Pair_chain
          (Datatypes.O, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
          (SomeGreen, NoYellow, NoOrange, NoRed)), refine0,
          (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tr))))) hind)
    and f14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_clause_2_clause_1_graph_equation_1 (
        pk1, e1, c3, tl0, cl, pk2, e2, c4, tr, cr) ->
      Obj.magic f7 __ pk1 e1 c3 tl0 cl __ __ pk2 e2 c4 tr cr __ __
    in f11 pk e c1 tl pk0 e0 c2 refine s c

  (** val concat_clause_1_clause_1_graph_mut :
      (__ -> kind -> ending -> __ chain -> kind -> ending -> __ chain -> __
      concat_clause_1_graph -> 'a2 -> 'a1) -> (__ -> kind -> ending -> __
      chain -> __ stored_triple vector -> __ -> kind -> ending -> __ chain ->
      __ concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> kind ->
      ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain ->
      __ concat_clause_1_clause_2_graph -> 'a4 -> 'a2) -> (__ -> kind ->
      ending -> __ chain -> __ stored_triple vector -> __ -> kind -> ending
      -> __ chain -> ending -> __ chain -> __ -> 'a3) -> (__ -> kind ->
      ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain ->
      __ stored_triple vector -> __ -> __
      concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> kind
      -> ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain
      -> __ triple -> __ -> __ concat_clause_1_clause_2_clause_2_graph -> 'a6
      -> 'a4) -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind
      -> ending -> __ chain -> __ stored_triple vector -> ending -> __ chain
      -> __ -> __ -> 'a5) -> (__ -> kind -> ending -> __ chain -> __ triple
      -> __ chain -> __ -> kind -> ending -> __ chain -> __ triple -> __ ->
      __ concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 -> 'a6) ->
      (__ -> kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __
      -> kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ ->
      'a7) -> kind -> ending -> 'a8 chain -> 'a8 stored_triple vector -> kind
      -> ending -> 'a8 chain -> 'a8 non_ending_chain -> 'a8 deque -> 'a8
      concat_clause_1_clause_1_graph -> 'a3 **)

  let concat_clause_1_clause_1_graph_mut _ _ _ f2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ = function
  | Coq_concat_clause_1_clause_1_graph_equation_1 (pk, e, c1, v, pk1, e0, c2,
                                                   e3, c3) ->
    Obj.magic f2 __ pk e c1 v __ pk1 e0 c2 e3 c3 __

  (** val concat_clause_1_graph_mut :
      (__ -> kind -> ending -> __ chain -> kind -> ending -> __ chain -> __
      concat_clause_1_graph -> 'a2 -> 'a1) -> (__ -> kind -> ending -> __
      chain -> __ stored_triple vector -> __ -> kind -> ending -> __ chain ->
      __ concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> kind ->
      ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain ->
      __ concat_clause_1_clause_2_graph -> 'a4 -> 'a2) -> (__ -> kind ->
      ending -> __ chain -> __ stored_triple vector -> __ -> kind -> ending
      -> __ chain -> ending -> __ chain -> __ -> 'a3) -> (__ -> kind ->
      ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain ->
      __ stored_triple vector -> __ -> __
      concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> kind
      -> ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain
      -> __ triple -> __ -> __ concat_clause_1_clause_2_clause_2_graph -> 'a6
      -> 'a4) -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind
      -> ending -> __ chain -> __ stored_triple vector -> ending -> __ chain
      -> __ -> __ -> 'a5) -> (__ -> kind -> ending -> __ chain -> __ triple
      -> __ chain -> __ -> kind -> ending -> __ chain -> __ triple -> __ ->
      __ concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 -> 'a6) ->
      (__ -> kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __
      -> kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ ->
      'a7) -> kind -> ending -> 'a8 chain -> 'a8 left_right_triple -> kind ->
      ending -> 'a8 chain -> 'a8 deque -> 'a8 concat_clause_1_graph -> 'a2 **)

  let concat_clause_1_graph_mut f f0 f1 f2 f3 f4 f5 f6 f7 pk e c1 refine pk0 e0 c2 s c =
    let rec _f8 _ _ _ _ = function
    | Coq_concat_graph_refinement_1 (pk1, e1, c3, pk2, e2, c4, hind) ->
      Obj.magic f __ pk1 e1 c3 pk2 e2 c4 hind
        (f9 pk1 e1 c3
          (make_left Datatypes.O pk1 e1 (Mix (SomeGreen, NoYellow, NoOrange,
            NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c3) pk2 e2
          c4
          (match make_left Datatypes.O pk1 e1 (Mix (SomeGreen, NoYellow,
                   NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
                   NoRed)) c3 with
           | Not_enough (_, _, v) ->
             let NE_chain (_, pk3, _, e3, _, _, c5) =
               push_vector Datatypes.O (S (S (S (S (S (S Datatypes.O))))))
                 pk2 (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix
                 (SomeGreen, NoYellow, NoOrange, NoRed)) v (NE_chain
                 (Datatypes.O, pk2, Only, e2, (Mix (SomeGreen, NoYellow,
                 NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
                 NoRed)), c4))
             in
             T (pk3, e3, c5)
           | Ok_lrt (_, _, _, t) ->
             (match make_right Datatypes.O pk2 e2 (Mix (SomeGreen, NoYellow,
                      NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
                      NoRed)) c4 with
              | Not_enough (_, _, v) ->
                let NE_chain (_, pk3, _, e3, _, _, c5) =
                  inject_vector Datatypes.O (S (S (S (S (S (S
                    Datatypes.O)))))) pk1 (Mix (SomeGreen, NoYellow,
                    NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
                    NoRed)) (NE_chain (Datatypes.O, pk1, Only, e1, (Mix
                    (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
                    NoYellow, NoOrange, NoRed)), c3)) v
                in
                T (pk3, e3, c5)
              | Ok_lrt (_, _, _, t0) ->
                T (Pair, Not_end, (Pair_chain (Datatypes.O, (Mix (SomeGreen,
                  NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
                  NoOrange, NoRed)),
                  (chain_of_triple Datatypes.O Left (Mix (SomeGreen,
                    NoYellow, NoOrange, NoRed)) t),
                  (chain_of_triple Datatypes.O Right (Mix (SomeGreen,
                    NoYellow, NoOrange, NoRed)) t0)))))) hind)
    and f9 _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_graph_refinement_1 (pk1, e1, c3, v, pk2, e2, c4,
                                              hind) ->
      Obj.magic f0 __ pk1 e1 c3 v __ pk2 e2 c4 hind
        (f10 __ pk1 e1 c3 v __ pk2 e2 c4
          (push_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk2
            (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)) v (NE_chain (Datatypes.O, pk2, Only,
            e2, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
            (SomeGreen, NoYellow, NoOrange, NoRed)), c4)))
          (let NE_chain (_, pk3, _, e3, _, _, c5) =
             push_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk2
               (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)) v (NE_chain (Datatypes.O, pk2,
               Only, e2, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
               (SomeGreen, NoYellow, NoOrange, NoRed)), c4))
           in
           T (pk3, e3, c5)) hind)
    | Coq_concat_clause_1_graph_refinement_2 (pk1, e1, c3, tl, pk2, e2, c4,
                                              hind) ->
      Obj.magic f1 __ pk1 e1 c3 tl __ pk2 e2 c4 hind
        (f11 __ pk1 e1 c3 tl __ pk2 e2 c4
          (make_right Datatypes.O pk2 e2 (Mix (SomeGreen, NoYellow, NoOrange,
            NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c4)
          (match make_right Datatypes.O pk2 e2 (Mix (SomeGreen, NoYellow,
                   NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
                   NoRed)) c4 with
           | Not_enough (_, _, v) ->
             let NE_chain (_, pk3, _, e3, _, _, c5) =
               inject_vector Datatypes.O (S (S (S (S (S (S Datatypes.O))))))
                 pk1 (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix
                 (SomeGreen, NoYellow, NoOrange, NoRed)) (NE_chain
                 (Datatypes.O, pk1, Only, e1, (Mix (SomeGreen, NoYellow,
                 NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
                 NoRed)), c3)) v
             in
             T (pk3, e3, c5)
           | Ok_lrt (_, _, _, t) ->
             T (Pair, Not_end, (Pair_chain (Datatypes.O, (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
               NoOrange, NoRed)),
               (chain_of_triple Datatypes.O Left (Mix (SomeGreen, NoYellow,
                 NoOrange, NoRed)) tl),
               (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
                 NoOrange, NoRed)) t))))) hind)
    and f10 _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_1_graph_equation_1 (pk1, e1, c3, v, pk2, e2,
                                                     c4, e3, c5) ->
      Obj.magic f2 __ pk1 e1 c3 v __ pk2 e2 c4 e3 c5 __
    and f11 _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_graph_refinement_1 (pk1, e1, c3, tl, pk2,
                                                       e2, c4, v, hind) ->
      Obj.magic f3 __ pk1 e1 c3 tl __ pk2 e2 c4 v __ hind
        (f12 __ pk1 e1 c3 tl __ pk2 e2 c4 v
          (inject_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk1
            (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)) (NE_chain (Datatypes.O, pk1, Only,
            e1, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
            (SomeGreen, NoYellow, NoOrange, NoRed)), c3)) v) __
          (let NE_chain (_, pk3, _, e3, _, _, c5) =
             inject_vector Datatypes.O (S (S (S (S (S (S Datatypes.O))))))
               pk1 (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix
               (SomeGreen, NoYellow, NoOrange, NoRed)) (NE_chain
               (Datatypes.O, pk1, Only, e1, (Mix (SomeGreen, NoYellow,
               NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
               NoRed)), c3)) v
           in
           T (pk3, e3, c5)) hind)
    | Coq_concat_clause_1_clause_2_graph_refinement_2 (pk1, e1, c3, tl, pk2,
                                                       e2, c4, tr, hind) ->
      Obj.magic f4 __ pk1 e1 c3 tl __ pk2 e2 c4 tr __ hind
        (f13 __ pk1 e1 c3 tl
          (chain_of_triple Datatypes.O Left (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tl) __ pk2 e2 c4 tr __ (T (Pair, Not_end,
          (Pair_chain (Datatypes.O, (Mix (SomeGreen, NoYellow, NoOrange,
          NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
          (chain_of_triple Datatypes.O Left (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tl),
          (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tr))))) hind)
    and f12 _ _ _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_clause_1_graph_equation_1 (pk1, e1, c3,
                                                              tl, pk2, e2,
                                                              c4, v, e4, c5) ->
      Obj.magic f5 __ pk1 e1 c3 tl __ pk2 e2 c4 v e4 c5 __ __
    and f13 _ _ _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_clause_2_graph_refinement_1 (pk1, e1, c3,
                                                                tl, refine0,
                                                                pk2, e2, c4,
                                                                tr, hind) ->
      Obj.magic f6 __ pk1 e1 c3 tl refine0 __ pk2 e2 c4 tr __ hind
        (f14 __ pk1 e1 c3 tl refine0 __ pk2 e2 c4 tr
          (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tr) __ (T (Pair, Not_end, (Pair_chain
          (Datatypes.O, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
          (SomeGreen, NoYellow, NoOrange, NoRed)), refine0,
          (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tr))))) hind)
    and f14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_clause_2_clause_1_graph_equation_1 (
        pk1, e1, c3, tl, cl, pk2, e2, c4, tr, cr) ->
      Obj.magic f7 __ pk1 e1 c3 tl cl __ __ pk2 e2 c4 tr cr __ __
    in f9 pk e c1 refine pk0 e0 c2 s c

  (** val concat_graph_mut :
      (__ -> kind -> ending -> __ chain -> kind -> ending -> __ chain -> __
      concat_clause_1_graph -> 'a2 -> 'a1) -> (__ -> kind -> ending -> __
      chain -> __ stored_triple vector -> __ -> kind -> ending -> __ chain ->
      __ concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> kind ->
      ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain ->
      __ concat_clause_1_clause_2_graph -> 'a4 -> 'a2) -> (__ -> kind ->
      ending -> __ chain -> __ stored_triple vector -> __ -> kind -> ending
      -> __ chain -> ending -> __ chain -> __ -> 'a3) -> (__ -> kind ->
      ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain ->
      __ stored_triple vector -> __ -> __
      concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> kind
      -> ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain
      -> __ triple -> __ -> __ concat_clause_1_clause_2_clause_2_graph -> 'a6
      -> 'a4) -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind
      -> ending -> __ chain -> __ stored_triple vector -> ending -> __ chain
      -> __ -> __ -> 'a5) -> (__ -> kind -> ending -> __ chain -> __ triple
      -> __ chain -> __ -> kind -> ending -> __ chain -> __ triple -> __ ->
      __ concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 -> 'a6) ->
      (__ -> kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __
      -> kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ ->
      'a7) -> 'a8 deque -> 'a8 deque -> 'a8 deque -> 'a8 concat_graph -> 'a1 **)

  let concat_graph_mut f f0 f1 f2 f3 f4 f5 f6 f7 d1 d2 s c =
    let rec f8 _ _ _ = function
    | Coq_concat_graph_refinement_1 (pk, e, c1, pk0, e0, c2, hind) ->
      Obj.magic f __ pk e c1 pk0 e0 c2 hind
        (f9 __ pk e c1
          (make_left Datatypes.O pk e (Mix (SomeGreen, NoYellow, NoOrange,
            NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c1) pk0 e0
          c2
          (match make_left Datatypes.O pk e (Mix (SomeGreen, NoYellow,
                   NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
                   NoRed)) c1 with
           | Not_enough (_, _, v) ->
             let NE_chain (_, pk1, _, e1, _, _, c3) =
               push_vector Datatypes.O (S (S (S (S (S (S Datatypes.O))))))
                 pk0 (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix
                 (SomeGreen, NoYellow, NoOrange, NoRed)) v (NE_chain
                 (Datatypes.O, pk0, Only, e0, (Mix (SomeGreen, NoYellow,
                 NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
                 NoRed)), c2))
             in
             T (pk1, e1, c3)
           | Ok_lrt (_, _, _, t) ->
             (match make_right Datatypes.O pk0 e0 (Mix (SomeGreen, NoYellow,
                      NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
                      NoRed)) c2 with
              | Not_enough (_, _, v) ->
                let NE_chain (_, pk1, _, e1, _, _, c3) =
                  inject_vector Datatypes.O (S (S (S (S (S (S
                    Datatypes.O)))))) pk (Mix (SomeGreen, NoYellow, NoOrange,
                    NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
                    (NE_chain (Datatypes.O, pk, Only, e, (Mix (SomeGreen,
                    NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
                    NoOrange, NoRed)), c1)) v
                in
                T (pk1, e1, c3)
              | Ok_lrt (_, _, _, t0) ->
                T (Pair, Not_end, (Pair_chain (Datatypes.O, (Mix (SomeGreen,
                  NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
                  NoOrange, NoRed)),
                  (chain_of_triple Datatypes.O Left (Mix (SomeGreen,
                    NoYellow, NoOrange, NoRed)) t),
                  (chain_of_triple Datatypes.O Right (Mix (SomeGreen,
                    NoYellow, NoOrange, NoRed)) t0)))))) hind)
    and f9 _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_graph_refinement_1 (pk, e, c1, v, pk0, e0, c2, hind) ->
      Obj.magic f0 __ pk e c1 v __ pk0 e0 c2 hind
        (f10 __ pk e c1 v __ pk0 e0 c2
          (push_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk0
            (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)) v (NE_chain (Datatypes.O, pk0, Only,
            e0, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
            (SomeGreen, NoYellow, NoOrange, NoRed)), c2)))
          (let NE_chain (_, pk1, _, e1, _, _, c3) =
             push_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk0
               (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)) v (NE_chain (Datatypes.O, pk0,
               Only, e0, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
               (SomeGreen, NoYellow, NoOrange, NoRed)), c2))
           in
           T (pk1, e1, c3)) hind)
    | Coq_concat_clause_1_graph_refinement_2 (pk, e, c1, tl, pk0, e0, c2, hind) ->
      Obj.magic f1 __ pk e c1 tl __ pk0 e0 c2 hind
        (f11 __ pk e c1 tl __ pk0 e0 c2
          (make_right Datatypes.O pk0 e0 (Mix (SomeGreen, NoYellow, NoOrange,
            NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c2)
          (match make_right Datatypes.O pk0 e0 (Mix (SomeGreen, NoYellow,
                   NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange,
                   NoRed)) c2 with
           | Not_enough (_, _, v) ->
             let NE_chain (_, pk1, _, e1, _, _, c3) =
               inject_vector Datatypes.O (S (S (S (S (S (S Datatypes.O))))))
                 pk (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix
                 (SomeGreen, NoYellow, NoOrange, NoRed)) (NE_chain
                 (Datatypes.O, pk, Only, e, (Mix (SomeGreen, NoYellow,
                 NoOrange, NoRed)), (Mix (SomeGreen, NoYellow, NoOrange,
                 NoRed)), c1)) v
             in
             T (pk1, e1, c3)
           | Ok_lrt (_, _, _, t) ->
             T (Pair, Not_end, (Pair_chain (Datatypes.O, (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
               NoOrange, NoRed)),
               (chain_of_triple Datatypes.O Left (Mix (SomeGreen, NoYellow,
                 NoOrange, NoRed)) tl),
               (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
                 NoOrange, NoRed)) t))))) hind)
    and f10 _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_1_graph_equation_1 (pk, e, c1, v, pk1, e0,
                                                     c2, e3, c3) ->
      Obj.magic f2 __ pk e c1 v __ pk1 e0 c2 e3 c3 __
    and f11 _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_graph_refinement_1 (pk, e, c1, tl, pk0,
                                                       e0, c2, v, hind) ->
      Obj.magic f3 __ pk e c1 tl __ pk0 e0 c2 v __ hind
        (f12 __ pk e c1 tl __ pk0 e0 c2 v
          (inject_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk
            (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)) (NE_chain (Datatypes.O, pk, Only, e,
            (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)), c1)) v) __
          (let NE_chain (_, pk1, _, e1, _, _, c3) =
             inject_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk
               (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)) (NE_chain (Datatypes.O, pk, Only,
               e, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
               (SomeGreen, NoYellow, NoOrange, NoRed)), c1)) v
           in
           T (pk1, e1, c3)) hind)
    | Coq_concat_clause_1_clause_2_graph_refinement_2 (pk, e, c1, tl, pk0,
                                                       e0, c2, tr, hind) ->
      Obj.magic f4 __ pk e c1 tl __ pk0 e0 c2 tr __ hind
        (f13 __ pk e c1 tl
          (chain_of_triple Datatypes.O Left (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tl) __ pk0 e0 c2 tr __ (T (Pair, Not_end,
          (Pair_chain (Datatypes.O, (Mix (SomeGreen, NoYellow, NoOrange,
          NoRed)), (Mix (SomeGreen, NoYellow, NoOrange, NoRed)),
          (chain_of_triple Datatypes.O Left (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tl),
          (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tr))))) hind)
    and f12 _ _ _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_clause_1_graph_equation_1 (pk1, e, c1, tl,
                                                              pk0, e0, c2, v,
                                                              e4, c3) ->
      Obj.magic f5 __ pk1 e c1 tl __ pk0 e0 c2 v e4 c3 __ __
    and f13 _ _ _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_clause_2_graph_refinement_1 (pk, e, c1,
                                                                tl, refine,
                                                                pk0, e0, c2,
                                                                tr, hind) ->
      Obj.magic f6 __ pk e c1 tl refine __ pk0 e0 c2 tr __ hind
        (f14 __ pk e c1 tl refine __ pk0 e0 c2 tr
          (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tr) __ (T (Pair, Not_end, (Pair_chain
          (Datatypes.O, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
          (SomeGreen, NoYellow, NoOrange, NoRed)), refine,
          (chain_of_triple Datatypes.O Right (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) tr))))) hind)
    and f14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_clause_2_clause_1_graph_equation_1 (
        pk, e, c1, tl, cl, pk0, e0, c2, tr, cr) ->
      Obj.magic f7 __ pk e c1 tl cl __ __ pk0 e0 c2 tr cr __ __
    in f8 d1 d2 s c

  (** val concat_graph_rect :
      (__ -> kind -> ending -> __ chain -> kind -> ending -> __ chain -> __
      concat_clause_1_graph -> 'a2 -> 'a1) -> (__ -> kind -> ending -> __
      chain -> __ stored_triple vector -> __ -> kind -> ending -> __ chain ->
      __ concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> kind ->
      ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain ->
      __ concat_clause_1_clause_2_graph -> 'a4 -> 'a2) -> (__ -> kind ->
      ending -> __ chain -> __ stored_triple vector -> __ -> kind -> ending
      -> __ chain -> ending -> __ chain -> __ -> 'a3) -> (__ -> kind ->
      ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain ->
      __ stored_triple vector -> __ -> __
      concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> kind
      -> ending -> __ chain -> __ triple -> __ -> kind -> ending -> __ chain
      -> __ triple -> __ -> __ concat_clause_1_clause_2_clause_2_graph -> 'a6
      -> 'a4) -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind
      -> ending -> __ chain -> __ stored_triple vector -> ending -> __ chain
      -> __ -> __ -> 'a5) -> (__ -> kind -> ending -> __ chain -> __ triple
      -> __ chain -> __ -> kind -> ending -> __ chain -> __ triple -> __ ->
      __ concat_clause_1_clause_2_clause_2_clause_1_graph -> 'a7 -> 'a6) ->
      (__ -> kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __
      -> kind -> ending -> __ chain -> __ triple -> __ chain -> __ -> __ ->
      'a7) -> 'a8 deque -> 'a8 deque -> 'a8 deque -> 'a8 concat_graph -> 'a1 **)

  let concat_graph_rect =
    concat_graph_mut

  (** val concat_graph_correct :
      'a1 deque -> 'a1 deque -> 'a1 concat_graph **)

  let concat_graph_correct d1 d2 =
    let T (pk, e, c) = d1 in
    let T (pk0, e0, c0) = d2 in
    Coq_concat_graph_refinement_1 (pk, e, c, pk0, e0, c0,
    (let refine =
       make_left Datatypes.O pk e (Mix (SomeGreen, NoYellow, NoOrange,
         NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) c
     in
     match refine with
     | Not_enough (_, _, v) ->
       Coq_concat_clause_1_graph_refinement_1 (pk, e, c, v, pk0, e0, c0,
         (let refine0 =
            push_vector Datatypes.O (S (S (S (S (S (S Datatypes.O)))))) pk0
              (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (Mix (SomeGreen,
              NoYellow, NoOrange, NoRed)) v (NE_chain (Datatypes.O, pk0,
              Only, e0, (Mix (SomeGreen, NoYellow, NoOrange, NoRed)), (Mix
              (SomeGreen, NoYellow, NoOrange, NoRed)), c0))
          in
          let NE_chain (_, pk1, _, e1, _, _, c1) = refine0 in
          Coq_concat_clause_1_clause_1_graph_equation_1 (pk, e, c, v, pk1,
          e0, c0, e1, c1)))
     | Ok_lrt (_, _, _, t) ->
       Coq_concat_clause_1_graph_refinement_2 (pk, e, c, t, pk0, e0, c0,
         (let refine0 =
            make_right Datatypes.O pk0 e0 (Mix (SomeGreen, NoYellow,
              NoOrange, NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
              c0
          in
          match refine0 with
          | Not_enough (_, _, v) ->
            Coq_concat_clause_1_clause_2_graph_refinement_1 (pk, e, c, t,
              pk0, e0, c0, v,
              (let refine1 =
                 inject_vector Datatypes.O (S (S (S (S (S (S
                   Datatypes.O)))))) pk (Mix (SomeGreen, NoYellow, NoOrange,
                   NoRed)) (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
                   (NE_chain (Datatypes.O, pk, Only, e, (Mix (SomeGreen,
                   NoYellow, NoOrange, NoRed)), (Mix (SomeGreen, NoYellow,
                   NoOrange, NoRed)), c)) v
               in
               let NE_chain (_, pk1, _, e1, _, _, c1) = refine1 in
               Coq_concat_clause_1_clause_2_clause_1_graph_equation_1 (pk1,
               e, c, t, pk0, e0, c0, v, e1, c1)))
          | Ok_lrt (_, _, _, t0) ->
            Coq_concat_clause_1_clause_2_graph_refinement_2 (pk, e, c, t,
              pk0, e0, c0, t0,
              (let refine1 =
                 chain_of_triple Datatypes.O Left (Mix (SomeGreen, NoYellow,
                   NoOrange, NoRed)) t
               in
               Coq_concat_clause_1_clause_2_clause_2_graph_refinement_1 (pk,
               e, c, t, refine1, pk0, e0, c0, t0,
               (let refine2 =
                  chain_of_triple Datatypes.O Right (Mix (SomeGreen,
                    NoYellow, NoOrange, NoRed)) t0
                in
                Coq_concat_clause_1_clause_2_clause_2_clause_1_graph_equation_1
                (pk, e, c, t, refine1, pk0, e0, c0, t0, refine2)))))))))

  (** val concat_elim :
      (__ -> kind -> ending -> __ chain -> __ stored_triple vector -> __ ->
      kind -> ending -> __ chain -> ending -> __ chain -> __ -> __ -> __ ->
      'a1) -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind ->
      ending -> __ chain -> __ stored_triple vector -> ending -> __ chain ->
      __ -> __ -> __ -> __ -> __ -> 'a1) -> (__ -> kind -> ending -> __ chain
      -> __ triple -> __ chain -> __ -> __ -> kind -> ending -> __ chain ->
      __ triple -> __ chain -> __ -> __ -> __ -> __ -> __ -> __ -> 'a1) ->
      'a2 deque -> 'a2 deque -> 'a1 **)

  let concat_elim f2 f5 f7 d1 d2 =
    concat_graph_mut (fun _ _ _ _ _ _ _ _ x -> x __)
      (fun _ _ _ _ _ _ _ _ _ _ x -> x __) (fun _ _ _ _ _ _ _ _ _ _ x ->
      x __) f2 (fun _ _ _ _ _ _ _ _ _ _ _ _ x -> x __)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ x -> x __) f5
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x -> x __) f7 d1 d2 (concat d1 d2)
      (concat_graph_correct d1 d2)

  (** val coq_FunctionalElimination_concat :
      (__ -> kind -> ending -> __ chain -> __ stored_triple vector -> __ ->
      kind -> ending -> __ chain -> ending -> __ chain -> __ -> __ -> __ ->
      __) -> (__ -> kind -> ending -> __ chain -> __ triple -> __ -> kind ->
      ending -> __ chain -> __ stored_triple vector -> ending -> __ chain ->
      __ -> __ -> __ -> __ -> __ -> __) -> (__ -> kind -> ending -> __ chain
      -> __ triple -> __ chain -> __ -> __ -> kind -> ending -> __ chain ->
      __ triple -> __ chain -> __ -> __ -> __ -> __ -> __ -> __ -> __) -> __
      deque -> __ deque -> __ **)

  let coq_FunctionalElimination_concat =
    concat_elim

  (** val coq_FunctionalInduction_concat :
      (__ -> __ deque -> __ deque -> __ deque) coq_FunctionalInduction **)

  let coq_FunctionalInduction_concat =
    Obj.magic (fun _ -> concat_graph_correct)

  (** val pop_clause_2_clause_1 :
      kind -> 'a1 chain -> 'a1 -> kind -> ending -> color -> color -> 'a1
      chain -> 'a1 chain -> ('a1, 'a1 deque) prod option **)

  let pop_clause_2_clause_1 _ _ x pk0 e _ _ _ refine =
    Some (Coq_pair (x, (T (pk0, e, refine))))

  (** val pop_clause_2 :
      kind -> 'a1 chain -> ('a1 stored_triple, 'a1 semi_deque) prod -> ('a1,
      'a1 deque) prod option **)

  let pop_clause_2 _ _ = function
  | Coq_pair (s, s0) ->
    (match s with
     | Ground y ->
       let Semi (_, pk, e, cl, cr, c) = s0 in
       Some (Coq_pair (y, (T (pk, e,
       (ensure_green Datatypes.O pk Only e cl cr c)))))
     | _ -> assert false (* absurd case *))

  (** val pop : 'a1 deque -> ('a1, 'a1 deque) prod option **)

  let pop = function
  | T (pk, e, c) ->
    (match e with
     | Is_end ->
       (match c with
        | Empty _ -> None
        | _ -> assert false (* absurd case *))
     | Not_end ->
       let Coq_pair (s, s0) = pop_green Datatypes.O pk c in
       (match s with
        | Ground y ->
          let Semi (_, pk0, e0, cl, cr, c0) = s0 in
          Some (Coq_pair (y, (T (pk0, e0,
          (ensure_green Datatypes.O pk0 Only e0 cl cr c0)))))
        | _ -> assert false (* absurd case *)))

  type 'a pop_graph =
  | Coq_pop_graph_equation_1
  | Coq_pop_graph_refinement_2 of kind * 'a chain * 'a pop_clause_2_graph
  and 'a pop_clause_2_graph =
  | Coq_pop_clause_2_graph_refinement_1 of kind * 'a chain * 'a * kind
     * ending * color * color * 'a chain * 'a pop_clause_2_clause_1_graph
  and 'a0 pop_clause_2_clause_1_graph =
  | Coq_pop_clause_2_clause_1_graph_equation_1 of kind * 'a0 chain *
     'a0 * kind * ending * color * color * 'a0 chain * 'a0 chain

  (** val pop_clause_2_clause_1_graph_mut :
      (__ -> 'a1) -> (__ -> kind -> __ chain -> __ pop_clause_2_graph -> 'a2
      -> 'a1) -> (__ -> kind -> __ chain -> __ -> kind -> ending -> color ->
      color -> __ chain -> __ -> __ pop_clause_2_clause_1_graph -> 'a3 ->
      'a2) -> (__ -> kind -> __ chain -> __ -> kind -> ending -> color ->
      color -> __ chain -> __ chain -> __ -> __ -> 'a3) -> kind -> 'a4 chain
      -> 'a4 -> kind -> ending -> color -> color -> 'a4 chain -> 'a4 chain ->
      ('a4, 'a4 deque) prod option -> 'a4 pop_clause_2_clause_1_graph -> 'a3 **)

  let pop_clause_2_clause_1_graph_mut _ _ _ f2 _ _ _ _ _ _ _ _ _ _ = function
  | Coq_pop_clause_2_clause_1_graph_equation_1 (pk, c, x, pk0, e, cl, cr, c1,
                                                c2) ->
    Obj.magic f2 __ pk c x pk0 e cl cr c1 c2 __ __

  (** val pop_clause_2_graph_mut :
      (__ -> 'a1) -> (__ -> kind -> __ chain -> __ pop_clause_2_graph -> 'a2
      -> 'a1) -> (__ -> kind -> __ chain -> __ -> kind -> ending -> color ->
      color -> __ chain -> __ -> __ pop_clause_2_clause_1_graph -> 'a3 ->
      'a2) -> (__ -> kind -> __ chain -> __ -> kind -> ending -> color ->
      color -> __ chain -> __ chain -> __ -> __ -> 'a3) -> kind -> 'a4 chain
      -> ('a4 stored_triple, 'a4 semi_deque) prod -> ('a4, 'a4 deque) prod
      option -> 'a4 pop_clause_2_graph -> 'a2 **)

  let pop_clause_2_graph_mut f f0 f1 f2 pk c refine s p =
    let rec _f3 _ _ _ = function
    | Coq_pop_graph_equation_1 -> f __
    | Coq_pop_graph_refinement_2 (pk0, c0, hind) ->
      Obj.magic f0 __ pk0 c0 hind
        (f4 pk0 c0 (pop_green Datatypes.O pk0 c0)
          (let Coq_pair (s0, s1) = pop_green Datatypes.O pk0 c0 in
           (match s0 with
            | Ground y ->
              let Semi (_, pk1, e, cl, cr, c1) = s1 in
              Some (Coq_pair (y, (T (pk1, e,
              (ensure_green Datatypes.O pk1 Only e cl cr c1)))))
            | _ -> assert false (* absurd case *))) hind)
    and f4 _ _ _ _ = function
    | Coq_pop_clause_2_graph_refinement_1 (pk0, c0, x, pk1, e, cl, cr, c1,
                                           hind) ->
      Obj.magic f1 __ pk0 c0 x pk1 e cl cr c1 __ hind
        (f5 __ pk0 c0 x pk1 e cl cr c1
          (ensure_green Datatypes.O pk1 Only e cl cr c1) __ (Some (Coq_pair
          (x, (T (pk1, e, (ensure_green Datatypes.O pk1 Only e cl cr c1))))))
          hind)
    and f5 _ _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_pop_clause_2_clause_1_graph_equation_1 (pk0, c0, x, pk1, e, cl, cr,
                                                  c1, c2) ->
      Obj.magic f2 __ pk0 c0 x pk1 e cl cr c1 c2 __ __
    in f4 pk c refine s p

  (** val pop_graph_mut :
      (__ -> 'a1) -> (__ -> kind -> __ chain -> __ pop_clause_2_graph -> 'a2
      -> 'a1) -> (__ -> kind -> __ chain -> __ -> kind -> ending -> color ->
      color -> __ chain -> __ -> __ pop_clause_2_clause_1_graph -> 'a3 ->
      'a2) -> (__ -> kind -> __ chain -> __ -> kind -> ending -> color ->
      color -> __ chain -> __ chain -> __ -> __ -> 'a3) -> 'a4 deque -> ('a4,
      'a4 deque) prod option -> 'a4 pop_graph -> 'a1 **)

  let pop_graph_mut f f0 f1 f2 d s p =
    let rec f3 _ _ = function
    | Coq_pop_graph_equation_1 -> f __
    | Coq_pop_graph_refinement_2 (pk, c, hind) ->
      Obj.magic f0 __ pk c hind
        (f4 __ pk c (pop_green Datatypes.O pk c)
          (let Coq_pair (s0, s1) = pop_green Datatypes.O pk c in
           (match s0 with
            | Ground y ->
              let Semi (_, pk0, e, cl, cr, c0) = s1 in
              Some (Coq_pair (y, (T (pk0, e,
              (ensure_green Datatypes.O pk0 Only e cl cr c0)))))
            | _ -> assert false (* absurd case *))) hind)
    and f4 _ _ _ _ _ = function
    | Coq_pop_clause_2_graph_refinement_1 (pk, c, x, pk0, e, cl, cr, c1, hind) ->
      Obj.magic f1 __ pk c x pk0 e cl cr c1 __ hind
        (f5 __ pk c x pk0 e cl cr c1
          (ensure_green Datatypes.O pk0 Only e cl cr c1) __ (Some (Coq_pair
          (x, (T (pk0, e, (ensure_green Datatypes.O pk0 Only e cl cr c1))))))
          hind)
    and f5 _ _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_pop_clause_2_clause_1_graph_equation_1 (pk, c, x, pk0, e, cl, cr,
                                                  c1, c2) ->
      Obj.magic f2 __ pk c x pk0 e cl cr c1 c2 __ __
    in f3 d s p

  (** val pop_graph_rect :
      (__ -> 'a1) -> (__ -> kind -> __ chain -> __ pop_clause_2_graph -> 'a2
      -> 'a1) -> (__ -> kind -> __ chain -> __ -> kind -> ending -> color ->
      color -> __ chain -> __ -> __ pop_clause_2_clause_1_graph -> 'a3 ->
      'a2) -> (__ -> kind -> __ chain -> __ -> kind -> ending -> color ->
      color -> __ chain -> __ chain -> __ -> __ -> 'a3) -> 'a4 deque -> ('a4,
      'a4 deque) prod option -> 'a4 pop_graph -> 'a1 **)

  let pop_graph_rect =
    pop_graph_mut

  (** val pop_graph_correct : 'a1 deque -> 'a1 pop_graph **)

  let pop_graph_correct = function
  | T (pk, e, c) ->
    (match e with
     | Is_end ->
       (match c with
        | Empty _ -> Coq_pop_graph_equation_1
        | _ -> assert false (* absurd case *))
     | Not_end ->
       Coq_pop_graph_refinement_2 (pk, c,
         (let refine = pop_green Datatypes.O pk c in
          let Coq_pair (s, s0) = refine in
          (match s with
           | Ground y ->
             let Semi (_, pk0, e0, cl, cr, c0) = s0 in
             Coq_pop_clause_2_graph_refinement_1 (pk, c, y, pk0, e0, cl, cr,
             c0,
             (let refine0 = ensure_green Datatypes.O pk0 Only e0 cl cr c0 in
              Coq_pop_clause_2_clause_1_graph_equation_1 (pk, c, y, pk0, e0,
              cl, cr, c0, refine0)))
           | _ -> assert false (* absurd case *)))))

  (** val pop_elim :
      (__ -> 'a1) -> (__ -> kind -> __ chain -> __ -> kind -> ending -> color
      -> color -> __ chain -> __ chain -> __ -> __ -> __ -> __ -> 'a1) -> 'a2
      deque -> 'a1 **)

  let pop_elim f f2 d =
    pop_graph_mut f (fun _ _ _ _ x -> x __) (fun _ _ _ _ _ _ _ _ _ _ _ x ->
      x __) f2 d (pop d) (pop_graph_correct d)

  (** val coq_FunctionalElimination_pop :
      (__ -> __) -> (__ -> kind -> __ chain -> __ -> kind -> ending -> color
      -> color -> __ chain -> __ chain -> __ -> __ -> __ -> __ -> __) -> __
      deque -> __ **)

  let coq_FunctionalElimination_pop =
    pop_elim

  (** val coq_FunctionalInduction_pop :
      (__ -> __ deque -> (__, __ deque) prod option) coq_FunctionalInduction **)

  let coq_FunctionalInduction_pop =
    Obj.magic (fun _ -> pop_graph_correct)

  (** val eject_clause_2_clause_1 :
      kind -> 'a1 chain -> kind -> ending -> color -> color -> 'a1 chain ->
      'a1 chain -> 'a1 -> ('a1 deque, 'a1) prod option **)

  let eject_clause_2_clause_1 _ _ pk0 e _ _ _ refine x =
    Some (Coq_pair ((T (pk0, e, refine)), x))

  (** val eject_clause_2 :
      kind -> 'a1 chain -> ('a1 semi_deque, 'a1 stored_triple) prod -> ('a1
      deque, 'a1) prod option **)

  let eject_clause_2 _ _ = function
  | Coq_pair (s, s0) ->
    let Semi (_, pk, e, cl, cr, c) = s in
    (match s0 with
     | Ground y ->
       Some (Coq_pair ((T (pk, e,
         (ensure_green Datatypes.O pk Only e cl cr c))), y))
     | _ -> assert false (* absurd case *))

  (** val eject : 'a1 deque -> ('a1 deque, 'a1) prod option **)

  let eject = function
  | T (pk, e, c) ->
    (match e with
     | Is_end ->
       (match c with
        | Empty _ -> None
        | _ -> assert false (* absurd case *))
     | Not_end ->
       let Coq_pair (s, s0) = eject_green Datatypes.O pk c in
       let Semi (_, pk0, e0, cl, cr, c0) = s in
       (match s0 with
        | Ground y ->
          Some (Coq_pair ((T (pk0, e0,
            (ensure_green Datatypes.O pk0 Only e0 cl cr c0))), y))
        | _ -> assert false (* absurd case *)))

  type 'a eject_graph =
  | Coq_eject_graph_equation_1
  | Coq_eject_graph_refinement_2 of kind * 'a chain * 'a eject_clause_2_graph
  and 'a eject_clause_2_graph =
  | Coq_eject_clause_2_graph_refinement_1 of kind * 'a chain * kind *
     ending * color * color * 'a chain * 'a * 'a eject_clause_2_clause_1_graph
  and 'a0 eject_clause_2_clause_1_graph =
  | Coq_eject_clause_2_clause_1_graph_equation_1 of kind * 'a0 chain *
     kind * ending * color * color * 'a0 chain * 'a0 chain * 'a0

  (** val eject_clause_2_clause_1_graph_mut :
      (__ -> 'a1) -> (__ -> kind -> __ chain -> __ eject_clause_2_graph ->
      'a2 -> 'a1) -> (__ -> kind -> __ chain -> kind -> ending -> color ->
      color -> __ chain -> __ -> __ -> __ eject_clause_2_clause_1_graph ->
      'a3 -> 'a2) -> (__ -> kind -> __ chain -> kind -> ending -> color ->
      color -> __ chain -> __ chain -> __ -> __ -> __ -> 'a3) -> kind -> 'a4
      chain -> kind -> ending -> color -> color -> 'a4 chain -> 'a4 chain ->
      'a4 -> ('a4 deque, 'a4) prod option -> 'a4
      eject_clause_2_clause_1_graph -> 'a3 **)

  let eject_clause_2_clause_1_graph_mut _ _ _ f2 _ _ _ _ _ _ _ _ _ _ = function
  | Coq_eject_clause_2_clause_1_graph_equation_1 (pk, c, pk0, e, cl, cr, c1,
                                                  c2, x) ->
    Obj.magic f2 __ pk c pk0 e cl cr c1 c2 __ x __

  (** val eject_clause_2_graph_mut :
      (__ -> 'a1) -> (__ -> kind -> __ chain -> __ eject_clause_2_graph ->
      'a2 -> 'a1) -> (__ -> kind -> __ chain -> kind -> ending -> color ->
      color -> __ chain -> __ -> __ -> __ eject_clause_2_clause_1_graph ->
      'a3 -> 'a2) -> (__ -> kind -> __ chain -> kind -> ending -> color ->
      color -> __ chain -> __ chain -> __ -> __ -> __ -> 'a3) -> kind -> 'a4
      chain -> ('a4 semi_deque, 'a4 stored_triple) prod -> ('a4 deque, 'a4)
      prod option -> 'a4 eject_clause_2_graph -> 'a2 **)

  let eject_clause_2_graph_mut f f0 f1 f2 pk c refine s e =
    let rec _f3 _ _ _ = function
    | Coq_eject_graph_equation_1 -> f __
    | Coq_eject_graph_refinement_2 (pk0, c0, hind) ->
      Obj.magic f0 __ pk0 c0 hind
        (f4 pk0 c0 (eject_green Datatypes.O pk0 c0)
          (let Coq_pair (s0, s1) = eject_green Datatypes.O pk0 c0 in
           let Semi (_, pk1, e1, cl, cr, c1) = s0 in
           (match s1 with
            | Ground y ->
              Some (Coq_pair ((T (pk1, e1,
                (ensure_green Datatypes.O pk1 Only e1 cl cr c1))), y))
            | _ -> assert false (* absurd case *))) hind)
    and f4 _ _ _ _ = function
    | Coq_eject_clause_2_graph_refinement_1 (pk0, c0, pk1, e1, cl, cr, c1, x,
                                             hind) ->
      Obj.magic f1 __ pk0 c0 pk1 e1 cl cr c1 x __ hind
        (f5 __ pk0 c0 pk1 e1 cl cr c1
          (ensure_green Datatypes.O pk1 Only e1 cl cr c1) x __ (Some
          (Coq_pair ((T (pk1, e1,
          (ensure_green Datatypes.O pk1 Only e1 cl cr c1))), x))) hind)
    and f5 _ _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_eject_clause_2_clause_1_graph_equation_1 (pk0, c0, pk1, e1, cl, cr,
                                                    c1, c2, x) ->
      Obj.magic f2 __ pk0 c0 pk1 e1 cl cr c1 c2 __ x __
    in f4 pk c refine s e

  (** val eject_graph_mut :
      (__ -> 'a1) -> (__ -> kind -> __ chain -> __ eject_clause_2_graph ->
      'a2 -> 'a1) -> (__ -> kind -> __ chain -> kind -> ending -> color ->
      color -> __ chain -> __ -> __ -> __ eject_clause_2_clause_1_graph ->
      'a3 -> 'a2) -> (__ -> kind -> __ chain -> kind -> ending -> color ->
      color -> __ chain -> __ chain -> __ -> __ -> __ -> 'a3) -> 'a4 deque ->
      ('a4 deque, 'a4) prod option -> 'a4 eject_graph -> 'a1 **)

  let eject_graph_mut f f0 f1 f2 d s e =
    let rec f3 _ _ = function
    | Coq_eject_graph_equation_1 -> f __
    | Coq_eject_graph_refinement_2 (pk, c, hind) ->
      Obj.magic f0 __ pk c hind
        (f4 __ pk c (eject_green Datatypes.O pk c)
          (let Coq_pair (s0, s1) = eject_green Datatypes.O pk c in
           let Semi (_, pk0, e1, cl, cr, c0) = s0 in
           (match s1 with
            | Ground y ->
              Some (Coq_pair ((T (pk0, e1,
                (ensure_green Datatypes.O pk0 Only e1 cl cr c0))), y))
            | _ -> assert false (* absurd case *))) hind)
    and f4 _ _ _ _ _ = function
    | Coq_eject_clause_2_graph_refinement_1 (pk, c, pk0, e1, cl, cr, c1, x,
                                             hind) ->
      Obj.magic f1 __ pk c pk0 e1 cl cr c1 x __ hind
        (f5 __ pk c pk0 e1 cl cr c1
          (ensure_green Datatypes.O pk0 Only e1 cl cr c1) x __ (Some
          (Coq_pair ((T (pk0, e1,
          (ensure_green Datatypes.O pk0 Only e1 cl cr c1))), x))) hind)
    and f5 _ _ _ _ _ _ _ _ _ _ _ _ = function
    | Coq_eject_clause_2_clause_1_graph_equation_1 (pk, c, pk0, e1, cl, cr,
                                                    c1, c2, x) ->
      Obj.magic f2 __ pk c pk0 e1 cl cr c1 c2 __ x __
    in f3 d s e

  (** val eject_graph_rect :
      (__ -> 'a1) -> (__ -> kind -> __ chain -> __ eject_clause_2_graph ->
      'a2 -> 'a1) -> (__ -> kind -> __ chain -> kind -> ending -> color ->
      color -> __ chain -> __ -> __ -> __ eject_clause_2_clause_1_graph ->
      'a3 -> 'a2) -> (__ -> kind -> __ chain -> kind -> ending -> color ->
      color -> __ chain -> __ chain -> __ -> __ -> __ -> 'a3) -> 'a4 deque ->
      ('a4 deque, 'a4) prod option -> 'a4 eject_graph -> 'a1 **)

  let eject_graph_rect =
    eject_graph_mut

  (** val eject_graph_correct : 'a1 deque -> 'a1 eject_graph **)

  let eject_graph_correct = function
  | T (pk, e, c) ->
    (match e with
     | Is_end ->
       (match c with
        | Empty _ -> Coq_eject_graph_equation_1
        | _ -> assert false (* absurd case *))
     | Not_end ->
       Coq_eject_graph_refinement_2 (pk, c,
         (let refine = eject_green Datatypes.O pk c in
          let Coq_pair (s, s0) = refine in
          let Semi (_, pk0, e0, cl, cr, c0) = s in
          (match s0 with
           | Ground y ->
             Coq_eject_clause_2_graph_refinement_1 (pk, c, pk0, e0, cl, cr,
               c0, y,
               (let refine0 = ensure_green Datatypes.O pk0 Only e0 cl cr c0 in
                Coq_eject_clause_2_clause_1_graph_equation_1 (pk, c, pk0, e0,
                cl, cr, c0, refine0, y)))
           | _ -> assert false (* absurd case *)))))

  (** val eject_elim :
      (__ -> 'a1) -> (__ -> kind -> __ chain -> kind -> ending -> color ->
      color -> __ chain -> __ chain -> __ -> __ -> __ -> __ -> __ -> 'a1) ->
      'a2 deque -> 'a1 **)

  let eject_elim f f2 d =
    eject_graph_mut f (fun _ _ _ _ x -> x __) (fun _ _ _ _ _ _ _ _ _ _ _ x ->
      x __) f2 d (eject d) (eject_graph_correct d)

  (** val coq_FunctionalElimination_eject :
      (__ -> __) -> (__ -> kind -> __ chain -> kind -> ending -> color ->
      color -> __ chain -> __ chain -> __ -> __ -> __ -> __ -> __ -> __) ->
      __ deque -> __ **)

  let coq_FunctionalElimination_eject =
    eject_elim

  (** val coq_FunctionalInduction_eject :
      (__ -> __ deque -> (__ deque, __) prod option) coq_FunctionalInduction **)

  let coq_FunctionalInduction_eject =
    Obj.magic (fun _ -> eject_graph_correct)
 end
