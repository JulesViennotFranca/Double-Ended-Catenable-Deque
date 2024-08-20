(* open Classes *)
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
    Empty O

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

  (** val push_clause_1 : 'a1 -> 'a1 cdeque -> 'a1 cdeque -> 'a1 deque **)

  let push_clause_1 _ _ refine =
    refine

  (** val push : 'a1 -> 'a1 deque -> 'a1 deque **)

  let push x d =
    push_cdeque O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) (ST_ground x) d

  type 'a push_graph =
  | Coq_push_graph_refinement_1 of 'a * 'a cdeque * 'a push_clause_1_graph
  and 'a push_clause_1_graph =
  | Coq_push_clause_1_graph_equation_1 of 'a * 'a cdeque * 'a cdeque

  (** val push_clause_1_graph_mut :
      (__ -> __ -> __ cdeque -> __ push_clause_1_graph -> 'a2 -> 'a1) -> (__
      -> __ -> __ cdeque -> __ cdeque -> __ -> 'a2) -> 'a3 -> 'a3 cdeque ->
      'a3 cdeque -> 'a3 deque -> 'a3 push_clause_1_graph -> 'a2 **)

  let push_clause_1_graph_mut _ f0 _ _ _ _ = function
  | Coq_push_clause_1_graph_equation_1 (x, cd, cd') ->
    Obj.magic f0 __ x cd cd' __

  (** val push_graph_mut :
      (__ -> __ -> __ cdeque -> __ push_clause_1_graph -> 'a2 -> 'a1) -> (__
      -> __ -> __ cdeque -> __ cdeque -> __ -> 'a2) -> 'a3 -> 'a3 deque ->
      'a3 deque -> 'a3 push_graph -> 'a1 **)

  let push_graph_mut f f0 x d s p =
    let rec f1 _ _ _ = function
    | Coq_push_graph_refinement_1 (x0, cd, hind) ->
      Obj.magic f __ x0 cd hind
        (f2 __ x0 cd
          (push_cdeque O (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
            (ST_ground x0) cd)
          (push_cdeque O (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
            (ST_ground x0) cd) hind)
    and f2 _ _ _ _ _ = function
    | Coq_push_clause_1_graph_equation_1 (x0, cd, cd') ->
      Obj.magic f0 __ x0 cd cd' __
    in f1 x d s p

  (** val push_graph_rect :
      (__ -> __ -> __ cdeque -> __ push_clause_1_graph -> 'a2 -> 'a1) -> (__
      -> __ -> __ cdeque -> __ cdeque -> __ -> 'a2) -> 'a3 -> 'a3 deque ->
      'a3 deque -> 'a3 push_graph -> 'a1 **)

  let push_graph_rect =
    push_graph_mut

  (** val push_graph_correct : 'a1 -> 'a1 deque -> 'a1 push_graph **)

  let push_graph_correct x d =
    Coq_push_graph_refinement_1 (x, d,
      (let refine =
         push_cdeque O (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
           (ST_ground x) d
       in
       Coq_push_clause_1_graph_equation_1 (x, d, refine)))

  (** val push_elim :
      (__ -> __ -> __ cdeque -> __ cdeque -> __ -> __ -> 'a1) -> 'a2 -> 'a2
      deque -> 'a1 **)

  let push_elim f0 x d =
    push_graph_mut (fun _ _ _ _ x0 -> x0 __) f0 x d (push x d)
      (push_graph_correct x d)

  (** val coq_FunctionalElimination_push :
      (__ -> __ -> __ cdeque -> __ cdeque -> __ -> __ -> __) -> __ -> __
      deque -> __ **)

  let coq_FunctionalElimination_push =
    push_elim

  (** val coq_FunctionalInduction_push :
      (__ -> __ -> __ deque -> __ deque) coq_FunctionalInduction **)

  let coq_FunctionalInduction_push =
    Obj.magic (fun _ -> push_graph_correct)

  (** val inject_clause_1 : 'a1 cdeque -> 'a1 -> 'a1 cdeque -> 'a1 deque **)

  let inject_clause_1 _ _ refine =
    refine

  (** val inject : 'a1 deque -> 'a1 -> 'a1 deque **)

  let inject d x =
    inject_cdeque O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) d (ST_ground
      x)

  type 'a inject_graph =
  | Coq_inject_graph_refinement_1 of 'a cdeque * 'a * 'a inject_clause_1_graph
  and 'a inject_clause_1_graph =
  | Coq_inject_clause_1_graph_equation_1 of 'a cdeque * 'a * 'a cdeque

  (** val inject_clause_1_graph_mut :
      (__ -> __ cdeque -> __ -> __ inject_clause_1_graph -> 'a2 -> 'a1) ->
      (__ -> __ cdeque -> __ -> __ cdeque -> __ -> 'a2) -> 'a3 cdeque -> 'a3
      -> 'a3 cdeque -> 'a3 deque -> 'a3 inject_clause_1_graph -> 'a2 **)

  let inject_clause_1_graph_mut _ f0 _ _ _ _ = function
  | Coq_inject_clause_1_graph_equation_1 (cd, x, cd') ->
    Obj.magic f0 __ cd x cd' __

  (** val inject_graph_mut :
      (__ -> __ cdeque -> __ -> __ inject_clause_1_graph -> 'a2 -> 'a1) ->
      (__ -> __ cdeque -> __ -> __ cdeque -> __ -> 'a2) -> 'a3 deque -> 'a3
      -> 'a3 deque -> 'a3 inject_graph -> 'a1 **)

  let inject_graph_mut f f0 d x s i =
    let rec f1 _ _ _ = function
    | Coq_inject_graph_refinement_1 (cd, x0, hind) ->
      Obj.magic f __ cd x0 hind
        (f2 __ cd x0
          (inject_cdeque O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) cd
            (ST_ground x0))
          (inject_cdeque O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) cd
            (ST_ground x0)) hind)
    and f2 _ _ _ _ _ = function
    | Coq_inject_clause_1_graph_equation_1 (cd, x0, cd') ->
      Obj.magic f0 __ cd x0 cd' __
    in f1 d x s i

  (** val inject_graph_rect :
      (__ -> __ cdeque -> __ -> __ inject_clause_1_graph -> 'a2 -> 'a1) ->
      (__ -> __ cdeque -> __ -> __ cdeque -> __ -> 'a2) -> 'a3 deque -> 'a3
      -> 'a3 deque -> 'a3 inject_graph -> 'a1 **)

  let inject_graph_rect =
    inject_graph_mut

  (** val inject_graph_correct : 'a1 deque -> 'a1 -> 'a1 inject_graph **)

  let inject_graph_correct d x =
    Coq_inject_graph_refinement_1 (d, x,
      (let refine =
         inject_cdeque O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) d
           (ST_ground x)
       in
       Coq_inject_clause_1_graph_equation_1 (d, x, refine)))

  (** val inject_elim :
      (__ -> __ cdeque -> __ -> __ cdeque -> __ -> __ -> 'a1) -> 'a2 deque ->
      'a2 -> 'a1 **)

  let inject_elim f0 d x =
    inject_graph_mut (fun _ _ _ _ x0 -> x0 __) f0 d x (inject d x)
      (inject_graph_correct d x)

  (** val coq_FunctionalElimination_inject :
      (__ -> __ cdeque -> __ -> __ cdeque -> __ -> __ -> __) -> __ deque ->
      __ -> __ **)

  let coq_FunctionalElimination_inject =
    inject_elim

  (** val coq_FunctionalInduction_inject :
      (__ -> __ deque -> __ -> __ deque) coq_FunctionalInduction **)

  let coq_FunctionalInduction_inject =
    Obj.magic (fun _ -> inject_graph_correct)

  (** val concat_clause_1_clause_1 :
      'a1 cdeque -> 'a1 stored_triple vector -> 'a1 cdeque -> 'a1 cdeque ->
      'a1 deque **)

  let concat_clause_1_clause_1 _ _ _ refine =
    refine

  (** val concat_clause_1_clause_2_clause_1 :
      'a1 cdeque -> 'a1 path -> 'a1 cdeque -> 'a1 stored_triple vector -> 'a1
      cdeque -> 'a1 deque **)

  let concat_clause_1_clause_2_clause_1 _ _ _ _ refine =
    refine

  (** val concat_clause_1_clause_2 :
      'a1 cdeque -> 'a1 path -> 'a1 cdeque -> 'a1 path_attempt -> 'a1 deque **)

  let concat_clause_1_clause_2 cd1 pl _ = function
  | ZeroSix (_, _, v) ->
    inject_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen, NoYellow,
      NoOrange, NoRed)) cd1 v
  | Ok (_, _, p) -> NonEmpty (O, SomeGreen, NoRed, (Pair_green (O, pl, p)))
  | Any (_, _, _) -> assert false (* absurd case *)

  (** val concat_clause_1 :
      'a1 cdeque -> 'a1 path_attempt -> 'a1 cdeque -> 'a1 deque **)

  let concat_clause_1 cd1 refine cd2 =
    match refine with
    | ZeroSix (_, _, v) ->
      push_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen, NoYellow,
        NoOrange, NoRed)) v cd2
    | Ok (_, _, p) ->
      (match make_right O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) cd2 with
       | ZeroSix (_, _, v) ->
         inject_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen, NoYellow,
           NoOrange, NoRed)) cd1 v
       | Ok (_, _, p0) ->
         NonEmpty (O, SomeGreen, NoRed, (Pair_green (O, p, p0)))
       | Any (_, _, _) -> assert false (* absurd case *))
    | Any (_, _, _) -> assert false (* absurd case *)

  (** val concat : 'a1 deque -> 'a1 deque -> 'a1 deque **)

  let concat d1 d2 =
    match make_left O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) d1 with
    | ZeroSix (_, _, v) ->
      push_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen, NoYellow,
        NoOrange, NoRed)) v d2
    | Ok (_, _, p) ->
      (match make_right O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) d2 with
       | ZeroSix (_, _, v) ->
         inject_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen, NoYellow,
           NoOrange, NoRed)) d1 v
       | Ok (_, _, p0) ->
         NonEmpty (O, SomeGreen, NoRed, (Pair_green (O, p, p0)))
       | Any (_, _, _) -> assert false (* absurd case *))
    | Any (_, _, _) -> assert false (* absurd case *)

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

  (** val concat_clause_1_clause_2_clause_1_graph_mut :
      (__ -> __ cdeque -> __ cdeque -> __ concat_clause_1_graph -> 'a2 ->
      'a1) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque
      -> __ concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __ cdeque
      -> __ path -> __ -> __ cdeque -> __ concat_clause_1_clause_2_graph ->
      'a4 -> 'a2) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __
      cdeque -> __ cdeque -> __ -> 'a3) -> (__ -> __ cdeque -> __ path -> __
      -> __ cdeque -> __ stored_triple vector -> __ -> __
      concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> __
      cdeque -> __ path -> __ -> __ cdeque -> __ path -> __ -> 'a4) -> (__ ->
      __ cdeque -> __ path -> __ -> __ cdeque -> __ stored_triple vector ->
      __ cdeque -> __ -> __ -> 'a5) -> 'a6 cdeque -> 'a6 path -> 'a6 cdeque
      -> 'a6 stored_triple vector -> 'a6 cdeque -> 'a6 deque -> 'a6
      concat_clause_1_clause_2_clause_1_graph -> 'a5 **)

  let concat_clause_1_clause_2_clause_1_graph_mut _ _ _ _ _ _ f5 _ _ _ _ _ _ = function
  | Coq_concat_clause_1_clause_2_clause_1_graph_equation_1 (cd1, pl, cd2, v,
                                                            cd) ->
    Obj.magic f5 __ cd1 pl __ cd2 v cd __ __

  (** val concat_clause_1_clause_2_graph_mut :
      (__ -> __ cdeque -> __ cdeque -> __ concat_clause_1_graph -> 'a2 ->
      'a1) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque
      -> __ concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __ cdeque
      -> __ path -> __ -> __ cdeque -> __ concat_clause_1_clause_2_graph ->
      'a4 -> 'a2) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __
      cdeque -> __ cdeque -> __ -> 'a3) -> (__ -> __ cdeque -> __ path -> __
      -> __ cdeque -> __ stored_triple vector -> __ -> __
      concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> __
      cdeque -> __ path -> __ -> __ cdeque -> __ path -> __ -> 'a4) -> (__ ->
      __ cdeque -> __ path -> __ -> __ cdeque -> __ stored_triple vector ->
      __ cdeque -> __ -> __ -> 'a5) -> 'a6 cdeque -> 'a6 path -> 'a6 cdeque
      -> 'a6 path_attempt -> 'a6 deque -> 'a6 concat_clause_1_clause_2_graph
      -> 'a4 **)

  let concat_clause_1_clause_2_graph_mut f f0 f1 f2 f3 f4 f5 cd1 pl cd2 refine s c =
    let rec _f6 _ _ _ _ = function
    | Coq_concat_graph_refinement_1 (cd3, cd4, hind) ->
      f __ cd3 cd4 hind
        (_f7 __ cd3
          (make_left O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) cd3) cd4
          (match make_left O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) cd3 with
           | ZeroSix (_, _, v) ->
             push_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)) v cd4
           | Ok (_, _, p) ->
             (match make_right O (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
                      cd4 with
              | ZeroSix (_, _, v) ->
                inject_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
                  NoYellow, NoOrange, NoRed)) cd3 v
              | Ok (_, _, p0) ->
                NonEmpty (O, SomeGreen, NoRed, (Pair_green (O, p, p0)))
              | Any (_, _, _) -> assert false (* absurd case *))
           | Any (_, _, _) -> assert false (* absurd case *)) hind)
    and _f7 _ _ _ _ _ = function
    | Coq_concat_clause_1_graph_refinement_1 (cd3, v, cd4, hind) ->
      f0 __ cd3 v __ cd4 hind
        (_f8 __ cd3 v __ cd4
          (push_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) v cd4)
          (push_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) v cd4) hind)
    | Coq_concat_clause_1_graph_refinement_2 (cd3, pl0, cd4, hind) ->
      f1 __ cd3 pl0 __ cd4 hind
        (Obj.magic f9 cd3 pl0 cd4
          (make_right O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) cd4)
          (match make_right O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) cd4 with
           | ZeroSix (_, _, v) ->
             inject_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)) cd3 v
           | Ok (_, _, p) ->
             NonEmpty (O, SomeGreen, NoRed, (Pair_green (O, pl0, p)))
           | Any (_, _, _) -> assert false (* absurd case *)) hind)
    and _f8 _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_1_graph_equation_1 (cd3, v, cd4, cd) ->
      f2 __ cd3 v __ cd4 cd __
    and f9 _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_graph_refinement_1 (cd3, pl0, cd4, v, hind) ->
      Obj.magic f3 __ cd3 pl0 __ cd4 v __ hind
        (f10 __ cd3 pl0 __ cd4 v
          (inject_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)) cd3 v) __
          (inject_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)) cd3 v) hind)
    | Coq_concat_clause_1_clause_2_graph_equation_2 (cd3, pl0, cd4, pr) ->
      Obj.magic f4 __ cd3 pl0 __ cd4 pr __
    and f10 _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_clause_1_graph_equation_1 (cd3, pl0, cd4,
                                                              v, cd) ->
      Obj.magic f5 __ cd3 pl0 __ cd4 v cd __ __
    in f9 cd1 pl cd2 refine s c

  (** val concat_clause_1_clause_1_graph_mut :
      (__ -> __ cdeque -> __ cdeque -> __ concat_clause_1_graph -> 'a2 ->
      'a1) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque
      -> __ concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __ cdeque
      -> __ path -> __ -> __ cdeque -> __ concat_clause_1_clause_2_graph ->
      'a4 -> 'a2) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __
      cdeque -> __ cdeque -> __ -> 'a3) -> (__ -> __ cdeque -> __ path -> __
      -> __ cdeque -> __ stored_triple vector -> __ -> __
      concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> __
      cdeque -> __ path -> __ -> __ cdeque -> __ path -> __ -> 'a4) -> (__ ->
      __ cdeque -> __ path -> __ -> __ cdeque -> __ stored_triple vector ->
      __ cdeque -> __ -> __ -> 'a5) -> 'a6 cdeque -> 'a6 stored_triple vector
      -> 'a6 cdeque -> 'a6 cdeque -> 'a6 deque -> 'a6
      concat_clause_1_clause_1_graph -> 'a3 **)

  let concat_clause_1_clause_1_graph_mut _ _ _ f2 _ _ _ _ _ _ _ _ = function
  | Coq_concat_clause_1_clause_1_graph_equation_1 (cd1, v, cd2, cd) ->
    Obj.magic f2 __ cd1 v __ cd2 cd __

  (** val concat_clause_1_graph_mut :
      (__ -> __ cdeque -> __ cdeque -> __ concat_clause_1_graph -> 'a2 ->
      'a1) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque
      -> __ concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __ cdeque
      -> __ path -> __ -> __ cdeque -> __ concat_clause_1_clause_2_graph ->
      'a4 -> 'a2) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __
      cdeque -> __ cdeque -> __ -> 'a3) -> (__ -> __ cdeque -> __ path -> __
      -> __ cdeque -> __ stored_triple vector -> __ -> __
      concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> __
      cdeque -> __ path -> __ -> __ cdeque -> __ path -> __ -> 'a4) -> (__ ->
      __ cdeque -> __ path -> __ -> __ cdeque -> __ stored_triple vector ->
      __ cdeque -> __ -> __ -> 'a5) -> 'a6 cdeque -> 'a6 path_attempt -> 'a6
      cdeque -> 'a6 deque -> 'a6 concat_clause_1_graph -> 'a2 **)

  let concat_clause_1_graph_mut f f0 f1 f2 f3 f4 f5 cd1 refine cd2 s c =
    let rec _f6 _ _ _ _ = function
    | Coq_concat_graph_refinement_1 (cd3, cd4, hind) ->
      Obj.magic f __ cd3 cd4 hind
        (f7 cd3
          (make_left O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) cd3) cd4
          (match make_left O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) cd3 with
           | ZeroSix (_, _, v) ->
             push_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)) v cd4
           | Ok (_, _, p) ->
             (match make_right O (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
                      cd4 with
              | ZeroSix (_, _, v) ->
                inject_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
                  NoYellow, NoOrange, NoRed)) cd3 v
              | Ok (_, _, p0) ->
                NonEmpty (O, SomeGreen, NoRed, (Pair_green (O, p, p0)))
              | Any (_, _, _) -> assert false (* absurd case *))
           | Any (_, _, _) -> assert false (* absurd case *)) hind)
    and f7 _ _ _ _ = function
    | Coq_concat_clause_1_graph_refinement_1 (cd3, v, cd4, hind) ->
      Obj.magic f0 __ cd3 v __ cd4 hind
        (f8 __ cd3 v __ cd4
          (push_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) v cd4)
          (push_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) v cd4) hind)
    | Coq_concat_clause_1_graph_refinement_2 (cd3, pl, cd4, hind) ->
      Obj.magic f1 __ cd3 pl __ cd4 hind
        (f9 __ cd3 pl __ cd4
          (make_right O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) cd4)
          (match make_right O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) cd4 with
           | ZeroSix (_, _, v) ->
             inject_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)) cd3 v
           | Ok (_, _, p) ->
             NonEmpty (O, SomeGreen, NoRed, (Pair_green (O, pl, p)))
           | Any (_, _, _) -> assert false (* absurd case *)) hind)
    and f8 _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_1_graph_equation_1 (cd3, v, cd4, cd) ->
      Obj.magic f2 __ cd3 v __ cd4 cd __
    and f9 _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_graph_refinement_1 (cd3, pl, cd4, v, hind) ->
      Obj.magic f3 __ cd3 pl __ cd4 v __ hind
        (f10 __ cd3 pl __ cd4 v
          (inject_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)) cd3 v) __
          (inject_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)) cd3 v) hind)
    | Coq_concat_clause_1_clause_2_graph_equation_2 (cd3, pl, cd4, pr) ->
      Obj.magic f4 __ cd3 pl __ cd4 pr __
    and f10 _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_clause_1_graph_equation_1 (cd3, pl, cd4,
                                                              v, cd) ->
      Obj.magic f5 __ cd3 pl __ cd4 v cd __ __
    in f7 cd1 refine cd2 s c

  (** val concat_graph_mut :
      (__ -> __ cdeque -> __ cdeque -> __ concat_clause_1_graph -> 'a2 ->
      'a1) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque
      -> __ concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __ cdeque
      -> __ path -> __ -> __ cdeque -> __ concat_clause_1_clause_2_graph ->
      'a4 -> 'a2) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __
      cdeque -> __ cdeque -> __ -> 'a3) -> (__ -> __ cdeque -> __ path -> __
      -> __ cdeque -> __ stored_triple vector -> __ -> __
      concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> __
      cdeque -> __ path -> __ -> __ cdeque -> __ path -> __ -> 'a4) -> (__ ->
      __ cdeque -> __ path -> __ -> __ cdeque -> __ stored_triple vector ->
      __ cdeque -> __ -> __ -> 'a5) -> 'a6 deque -> 'a6 deque -> 'a6 deque ->
      'a6 concat_graph -> 'a1 **)

  let concat_graph_mut f f0 f1 f2 f3 f4 f5 d1 d2 s c =
    let rec f6 _ _ _ = function
    | Coq_concat_graph_refinement_1 (cd1, cd2, hind) ->
      Obj.magic f __ cd1 cd2 hind
        (f7 __ cd1
          (make_left O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) cd1) cd2
          (match make_left O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) cd1 with
           | ZeroSix (_, _, v) ->
             push_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)) v cd2
           | Ok (_, _, p) ->
             (match make_right O (Mix (SomeGreen, NoYellow, NoOrange, NoRed))
                      cd2 with
              | ZeroSix (_, _, v) ->
                inject_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
                  NoYellow, NoOrange, NoRed)) cd1 v
              | Ok (_, _, p0) ->
                NonEmpty (O, SomeGreen, NoRed, (Pair_green (O, p, p0)))
              | Any (_, _, _) -> assert false (* absurd case *))
           | Any (_, _, _) -> assert false (* absurd case *)) hind)
    and f7 _ _ _ _ _ = function
    | Coq_concat_clause_1_graph_refinement_1 (cd1, v, cd2, hind) ->
      Obj.magic f0 __ cd1 v __ cd2 hind
        (f8 __ cd1 v __ cd2
          (push_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) v cd2)
          (push_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen, NoYellow,
            NoOrange, NoRed)) v cd2) hind)
    | Coq_concat_clause_1_graph_refinement_2 (cd1, pl, cd2, hind) ->
      Obj.magic f1 __ cd1 pl __ cd2 hind
        (f9 __ cd1 pl __ cd2
          (make_right O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) cd2)
          (match make_right O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) cd2 with
           | ZeroSix (_, _, v) ->
             inject_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
               NoYellow, NoOrange, NoRed)) cd1 v
           | Ok (_, _, p) ->
             NonEmpty (O, SomeGreen, NoRed, (Pair_green (O, pl, p)))
           | Any (_, _, _) -> assert false (* absurd case *)) hind)
    and f8 _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_1_graph_equation_1 (cd1, v, cd2, cd) ->
      Obj.magic f2 __ cd1 v __ cd2 cd __
    and f9 _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_graph_refinement_1 (cd1, pl, cd2, v, hind) ->
      Obj.magic f3 __ cd1 pl __ cd2 v __ hind
        (f10 __ cd1 pl __ cd2 v
          (inject_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)) cd1 v) __
          (inject_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
            NoYellow, NoOrange, NoRed)) cd1 v) hind)
    | Coq_concat_clause_1_clause_2_graph_equation_2 (cd1, pl, cd2, pr) ->
      Obj.magic f4 __ cd1 pl __ cd2 pr __
    and f10 _ _ _ _ _ _ _ _ _ = function
    | Coq_concat_clause_1_clause_2_clause_1_graph_equation_1 (cd1, pl, cd2,
                                                              v, cd) ->
      Obj.magic f5 __ cd1 pl __ cd2 v cd __ __
    in f6 d1 d2 s c

  (** val concat_graph_rect :
      (__ -> __ cdeque -> __ cdeque -> __ concat_clause_1_graph -> 'a2 ->
      'a1) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque
      -> __ concat_clause_1_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __ cdeque
      -> __ path -> __ -> __ cdeque -> __ concat_clause_1_clause_2_graph ->
      'a4 -> 'a2) -> (__ -> __ cdeque -> __ stored_triple vector -> __ -> __
      cdeque -> __ cdeque -> __ -> 'a3) -> (__ -> __ cdeque -> __ path -> __
      -> __ cdeque -> __ stored_triple vector -> __ -> __
      concat_clause_1_clause_2_clause_1_graph -> 'a5 -> 'a4) -> (__ -> __
      cdeque -> __ path -> __ -> __ cdeque -> __ path -> __ -> 'a4) -> (__ ->
      __ cdeque -> __ path -> __ -> __ cdeque -> __ stored_triple vector ->
      __ cdeque -> __ -> __ -> 'a5) -> 'a6 deque -> 'a6 deque -> 'a6 deque ->
      'a6 concat_graph -> 'a1 **)

  let concat_graph_rect =
    concat_graph_mut

  (** val concat_graph_correct :
      'a1 deque -> 'a1 deque -> 'a1 concat_graph **)

  let concat_graph_correct d1 d2 =
    Coq_concat_graph_refinement_1 (d1, d2,
      (let refine =
         make_left O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) d1
       in
       match refine with
       | ZeroSix (_, _, v) ->
         Coq_concat_clause_1_graph_refinement_1 (d1, v, d2,
           (let refine0 =
              push_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
                NoYellow, NoOrange, NoRed)) v d2
            in
            Coq_concat_clause_1_clause_1_graph_equation_1 (d1, v, d2, refine0)))
       | Ok (_, _, p) ->
         Coq_concat_clause_1_graph_refinement_2 (d1, p, d2,
           (let refine0 =
              make_right O (Mix (SomeGreen, NoYellow, NoOrange, NoRed)) d2
            in
            match refine0 with
            | ZeroSix (_, _, v) ->
              Coq_concat_clause_1_clause_2_graph_refinement_1 (d1, p, d2, v,
                (let refine1 =
                   inject_vector O (S (S (S (S (S (S O)))))) (Mix (SomeGreen,
                     NoYellow, NoOrange, NoRed)) d1 v
                 in
                 Coq_concat_clause_1_clause_2_clause_1_graph_equation_1 (d1,
                 p, d2, v, refine1)))
            | Ok (_, _, p0) ->
              Coq_concat_clause_1_clause_2_graph_equation_2 (d1, p, d2, p0)
            | Any (_, _, _) -> assert false (* absurd case *)))
       | Any (_, _, _) -> assert false (* absurd case *)))

  (** val concat_elim :
      (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque -> __
      cdeque -> __ -> __ -> __ -> 'a1) -> (__ -> __ cdeque -> __ path -> __
      -> __ cdeque -> __ path -> __ -> __ -> __ -> 'a1) -> (__ -> __ cdeque
      -> __ path -> __ -> __ cdeque -> __ stored_triple vector -> __ cdeque
      -> __ -> __ -> __ -> __ -> __ -> 'a1) -> 'a2 deque -> 'a2 deque -> 'a1 **)

  let concat_elim f2 f4 f5 d1 d2 =
    concat_graph_mut (fun _ _ _ _ x -> x __) (fun _ _ _ _ _ _ x -> x __)
      (fun _ _ _ _ _ _ x -> x __) f2 (fun _ _ _ _ _ _ _ _ x -> x __) f4 f5 d1
      d2 (concat d1 d2) (concat_graph_correct d1 d2)

  (** val coq_FunctionalElimination_concat :
      (__ -> __ cdeque -> __ stored_triple vector -> __ -> __ cdeque -> __
      cdeque -> __ -> __ -> __ -> __) -> (__ -> __ cdeque -> __ path -> __ ->
      __ cdeque -> __ path -> __ -> __ -> __ -> __) -> (__ -> __ cdeque -> __
      path -> __ -> __ cdeque -> __ stored_triple vector -> __ cdeque -> __
      -> __ -> __ -> __ -> __ -> __) -> __ deque -> __ deque -> __ **)

  let coq_FunctionalElimination_concat =
    concat_elim

  (** val coq_FunctionalInduction_concat :
      (__ -> __ deque -> __ deque -> __ deque) coq_FunctionalInduction **)

  let coq_FunctionalInduction_concat =
    Obj.magic (fun _ -> concat_graph_correct)

  (** val pop_clause_2_clause_1 :
      'a1 non_empty_cdeque -> 'a1 -> 'a1 sdeque -> 'a1 deque -> ('a1, 'a1
      deque) prod option **)

  let pop_clause_2_clause_1 _ x _ refine =
    Some (Coq_pair (x, refine))

  (** val pop_clause_2 :
      'a1 non_empty_cdeque -> ('a1 stored_triple, 'a1 sdeque) prod -> ('a1,
      'a1 deque) prod option **)

  let pop_clause_2 _ = function
  | Coq_pair (s, s0) ->
    (match s with
     | ST_ground y -> Some (Coq_pair (y, (regular_of_semi s0)))
     | _ -> assert false (* absurd case *))

  (** val pop : 'a1 deque -> ('a1, 'a1 deque) prod option **)

  let pop = function
  | Empty _ -> None
  | NonEmpty (_, _, _, n) ->
    let Coq_pair (s, s0) = pop_green O n in
    (match s with
     | ST_ground y -> Some (Coq_pair (y, (regular_of_semi s0)))
     | _ -> assert false (* absurd case *))

  type 'a pop_graph =
  | Coq_pop_graph_equation_1
  | Coq_pop_graph_refinement_2 of 'a non_empty_cdeque * 'a pop_clause_2_graph
  and 'a pop_clause_2_graph =
  | Coq_pop_clause_2_graph_refinement_1 of 'a non_empty_cdeque * 'a
     * 'a sdeque * 'a pop_clause_2_clause_1_graph
  and 'a pop_clause_2_clause_1_graph =
  | Coq_pop_clause_2_clause_1_graph_equation_1 of 'a non_empty_cdeque * 
     'a * 'a sdeque * 'a deque

  (** val pop_clause_2_clause_1_graph_mut :
      (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ pop_clause_2_graph ->
      'a2 -> 'a1) -> (__ -> __ non_empty_cdeque -> __ -> __ sdeque -> __ ->
      __ pop_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __
      non_empty_cdeque -> __ -> __ sdeque -> __ deque -> __ -> __ -> 'a3) ->
      'a4 non_empty_cdeque -> 'a4 -> 'a4 sdeque -> 'a4 deque -> ('a4, 'a4
      deque) prod option -> 'a4 pop_clause_2_clause_1_graph -> 'a3 **)

  let pop_clause_2_clause_1_graph_mut _ _ _ f2 _ _ _ _ _ = function
  | Coq_pop_clause_2_clause_1_graph_equation_1 (cd, x, sd, d') ->
    Obj.magic f2 __ cd x sd d' __ __

  (** val pop_clause_2_graph_mut :
      (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ pop_clause_2_graph ->
      'a2 -> 'a1) -> (__ -> __ non_empty_cdeque -> __ -> __ sdeque -> __ ->
      __ pop_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __
      non_empty_cdeque -> __ -> __ sdeque -> __ deque -> __ -> __ -> 'a3) ->
      'a4 non_empty_cdeque -> ('a4 stored_triple, 'a4 sdeque) prod -> ('a4,
      'a4 deque) prod option -> 'a4 pop_clause_2_graph -> 'a2 **)

  let pop_clause_2_graph_mut f f0 f1 f2 cd refine s p =
    let rec _f3 _ _ _ = function
    | Coq_pop_graph_equation_1 -> f __
    | Coq_pop_graph_refinement_2 (cd0, hind) ->
      Obj.magic f0 __ cd0 hind
        (f4 cd0 (pop_green O cd0)
          (let Coq_pair (s0, s1) = pop_green O cd0 in
           (match s0 with
            | ST_ground y -> Some (Coq_pair (y, (regular_of_semi s1)))
            | _ -> assert false (* absurd case *))) hind)
    and f4 _ _ _ = function
    | Coq_pop_clause_2_graph_refinement_1 (cd0, x, sd, hind) ->
      Obj.magic f1 __ cd0 x sd __ hind
        (f5 __ cd0 x sd (regular_of_semi sd) __ (Some (Coq_pair (x,
          (regular_of_semi sd)))) hind)
    and f5 _ _ _ _ _ _ _ = function
    | Coq_pop_clause_2_clause_1_graph_equation_1 (cd0, x, sd, d') ->
      Obj.magic f2 __ cd0 x sd d' __ __
    in f4 cd refine s p

  (** val pop_graph_mut :
      (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ pop_clause_2_graph ->
      'a2 -> 'a1) -> (__ -> __ non_empty_cdeque -> __ -> __ sdeque -> __ ->
      __ pop_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __
      non_empty_cdeque -> __ -> __ sdeque -> __ deque -> __ -> __ -> 'a3) ->
      'a4 deque -> ('a4, 'a4 deque) prod option -> 'a4 pop_graph -> 'a1 **)

  let pop_graph_mut f f0 f1 f2 d s p =
    let rec f3 _ _ = function
    | Coq_pop_graph_equation_1 -> f __
    | Coq_pop_graph_refinement_2 (cd, hind) ->
      Obj.magic f0 __ cd hind
        (f4 __ cd (pop_green O cd)
          (let Coq_pair (s0, s1) = pop_green O cd in
           (match s0 with
            | ST_ground y -> Some (Coq_pair (y, (regular_of_semi s1)))
            | _ -> assert false (* absurd case *))) hind)
    and f4 _ _ _ _ = function
    | Coq_pop_clause_2_graph_refinement_1 (cd, x, sd, hind) ->
      Obj.magic f1 __ cd x sd __ hind
        (f5 __ cd x sd (regular_of_semi sd) __ (Some (Coq_pair (x,
          (regular_of_semi sd)))) hind)
    and f5 _ _ _ _ _ _ _ = function
    | Coq_pop_clause_2_clause_1_graph_equation_1 (cd, x, sd, d') ->
      Obj.magic f2 __ cd x sd d' __ __
    in f3 d s p

  (** val pop_graph_rect :
      (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ pop_clause_2_graph ->
      'a2 -> 'a1) -> (__ -> __ non_empty_cdeque -> __ -> __ sdeque -> __ ->
      __ pop_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __
      non_empty_cdeque -> __ -> __ sdeque -> __ deque -> __ -> __ -> 'a3) ->
      'a4 deque -> ('a4, 'a4 deque) prod option -> 'a4 pop_graph -> 'a1 **)

  let pop_graph_rect =
    pop_graph_mut

  (** val pop_graph_correct : 'a1 deque -> 'a1 pop_graph **)

  let pop_graph_correct = function
  | Empty _ -> Coq_pop_graph_equation_1
  | NonEmpty (_, _, _, n) ->
    Coq_pop_graph_refinement_2 (n,
      (let refine = pop_green O n in
       let Coq_pair (s, s0) = refine in
       (match s with
        | ST_ground y ->
          Coq_pop_clause_2_graph_refinement_1 (n, y, s0,
            (let refine0 = regular_of_semi s0 in
             Coq_pop_clause_2_clause_1_graph_equation_1 (n, y, s0, refine0)))
        | _ -> assert false (* absurd case *))))

  (** val pop_elim :
      (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ -> __ sdeque -> __
      deque -> __ -> __ -> __ -> __ -> 'a1) -> 'a2 deque -> 'a1 **)

  let pop_elim f f2 d =
    pop_graph_mut f (fun _ _ _ x -> x __) (fun _ _ _ _ _ _ x -> x __) f2 d
      (pop d) (pop_graph_correct d)

  (** val coq_FunctionalElimination_pop :
      (__ -> __) -> (__ -> __ non_empty_cdeque -> __ -> __ sdeque -> __ deque
      -> __ -> __ -> __ -> __ -> __) -> __ deque -> __ **)

  let coq_FunctionalElimination_pop =
    pop_elim

  (** val coq_FunctionalInduction_pop :
      (__ -> __ deque -> (__, __ deque) prod option) coq_FunctionalInduction **)

  let coq_FunctionalInduction_pop =
    Obj.magic (fun _ -> pop_graph_correct)

  (** val eject_clause_2_clause_1 :
      'a1 non_empty_cdeque -> 'a1 sdeque -> 'a1 deque -> 'a1 -> ('a1 deque,
      'a1) prod option **)

  let eject_clause_2_clause_1 _ _ refine x =
    Some (Coq_pair (refine, x))

  (** val eject_clause_2 :
      'a1 non_empty_cdeque -> ('a1 sdeque, 'a1 stored_triple) prod -> ('a1
      deque, 'a1) prod option **)

  let eject_clause_2 _ = function
  | Coq_pair (s, s0) ->
    (match s0 with
     | ST_ground y -> Some (Coq_pair ((regular_of_semi s), y))
     | _ -> assert false (* absurd case *))

  (** val eject : 'a1 deque -> ('a1 deque, 'a1) prod option **)

  let eject = function
  | Empty _ -> None
  | NonEmpty (_, _, _, n) ->
    let Coq_pair (s, s0) = eject_green O n in
    (match s0 with
     | ST_ground y -> Some (Coq_pair ((regular_of_semi s), y))
     | _ -> assert false (* absurd case *))

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

  (** val eject_clause_2_clause_1_graph_mut :
      (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ eject_clause_2_graph ->
      'a2 -> 'a1) -> (__ -> __ non_empty_cdeque -> __ sdeque -> __ -> __ ->
      __ eject_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __
      non_empty_cdeque -> __ sdeque -> __ deque -> __ -> __ -> __ -> 'a3) ->
      'a4 non_empty_cdeque -> 'a4 sdeque -> 'a4 deque -> 'a4 -> ('a4 deque,
      'a4) prod option -> 'a4 eject_clause_2_clause_1_graph -> 'a3 **)

  let eject_clause_2_clause_1_graph_mut _ _ _ f2 _ _ _ _ _ = function
  | Coq_eject_clause_2_clause_1_graph_equation_1 (cd, sd, d', x) ->
    Obj.magic f2 __ cd sd d' __ x __

  (** val eject_clause_2_graph_mut :
      (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ eject_clause_2_graph ->
      'a2 -> 'a1) -> (__ -> __ non_empty_cdeque -> __ sdeque -> __ -> __ ->
      __ eject_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __
      non_empty_cdeque -> __ sdeque -> __ deque -> __ -> __ -> __ -> 'a3) ->
      'a4 non_empty_cdeque -> ('a4 sdeque, 'a4 stored_triple) prod -> ('a4
      deque, 'a4) prod option -> 'a4 eject_clause_2_graph -> 'a2 **)

  let eject_clause_2_graph_mut f f0 f1 f2 cd refine s e =
    let rec _f3 _ _ _ = function
    | Coq_eject_graph_equation_1 -> f __
    | Coq_eject_graph_refinement_2 (cd0, hind) ->
      Obj.magic f0 __ cd0 hind
        (f4 cd0 (eject_green O cd0)
          (let Coq_pair (s0, s1) = eject_green O cd0 in
           (match s1 with
            | ST_ground y -> Some (Coq_pair ((regular_of_semi s0), y))
            | _ -> assert false (* absurd case *))) hind)
    and f4 _ _ _ = function
    | Coq_eject_clause_2_graph_refinement_1 (cd0, sd, x, hind) ->
      Obj.magic f1 __ cd0 sd x __ hind
        (f5 __ cd0 sd (regular_of_semi sd) x __ (Some (Coq_pair
          ((regular_of_semi sd), x))) hind)
    and f5 _ _ _ _ _ _ _ = function
    | Coq_eject_clause_2_clause_1_graph_equation_1 (cd0, sd, d', x) ->
      Obj.magic f2 __ cd0 sd d' __ x __
    in f4 cd refine s e

  (** val eject_graph_mut :
      (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ eject_clause_2_graph ->
      'a2 -> 'a1) -> (__ -> __ non_empty_cdeque -> __ sdeque -> __ -> __ ->
      __ eject_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __
      non_empty_cdeque -> __ sdeque -> __ deque -> __ -> __ -> __ -> 'a3) ->
      'a4 deque -> ('a4 deque, 'a4) prod option -> 'a4 eject_graph -> 'a1 **)

  let eject_graph_mut f f0 f1 f2 d s e =
    let rec f3 _ _ = function
    | Coq_eject_graph_equation_1 -> f __
    | Coq_eject_graph_refinement_2 (cd, hind) ->
      Obj.magic f0 __ cd hind
        (f4 __ cd (eject_green O cd)
          (let Coq_pair (s0, s1) = eject_green O cd in
           (match s1 with
            | ST_ground y -> Some (Coq_pair ((regular_of_semi s0), y))
            | _ -> assert false (* absurd case *))) hind)
    and f4 _ _ _ _ = function
    | Coq_eject_clause_2_graph_refinement_1 (cd, sd, x, hind) ->
      Obj.magic f1 __ cd sd x __ hind
        (f5 __ cd sd (regular_of_semi sd) x __ (Some (Coq_pair
          ((regular_of_semi sd), x))) hind)
    and f5 _ _ _ _ _ _ _ = function
    | Coq_eject_clause_2_clause_1_graph_equation_1 (cd, sd, d', x) ->
      Obj.magic f2 __ cd sd d' __ x __
    in f3 d s e

  (** val eject_graph_rect :
      (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ eject_clause_2_graph ->
      'a2 -> 'a1) -> (__ -> __ non_empty_cdeque -> __ sdeque -> __ -> __ ->
      __ eject_clause_2_clause_1_graph -> 'a3 -> 'a2) -> (__ -> __
      non_empty_cdeque -> __ sdeque -> __ deque -> __ -> __ -> __ -> 'a3) ->
      'a4 deque -> ('a4 deque, 'a4) prod option -> 'a4 eject_graph -> 'a1 **)

  let eject_graph_rect =
    eject_graph_mut

  (** val eject_graph_correct : 'a1 deque -> 'a1 eject_graph **)

  let eject_graph_correct = function
  | Empty _ -> Coq_eject_graph_equation_1
  | NonEmpty (_, _, _, n) ->
    Coq_eject_graph_refinement_2 (n,
      (let refine = eject_green O n in
       let Coq_pair (s, s0) = refine in
       (match s0 with
        | ST_ground y ->
          Coq_eject_clause_2_graph_refinement_1 (n, s, y,
            (let refine0 = regular_of_semi s in
             Coq_eject_clause_2_clause_1_graph_equation_1 (n, s, refine0, y)))
        | _ -> assert false (* absurd case *))))

  (** val eject_elim :
      (__ -> 'a1) -> (__ -> __ non_empty_cdeque -> __ sdeque -> __ deque ->
      __ -> __ -> __ -> __ -> __ -> 'a1) -> 'a2 deque -> 'a1 **)

  let eject_elim f f2 d =
    eject_graph_mut f (fun _ _ _ x -> x __) (fun _ _ _ _ _ _ x -> x __) f2 d
      (eject d) (eject_graph_correct d)

  (** val coq_FunctionalElimination_eject :
      (__ -> __) -> (__ -> __ non_empty_cdeque -> __ sdeque -> __ deque -> __
      -> __ -> __ -> __ -> __ -> __) -> __ deque -> __ **)

  let coq_FunctionalElimination_eject =
    eject_elim

  (** val coq_FunctionalInduction_eject :
      (__ -> __ deque -> (__ deque, __) prod option) coq_FunctionalInduction **)

  let coq_FunctionalInduction_eject =
    Obj.magic (fun _ -> eject_graph_correct)
 end
