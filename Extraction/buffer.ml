open Datatypes
open Nat
open Ncdeque

type 'a vector =
| V0 of nat
| V1 of nat * 'a
| V2 of nat * 'a * 'a
| V3 of nat * 'a * 'a * 'a
| V4 of nat * 'a * 'a * 'a * 'a
| V5 of nat * 'a * 'a * 'a * 'a * 'a
| V6 of nat * 'a * 'a * 'a * 'a * 'a * 'a

type 'a t = 'a deque
  (* singleton inductive, whose constructor was Buffer *)

type 'a pt = 'a t

(** val seq : nat -> 'a1 t -> 'a1 list **)

let seq =
  deque_seq

(** val vector_seq : nat -> 'a1 vector -> 'a1 list **)

let vector_seq _ = function
| V0 _ -> Coq_nil
| V1 (_, y) -> Coq_cons (y, Coq_nil)
| V2 (_, y, y0) -> app (Coq_cons (y, Coq_nil)) (Coq_cons (y0, Coq_nil))
| V3 (_, y, y0, y1) ->
  app (Coq_cons (y, Coq_nil))
    (app (Coq_cons (y0, Coq_nil)) (Coq_cons (y1, Coq_nil)))
| V4 (_, y, y0, y1, y2) ->
  app (Coq_cons (y, Coq_nil))
    (app (Coq_cons (y0, Coq_nil))
      (app (Coq_cons (y1, Coq_nil)) (Coq_cons (y2, Coq_nil))))
| V5 (_, y, y0, y1, y2, y3) ->
  app (Coq_cons (y, Coq_nil))
    (app (Coq_cons (y0, Coq_nil))
      (app (Coq_cons (y1, Coq_nil))
        (app (Coq_cons (y2, Coq_nil)) (Coq_cons (y3, Coq_nil)))))
| V6 (_, y, y0, y1, y2, y3, y4) ->
  app (Coq_cons (y, Coq_nil))
    (app (Coq_cons (y0, Coq_nil))
      (app (Coq_cons (y1, Coq_nil))
        (app (Coq_cons (y2, Coq_nil))
          (app (Coq_cons (y3, Coq_nil)) (Coq_cons (y4, Coq_nil))))))

(** val map_buffer :
    (nat -> 'a1 -> 'a2 list) -> nat -> nat -> 'a1 t -> 'a2 list **)

let map_buffer =
  map_deque

(** val empty : 'a1 t **)

let empty =
  empty

(** val vector_length : nat -> 'a1 vector -> nat **)

let vector_length _ = function
| V0 _ -> O
| V1 (_, _) -> S O
| V2 (_, _, _) -> S (S O)
| V3 (_, _, _, _) -> S (S (S O))
| V4 (_, _, _, _, _) -> S (S (S (S O)))
| V5 (_, _, _, _, _, _) -> S (S (S (S (S O))))
| V6 (_, _, _, _, _, _, _) -> S (S (S (S (S (S O)))))

(** val translate : nat -> nat -> 'a1 t -> 'a1 t **)

let translate _ _ b =
  b

(** val push : nat -> 'a1 -> 'a1 t -> 'a1 t **)

let push =
  push

(** val inject : nat -> 'a1 t -> 'a1 -> 'a1 t **)

let inject =
  inject

(** val pop : nat -> 'a1 t -> ('a1, 'a1 t) prod **)

let pop q b =
  let Coq_pair (y, d) = pop q b in Coq_pair (y, d)

(** val eject : nat -> 'a1 t -> ('a1 t, 'a1) prod **)

let eject q b =
  let Coq_pair (d, y) = eject q b in Coq_pair (d, y)

(** val single : 'a1 -> 'a1 t **)

let single a1 =
  Ncdeque.push O a1 Ncdeque.empty

(** val pair : 'a1 -> 'a1 -> 'a1 t **)

let pair a1 a2 =
  push (S O) a1 (single a2)

(** val triple : 'a1 -> 'a1 -> 'a1 -> 'a1 t **)

let triple a1 a2 a3 =
  push (S (S O)) a1 (pair a2 a3)

(** val push2 : nat -> 'a1 -> 'a1 -> 'a1 t -> 'a1 t **)

let push2 q a1 a2 b =
  push (S q) a1 (push q a2 b)

(** val inject2 : nat -> 'a1 t -> 'a1 -> 'a1 -> 'a1 t **)

let inject2 q b a2 a1 =
  inject (S q) (inject q b a2) a1

(** val pop2 : nat -> 'a1 t -> (('a1, 'a1) prod, 'a1 t) prod **)

let pop2 q b =
  let Coq_pair (y, t0) = pop (S q) b in
  let Coq_pair (y0, t1) = pop q t0 in Coq_pair ((Coq_pair (y, y0)), t1)

(** val eject2 : nat -> 'a1 t -> (('a1 t, 'a1) prod, 'a1) prod **)

let eject2 q b =
  let Coq_pair (t0, y) = eject (S q) b in Coq_pair ((eject q t0), y)

(** val push5 : nat -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 t -> 'a1 t **)

let push5 q a1 a2 a3 a4 a5 b =
  push (S (S (S (S q)))) a1 (push2 (S (S q)) a2 a3 (push2 q a4 a5 b))

(** val inject5 : nat -> 'a1 t -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 t **)

let inject5 q b a5 a4 a3 a2 a1 =
  inject (S (S (S (S q)))) (inject2 (S (S q)) (inject2 q b a5 a4) a3 a2) a1

(** val pop5 :
    nat -> 'a1 t -> ((((('a1, 'a1) prod, 'a1) prod, 'a1) prod, 'a1) prod, 'a1
    t) prod **)

let pop5 q b =
  let Coq_pair (p, t0) =
    pop2 (S
      (let rec add0 n m =
         match n with
         | O -> m
         | S p -> S (add0 p m)
       in add0 (S (S O)) q)) b
  in
  let Coq_pair (p0, t1) =
    pop2 (S
      (let rec add0 n m =
         match n with
         | O -> m
         | S p0 -> S (add0 p0 m)
       in add0 O q)) t0
  in
  let Coq_pair (y, y0) = p0 in
  let Coq_pair (y1, t2) = pop q t1 in
  Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair (p, y)), y0)), y1)), t2)

(** val push6 :
    nat -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 t -> 'a1 t **)

let push6 q a1 a2 a3 a4 a5 a6 b =
  push (add (S (S (S (S (S O))))) q) a1 (push5 q a2 a3 a4 a5 a6 b)

(** val inject6 :
    nat -> 'a1 t -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 t **)

let inject6 q b a6 a5 a4 a3 a2 a1 =
  inject (add (S (S (S (S (S O))))) q) (inject5 q b a6 a5 a4 a3 a2) a1

(** val inject8 :
    nat -> 'a1 t -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 t **)

let inject8 q b a8 a7 a6 a5 a4 a3 a2 a1 =
  inject2 (add (S (S (S (S (S (S O)))))) q) (inject6 q b a8 a7 a6 a5 a4 a3)
    a2 a1

(** val push_vector : nat -> nat -> 'a1 vector -> 'a1 t -> 'a1 t **)

let push_vector _ q v b =
  match v with
  | V0 _ -> translate q (add q O) b
  | V1 (_, y) -> translate (S q) (add q (S O)) (push q y b)
  | V2 (_, y, y0) -> translate (S (S q)) (add q (S (S O))) (push2 q y y0 b)
  | V3 (_, y, y0, y1) ->
    translate (S (S (S q))) (add q (S (S (S O))))
      (push (S (S q)) y (push2 q y0 y1 b))
  | V4 (_, y, y0, y1, y2) ->
    translate (S (S (S (S q)))) (add q (S (S (S (S O)))))
      (push2 (S (S q)) y y0 (push2 q y1 y2 b))
  | V5 (_, y, y0, y1, y2, y3) ->
    translate (add (S (S (S (S (S O))))) q) (add q (S (S (S (S (S O))))))
      (push5 q y y0 y1 y2 y3 b)
  | V6 (_, y, y0, y1, y2, y3, y4) ->
    translate (add (S (S (S (S (S (S O)))))) q)
      (add q (S (S (S (S (S (S O))))))) (push6 q y y0 y1 y2 y3 y4 b)

(** val inject_vector : nat -> nat -> 'a1 t -> 'a1 vector -> 'a1 t **)

let inject_vector _ q b = function
| V0 _ -> translate q (add q O) b
| V1 (_, y) -> translate (S q) (add q (S O)) (inject q b y)
| V2 (_, y, y0) -> translate (S (S q)) (add q (S (S O))) (inject2 q b y y0)
| V3 (_, y, y0, y1) ->
  translate (S (S (S q))) (add q (S (S (S O))))
    (inject (S (S q)) (inject2 q b y y0) y1)
| V4 (_, y, y0, y1, y2) ->
  translate (S (S (S (S q)))) (add q (S (S (S (S O)))))
    (inject2 (S (S q)) (inject2 q b y y0) y1 y2)
| V5 (_, y, y0, y1, y2, y3) ->
  translate (add (S (S (S (S (S O))))) q) (add q (S (S (S (S (S O))))))
    (inject5 q b y y0 y1 y2 y3)
| V6 (_, y, y0, y1, y2, y3, y4) ->
  translate (add (S (S (S (S (S (S O)))))) q)
    (add q (S (S (S (S (S (S O))))))) (inject6 q b y y0 y1 y2 y3 y4)

(** val push5_vector :
    nat -> nat -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vector -> 'a1 t ->
    'a1 t **)

let push5_vector n q a1 a2 a3 a4 a5 vec b =
  push5 (add q (vector_length n vec)) a1 a2 a3 a4 a5 (push_vector n q vec b)

(** val inject5_vector :
    nat -> nat -> 'a1 t -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vector ->
    'a1 t **)

let inject5_vector n q b a5 a4 a3 a2 a1 vec =
  inject_vector n (add (S (S (S (S (S O))))) q) (inject5 q b a5 a4 a3 a2 a1)
    vec

(** val two : 'a1 t -> ('a1, 'a1) prod **)

let two b =
  let Coq_pair (y, t0) = pop (S O) b in
  let Coq_pair (y0, _) = pop O t0 in Coq_pair (y, y0)

(** val has1 : nat -> 'a1 t -> 'a1 pt option **)

let has1 q b =
  match q with
  | O -> None
  | S _ -> Some b

(** val has5 :
    nat -> 'a1 t -> (((('a1, 'a1) prod, 'a1) prod, 'a1) prod, 'a1 pt) sum **)

let has5 q b =
  match q with
  | O ->
    let Coq_pair (p, t0) =
      pop2 (S
        (let rec add0 n m =
           match n with
           | O -> m
           | S p -> S (add0 p m)
         in add0 (S O) O)) b
    in
    let Coq_pair (y, y0) = two t0 in
    Coq_inl (Coq_pair ((Coq_pair (p, y)), y0))
  | S _ -> Coq_inr b

(** val has5p2 :
    nat -> 'a1 t -> ('a1 vector, (('a1 pt, 'a1) prod, 'a1) prod) sum **)

let has5p2 q b =
  match q with
  | O ->
    let Coq_pair (y, _) = pop O b in Coq_inl (V1 ((S (S (S (S (S O))))), y))
  | S n ->
    (match n with
     | O ->
       let Coq_pair (y, y0) = two b in Coq_inl (V2 ((S (S (S (S O)))), y, y0))
     | S n0 ->
       (match n0 with
        | O ->
          let Coq_pair (p, t0) = pop2 (S O) b in
          let Coq_pair (y, y0) = p in
          let Coq_pair (y1, _) = pop O t0 in
          Coq_inl (V3 ((S (S (S O))), y, y0, y1))
        | S n1 ->
          (match n1 with
           | O ->
             let Coq_pair (p, t0) = pop2 (S (S O)) b in
             let Coq_pair (y, y0) = p in
             let Coq_pair (y1, y2) = two t0 in
             Coq_inl (V4 ((S (S O)), y, y0, y1, y2))
           | S n2 ->
             (match n2 with
              | O ->
                let Coq_pair (p, _) = pop5 O b in
                let Coq_pair (p0, y) = p in
                let Coq_pair (p1, y0) = p0 in
                let Coq_pair (p2, y1) = p1 in
                let Coq_pair (y2, y3) = p2 in
                Coq_inl (V5 ((S O), y2, y3, y1, y0, y))
              | S n3 ->
                (match n3 with
                 | O ->
                   let Coq_pair (p, t0) = pop5 (S O) b in
                   let Coq_pair (p0, y) = p in
                   let Coq_pair (p1, y0) = p0 in
                   let Coq_pair (p2, y1) = p1 in
                   let Coq_pair (y2, y3) = p2 in
                   let Coq_pair (y4, _) = pop O t0 in
                   Coq_inl (V6 (O, y2, y3, y1, y0, y, y4))
                 | S n4 -> Coq_inr (eject2 (S (S (S (S (S n4))))) b))))))

(** val has2p5 :
    nat -> 'a1 t -> ('a1 vector, (('a1, 'a1) prod, 'a1 pt) prod) sum **)

let has2p5 q b =
  match q with
  | O ->
    let Coq_pair (y, _) = pop O b in Coq_inl (V1 ((S (S (S (S (S O))))), y))
  | S n ->
    (match n with
     | O ->
       let Coq_pair (y, y0) = two b in Coq_inl (V2 ((S (S (S (S O)))), y, y0))
     | S n0 ->
       (match n0 with
        | O ->
          let Coq_pair (p, t0) = pop2 (S O) b in
          let Coq_pair (y, y0) = p in
          let Coq_pair (y1, _) = pop O t0 in
          Coq_inl (V3 ((S (S (S O))), y, y0, y1))
        | S n1 ->
          (match n1 with
           | O ->
             let Coq_pair (p, t0) = pop2 (S (S O)) b in
             let Coq_pair (y, y0) = p in
             let Coq_pair (y1, y2) = two t0 in
             Coq_inl (V4 ((S (S O)), y, y0, y1, y2))
           | S n2 ->
             (match n2 with
              | O ->
                let Coq_pair (p, _) = pop5 O b in
                let Coq_pair (p0, y) = p in
                let Coq_pair (p1, y0) = p0 in
                let Coq_pair (p2, y1) = p1 in
                let Coq_pair (y2, y3) = p2 in
                Coq_inl (V5 ((S O), y2, y3, y1, y0, y))
              | S n3 ->
                (match n3 with
                 | O ->
                   let Coq_pair (p, t0) = pop5 (S O) b in
                   let Coq_pair (p0, y) = p in
                   let Coq_pair (p1, y0) = p0 in
                   let Coq_pair (p2, y1) = p1 in
                   let Coq_pair (y2, y3) = p2 in
                   let Coq_pair (y4, _) = pop O t0 in
                   Coq_inl (V6 (O, y2, y3, y1, y0, y, y4))
                 | S n4 -> Coq_inr (pop2 (S (S (S (S (S n4))))) b))))))

(** val has8 :
    nat -> 'a1 t -> (((((('a1, 'a1) prod, 'a1) prod, 'a1) prod, 'a1) prod,
    'a1 vector) prod, 'a1 pt) sum **)

let has8 q b =
  match q with
  | O ->
    let Coq_pair (p, _) = pop5 O b in Coq_inl (Coq_pair (p, (V0 (S (S O)))))
  | S n ->
    (match n with
     | O ->
       let Coq_pair (p, t0) = pop5 (S O) b in
       let Coq_pair (y, _) = pop O t0 in
       Coq_inl (Coq_pair (p, (V1 ((S O), y))))
     | S n0 ->
       (match n0 with
        | O ->
          let Coq_pair (p, t0) = pop5 (S (S O)) b in
          let Coq_pair (y, y0) = two t0 in
          Coq_inl (Coq_pair (p, (V2 (O, y, y0))))
        | S _ -> Coq_inr b))

(** val has3p8 :
    nat -> 'a1 t -> ((((((((('a1, 'a1) prod, 'a1) prod, 'a1) prod, 'a1) prod,
    'a1) prod, 'a1) prod, 'a1) prod, 'a1 vector) prod, ((('a1, 'a1) prod,
    'a1) prod, 'a1 pt) prod) sum **)

let has3p8 q b =
  match q with
  | O ->
    let Coq_pair (p, t0) =
      pop5 (S
        (let rec add0 n m =
           match n with
           | O -> m
           | S p -> S (add0 p m)
         in add0 (S (S O)) O)) b
    in
    let Coq_pair (p0, t1) =
      pop2 (S
        (let rec add0 n m =
           match n with
           | O -> m
           | S p0 -> S (add0 p0 m)
         in add0 O O)) t0
    in
    let Coq_pair (y, y0) = p0 in
    let Coq_pair (y1, _) = pop O t1 in
    Coq_inl (Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair (p, y)), y0)), y1)),
    (V0 (S (S O)))))
  | S n ->
    (match n with
     | O ->
       let Coq_pair (p, t0) =
         pop5 (S
           (let rec add0 n0 m =
              match n0 with
              | O -> m
              | S p -> S (add0 p m)
            in add0 (S (S O)) (S O))) b
       in
       let Coq_pair (p0, t1) =
         pop2 (S
           (let rec add0 n0 m =
              match n0 with
              | O -> m
              | S p0 -> S (add0 p0 m)
            in add0 O (S O))) t0
       in
       let Coq_pair (y, y0) = p0 in
       let Coq_pair (y1, y2) = two t1 in
       Coq_inl (Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair (p, y)), y0)),
       y1)), (V1 ((S O), y2))))
     | S n0 ->
       (match n0 with
        | O ->
          let Coq_pair (p, t0) =
            pop5 (S
              (let rec add0 n1 m =
                 match n1 with
                 | O -> m
                 | S p -> S (add0 p m)
               in add0 (S (S O)) (S (S O)))) b
          in
          let Coq_pair (p0, _) = pop5 O t0 in
          let Coq_pair (p1, y) = p0 in
          let Coq_pair (p2, y0) = p1 in
          let Coq_pair (p3, y1) = p2 in
          let Coq_pair (y2, y3) = p3 in
          Coq_inl (Coq_pair ((Coq_pair ((Coq_pair ((Coq_pair (p, y2)), y3)),
          y1)), (V2 (O, y0, y))))
        | S n1 ->
          let Coq_pair (p, t0) =
            pop2 (S
              (let rec add0 n2 m =
                 match n2 with
                 | O -> m
                 | S p -> S (add0 p m)
               in add0 (S (S (S (S (S O))))) (S (S (S n1))))) b
          in
          let Coq_pair (y, t1) =
            pop (S
              (let rec add0 n2 m =
                 match n2 with
                 | O -> m
                 | S p0 -> S (add0 p0 m)
               in add0 (S (S (S (S O)))) (S (S (S n1))))) t0
          in
          Coq_inr (Coq_pair ((Coq_pair (p, y)), t1))))
