open Datatypes
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

val seq : nat -> 'a1 t -> 'a1 list

val vector_seq : nat -> 'a1 vector -> 'a1 list

val map_buffer : (nat -> 'a1 -> 'a2 list) -> nat -> nat -> 'a1 t -> 'a2 list

val empty : 'a1 t

val vector_length : nat -> 'a1 vector -> nat

val translate : nat -> nat -> 'a1 t -> 'a1 t

val push : nat -> 'a1 -> 'a1 t -> 'a1 t

val inject : nat -> 'a1 t -> 'a1 -> 'a1 t

val pop : nat -> 'a1 t -> ('a1, 'a1 t) prod

val eject : nat -> 'a1 t -> ('a1 t, 'a1) prod

val push2 : nat -> 'a1 -> 'a1 -> 'a1 t -> 'a1 t

val inject2 : nat -> 'a1 t -> 'a1 -> 'a1 -> 'a1 t

val pop2 : nat -> 'a1 t -> (('a1, 'a1) prod, 'a1 t) prod

val eject2 : nat -> 'a1 t -> (('a1 t, 'a1) prod, 'a1) prod

val two : 'a1 t -> ('a1, 'a1) prod

val single : 'a1 -> 'a1 t

val pair : 'a1 -> 'a1 -> 'a1 t

val push3 : nat -> 'a1 -> 'a1 -> 'a1 -> 'a1 t -> 'a1 t

val inject3 : nat -> 'a1 t -> 'a1 -> 'a1 -> 'a1 -> 'a1 t

val push5 : nat -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 t -> 'a1 t

val inject5 : nat -> 'a1 t -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 t

val pop5 :
  nat -> 'a1 t -> ((((('a1, 'a1) prod, 'a1) prod, 'a1) prod, 'a1) prod, 'a1
  t) prod

val push6 : nat -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 t -> 'a1 t

val inject6 : nat -> 'a1 t -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 t

val inject8 :
  nat -> 'a1 t -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  t

val pop8 :
  nat -> 'a1 t -> (((((((('a1, 'a1) prod, 'a1) prod, 'a1) prod, 'a1) prod,
  'a1) prod, 'a1) prod, 'a1) prod, 'a1 t) prod

val push_vector : nat -> nat -> 'a1 vector -> 'a1 t -> 'a1 t

val inject_vector : nat -> nat -> 'a1 t -> 'a1 vector -> 'a1 t

val push_5vector :
  nat -> nat -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vector -> 'a1 t -> 'a1
  t

val inject_5vector :
  nat -> nat -> 'a1 t -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vector -> 'a1
  t

val has1 : nat -> 'a1 t -> 'a1 pt option

val has3 : nat -> 'a1 t -> ('a1 vector, 'a1 pt) sum

val has5 :
  nat -> 'a1 t -> (((('a1, 'a1) prod, 'a1) prod, 'a1) prod, 'a1 pt) sum

val has7 : nat -> 'a1 t -> ('a1 vector, 'a1 pt) sum

val has8 :
  nat -> 'a1 t -> (((((('a1, 'a1) prod, 'a1) prod, 'a1) prod, 'a1) prod, 'a1
  vector) prod, 'a1 pt) sum

val has3p :
  nat -> 'a1 t -> ((('a1, 'a1) prod, 'a1) prod, ('a1 vector, 'a1 pt) sum) prod

val has3s :
  nat -> 'a1 t -> (('a1 vector, 'a1 pt) sum, (('a1, 'a1) prod, 'a1) prod) prod

val has3p8 :
  nat -> 'a1 t -> ((((((((('a1, 'a1) prod, 'a1) prod, 'a1) prod, 'a1) prod,
  'a1) prod, 'a1) prod, 'a1) prod, 'a1 vector) prod, ('a1 t, 'a1 pt) prod) sum
