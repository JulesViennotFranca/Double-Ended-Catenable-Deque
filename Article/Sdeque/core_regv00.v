From Coq Require Import ssreflect.
From Coq Require Import Program List ZArith Lia.
Import ListNotations.
From Equations Require Import Equations.
From Hammer Require Import Tactics.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Color Require Import color.
Import GYR.

(* Types *)

(* In the following types, an integer parameter is introduced : the [lvl] of
   the type. The level contains information on the type of elements stored in
   the structure encoded. As elements stored in our different structure are
   iterated pairs of a type A, the level is simply the number of times we
   iterated the product on A.

   For example, a buffer of level 0 will contain elements of A, a buffer of
   level 1 will contain elements of A * A, a buffer of level 2 will contain
   elements of (A * A) * (A * A), and so on ... *)

(* A type for buffers. *)

Inductive buffer (A : Type) : color -> Type :=
  | B0 : buffer A red
  | B1 : A -> buffer A yellow
  | B2 : A -> A -> buffer A green
  | B3 : A -> A -> A -> buffer A green
  | B4 : A -> A -> A -> A -> buffer A yellow
  | B5 : A -> A -> A -> A -> A -> buffer A red.
Arguments B0 {A}.
Arguments B1 {A}.
Arguments B2 {A}.
Arguments B3 {A}.
Arguments B4 {A}.
Arguments B5 {A}.


(* A type for yellow buffers. *)

Inductive yellow_buffer : Type -> Type :=
  | Yellowish {A G Y} :
    buffer A (Mix G Y NoRed) -> yellow_buffer A.

(*
(* A type for any buffers. *)

Inductive any_buffer (A: Type) (lvl : nat) : Type :=
  | Any {G Y R} : buffer A lvl (Mix G Y R) -> any_buffer A lvl.
Arguments Any {A lvl G Y R}. *)

(* A type for packet. *)

Inductive packet : Type -> Type -> color -> Type :=
  | Hole {A : Type} : packet A A uncolored
  | Green_node {A B : Type} {Y : yellow_hue} :
    buffer A green ->
    packet (A * A) B (Mix NoGreen Y NoRed) ->
    buffer A green ->
    packet A B green
  | Yellow_node {A B : Type} {GP GS : green_hue} {YP Y YS : yellow_hue} :
    buffer A (Mix GP YP NoRed) ->
    packet (A * A) B (Mix NoGreen Y NoRed) ->
    buffer A (Mix GS YS NoRed) ->
    packet A B yellow
  | Red_node {A B : Type} {CP CS : color} {Y : yellow_hue} :
    buffer A CP ->
    packet (A * A) B (Mix NoGreen Y NoRed) ->
    buffer A CS ->
    packet A B red.

Inductive regularity : color -> color -> Type :=
  | G {G R} : regularity green (Mix G NoYellow R)
  | Y : regularity yellow green
  | R : regularity red    green.

(* A type for chain. *)

Inductive chain : Type -> color -> Type :=
  | Ending {A : Type} {C : color} : buffer A C -> chain A green
  | Chain {A B : Type} {C1 C2 : color} :
    regularity C1 C2 ->
    packet A B C1 ->
    chain B C2 ->
    chain A C1.

(*
(* The leveled decompose type. *)

Inductive decompose (A : Type) (lvl : nat) : Type :=
| Underflow : option (prodN A lvl) -> decompose A lvl
| Ok : buffer A lvl green -> decompose A lvl
| Overflow : buffer A lvl green -> prodN A (S lvl) -> decompose A lvl.

Arguments Underflow {_ _}.
Arguments Ok {_ _}.
Arguments Overflow {_ _}.

(* The leveled sandwich type. *)

Inductive sandwich (A : Type) (lvl : nat) : Type :=
| Alone : option (prodN A lvl) -> sandwich A lvl
| Sandwich {C} : prodN A lvl -> buffer A lvl C -> prodN A lvl -> sandwich A lvl.
Arguments Alone {A lvl}.
Arguments Sandwich {A lvl C}. *)

(* A type for deque. *)

Inductive deque : Type -> Type :=
  | T {A G Y} : chain A (Mix G Y NoRed) -> deque A.

(* Models *)

Set Equations Transparent.


Opaque app.
Definition singleton {A : Type} (x : A) : list A := [x].
Opaque singleton.

(*
(* A list of tactics to be used when trying to resolve obligations generated by
   Equations. *)

#[export] Hint Rewrite <-app_assoc : rlist.
#[export] Hint Rewrite <-app_comm_cons : rlist.
#[export] Hint Rewrite app_nil_r : rlist.

#[local] Obligation Tactic :=
  try first [ done | cbn; hauto db:rlist ]. *)

(* Returns the sequence contained in an option. *)

Equations option_seq {A} : option A -> list A :=
option_seq None := [];
option_seq (Some x) := [x].

(* Returns the sequence contained in a buffer. *)

Equations buffer_seq {A C} : buffer A C -> list A :=
buffer_seq B0 := [];
buffer_seq (B1 a) := [a];
buffer_seq (B2 a b) := [a] ++ [b];
buffer_seq (B3 a b c) := [a] ++ [b] ++ [c];
buffer_seq (B4 a b c d) := [a] ++ [b] ++ [c] ++ [d];
buffer_seq (B5 a b c d e) := [a] ++ [b] ++ [c] ++ [d] ++ [e].


(* Returns the sequence contained in a yellow buffer. *)

Equations yellow_buffer_seq {A} : yellow_buffer A -> list A :=
yellow_buffer_seq (Yellowish buf) := buffer_seq buf.

(*
(* Returns the sequence contained in any buffer. *)

Equations any_buffer_seq {A lvl} : any_buffer A lvl -> list A :=
any_buffer_seq (Any buf) := buffer_seq buf. *)

(* Transforms a list of pairs into a list, preserving the order. *)

Equations flattenp {A} (l : list (A * A)) : list A :=
flattenp [] := [];
flattenp ((x, y) :: l) := [x] ++ [y] ++ flattenp l.

Equations packet_seq {A B C} : packet A B C -> list B -> list A :=
packet_seq Hole l := l;
packet_seq (Green_node p pkt s) l :=
  buffer_seq p ++ flattenp (packet_seq pkt l) ++ buffer_seq s;
packet_seq (Yellow_node p pkt s) l :=
  buffer_seq p ++ flattenp (packet_seq pkt l) ++ buffer_seq s;
packet_seq (Red_node p pkt s) l :=
  buffer_seq p ++ flattenp (packet_seq pkt l) ++ buffer_seq s.

(* Returns the sequence of elements stored in prefix buffers along a
   packet. *)

(* Equations packet_left_seq {A B C} : packet A B C -> list A :=
packet_left_seq Hole := [];
packet_left_seq (Green_node buf1 p _) :=
  buffer_seq buf1 ++ flattenp (packet_left_seq p);
packet_left_seq (Yellow_node buf1 p _) :=
  buffer_seq buf1 ++ flattenp (packet_left_seq p);
packet_left_seq (Red_node buf1 p _) :=
  buffer_seq buf1 ++ flattenp (packet_left_seq p).

(* Returns the sequence of elements stored in suffix buffers along a
   packet. *)

Equations packet_right_seq {A B C} : packet A B C -> list A :=
packet_right_seq Hole := [];
packet_right_seq (Green_node _ p buf2) :=
  flattenp (packet_right_seq p) ++ buffer_seq buf2;
packet_right_seq (Yellow_node _ p buf2) :=
  flattenp (packet_right_seq p) ++ buffer_seq buf2;
packet_right_seq (Red_node _ p buf2) :=
  flattenp (packet_right_seq p) ++ buffer_seq buf2.

Equations flattenpkt {A B C} : packet A B C -> list B -> list A :=
flattenpkt Hole l := l;
flattenpkt (Green_node  _ p _) l := flattenp (flattenpkt p l);
flattenpkt (Yellow_node _ p _) l := flattenp (flattenpkt p l);
flattenpkt (Red_node    _ p _) l := flattenp (flattenpkt p l). *)

(* Returns the sequence contained in a leveled colored deque. *)

Equations chain_seq {A C} : chain A C -> list A :=
chain_seq (Ending b) := buffer_seq b;
chain_seq (Chain _ pkt cd) := packet_seq pkt (chain_seq cd).

(*
(* Returns the sequence of non-excess elements of an object of type decompose. *)

Equations decompose_main_seq {A lvl} (dec : decompose A lvl) : list A :=
decompose_main_seq (Underflow opt) := option_seq opt;
decompose_main_seq (Ok b) := buffer_seq b;
decompose_main_seq (Overflow b _) := buffer_seq b.

(* Returns the sequence of excess elements of an object of type decompose. *)

Equations decompose_rest_seq {A lvl} (dec : decompose A lvl) : list A :=
decompose_rest_seq (Underflow _) := [];
decompose_rest_seq (Ok _) := [];
decompose_rest_seq (Overflow _ p) := prodN_seq p.

(* Returns the sequence of elements of an object of type sandwich. *)

Equations sandwich_seq {A lvl} (sw : sandwich A lvl) : list A :=
sandwich_seq (Alone opt) := option_seq opt;
sandwich_seq (Sandwich x b y) := prodN_seq x ++ buffer_seq b ++ prodN_seq y. *)

(* Returns the sequence contained in a deque. *)

Equations deque_seq {A} : deque A -> list A :=
deque_seq (T dq) := chain_seq dq.

Unset Equations Transparent.

(* Definition push_green_packet {A B} (a : A) (pkt : packet A B green) :=
  match pkt in packet A B green return packet A B yellow with
  | Green_node (B0) pkt s => _
  | Green_node (B1 _) pkt s => _
  | Green_node (B2 b c) pkt s => Yellow_node (B3 a b c) pkt s
  | Green_node (B3 b c d) pkt s => Yellow_node (B4 a b c d) pkt s
  | Green_node (B4 _ _ _ _) pkt s => _
  | Green_node (B5 _ _ _ _ _) pkt s => _
  end. *)

(* Equations push_green_packet {A B} :
    A -> packet A B green -> packet A B yellow :=
push_green_packet a (Green_node (B2 b c) pkt s) := Yellow_node (B3 a b c) pkt s;
push_green_packet a (Green_node (B3 b c d) pkt s) := Yellow_node (B4 a b c d) pkt s.

Lemma push_green_packet_correct {A B} (a : A) (pkt : packet A B green) :
    packet_left_seq (push_green_packet a pkt) = [a] ++ packet_left_seq pkt.
Proof.
  dependent destruction pkt.
  dependent destruction b;
  simp push_green_packet packet_left_seq buffer_seq.
  - aac_reflexivity.
  - aac_reflexivity.
Qed. *)

Notation "? x" := (@exist _ _ x _) (at level 100).

Equations push_green_packet {A B} (a : A) (pkt : packet A B green) :
  { pkt' : packet A B yellow |
    forall (l : list B), packet_seq pkt' l = [a] ++ packet_seq pkt l } :=
push_green_packet a (Green_node(B2 b c) pkt s) :=
  ? Yellow_node (B3 a b c) pkt s;
push_green_packet a (Green_node(B3 b c d) pkt s) :=
  ? Yellow_node (B4 a b c d) pkt s.
