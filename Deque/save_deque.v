From Coq Require Import ssreflect.
From Coq Require Import Program List ZArith Lia.
Import ListNotations.
From Equations Require Import Equations.
From Hammer Require Import Tactics.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import buffer.

(* Types *)

Inductive preferred_child : Type :=
  | Preferred : bool -> bool -> preferred_child.

Inductive kind : Type := Only | Left | Right.

(* Here, [green_hue], [yellow_hue], [orange_hue] and [red_hue] will be utilized 
   to generate the colors essential for our program. They function as boolean 
   variables, indicating whether or not a specific hue is present in our color. *)

Inductive green_hue  : Type := SomeGreen  | NoGreen.
Inductive yellow_hue : Type := SomeYellow | NoYellow.
Inductive orange_hue : Type := SomeOrange | NoOrange.
Inductive red_hue    : Type := SomeRed    | NoRed.

(* Colors are generated through the constructor [Mix], which accepts amount 
   of each hue as arguments. *)

Inductive color : Type :=
  | Mix : green_hue -> yellow_hue -> orange_hue -> red_hue -> color.

(* In order for [Equations] to work on hues and colors, instances of 
   [NoConfusion] are added to these types. *)

Derive NoConfusion for kind.
Derive NoConfusion for green_hue.
Derive NoConfusion for yellow_hue.
Derive NoConfusion for orange_hue.
Derive NoConfusion for red_hue.
Derive NoConfusion for color.

(* Some basic colors that we'll need. *)

Notation green := (Mix SomeGreen NoYellow NoOrange NoRed).
Notation yellow := (Mix NoGreen SomeYellow NoOrange NoRed).
Notation yellorange := (Mix NoGreen SomeYellow SomeOrange NoRed).
Notation orange := (Mix NoGreen NoYellow SomeOrange NoRed).
Notation red := (Mix NoGreen NoYellow NoOrange SomeRed).

(* Types for general prefix and suffix, they are simply aliases for buffer.t. *)

Definition prefix' := buffer.t.
Definition suffix' := buffer.t.

Inductive stored_triple (A : Type) : nat -> Type :=
  | ST_ground : A -> stored_triple A 0
  | ST_prefix {lvl q : nat} : 
      prefix' (stored_triple A lvl) (3 + q) -> 
      stored_triple A (S lvl)
  | ST_triple {lvl qp qs : nat} {C : color} :
      prefix' (stored_triple A lvl) (3 + qp) -> 
      cdeque A (S lvl) C -> 
      suffix' (stored_triple A lvl) (3 + qs) -> 
      stored_triple A (S lvl)

with triple (A : Type) : nat -> nat -> kind -> kind -> color -> Type :=
  | Hole {lvl : nat} {K : kind} : 
      triple A lvl 0 K K yellorange
  | OT_prefix {lvl q : nat} : 
      prefix' (stored_triple A lvl) (S q) -> 
      triple A lvl 0 Only Only green
  | OT_green {lvl qp qs : nat} {G R} :
      prefix' (stored_triple A lvl) (8 + qp) ->
      cdeque A (S lvl) (Mix G NoYellow NoOrange R) ->
      suffix' (stored_triple A lvl) (8 + qs) -> 
      triple A lvl 0 Only Only green
  | OT_yellow {lvl len qp qs : nat} {K : kind} :
      prefix' (stored_triple A lvl) (7 + qp) ->
      packet A (S lvl) len (Preferred true false) K ->
      suffix' (stored_triple A lvl) (7 + qs) ->
      triple A lvl (S len) Only K yellow
  | OT_orange {lvl len qp qs : nat} {K : kind} :
      prefix' (stored_triple A lvl) (6 + qp) ->
      packet A (S lvl) len (Preferred false true) K ->
      suffix' (stored_triple A lvl) (6 + qs) ->
      triple A lvl (S len) Only K orange
  | OT_red {lvl qp qs : nat} :
      prefix' (stored_triple A lvl) (5 + qp) ->
      cdeque A (S lvl) green ->
      suffix' (stored_triple A lvl) (5 + qs) ->
      triple A lvl 0 Only Only red
  | LT_prefix {lvl qp : nat} :
      prefix' (stored_triple A lvl) (5 + qp) ->
      suffix' (stored_triple A lvl) 2 ->
      triple A lvl 0 Left Left green
  | LT_green {lvl qp : nat} {G R} :
      prefix' (stored_triple A lvl) (8 + qp) ->
      cdeque A (S lvl) (Mix G NoYellow NoOrange R) ->
      suffix' (stored_triple A lvl) 2 ->
      triple A lvl 0 Left Left green 
  | LT_yellow {lvl len qp : nat} {K : kind} :
      prefix' (stored_triple A lvl) (7 + qp) ->
      packet A (S lvl) len (Preferred true false) K ->
      suffix' (stored_triple A lvl) 2 ->
      triple A lvl (S len) Left K yellow
  | LT_orange {lvl len qp : nat} {K : kind} :
      prefix' (stored_triple A lvl) (6 + qp) ->
      packet A (S lvl) len (Preferred false true) K ->
      suffix' (stored_triple A lvl) 2 ->
      triple A lvl (S len) Left K orange
  | LT_red {lvl qp : nat} :
      prefix' (stored_triple A lvl) (5 + qp) ->
      cdeque A (S lvl) green ->
      suffix' (stored_triple A lvl) 2 ->
      triple A lvl 0 Left Left red
  | RT_prefix {lvl qs : nat} :
      prefix' (stored_triple A lvl) 2 ->
      suffix' (stored_triple A lvl) (5 + qs) ->
      triple A lvl 0 Right Right green
  | RT_green {lvl qs : nat} {G R} :
      prefix' (stored_triple A lvl) 2 ->
      cdeque A (S lvl) (Mix G NoYellow NoOrange R) ->
      suffix' (stored_triple A lvl) (8 + qs) ->
      triple A lvl 0 Right Right green 
  | RT_yellow {lvl len qs : nat} {K : kind} :
      prefix' (stored_triple A lvl) 2 ->
      packet A (S lvl) len (Preferred true false) K ->
      suffix' (stored_triple A lvl) (7 + qs) ->
      triple A lvl (S len) Right K yellow
  | RT_orange {lvl len qs : nat} {K : kind} :
      prefix' (stored_triple A lvl) 2 ->
      packet A (S lvl) len (Preferred false true) K ->
      suffix' (stored_triple A lvl) (6 + qs) ->
      triple A lvl (S len) Right K orange
  | RT_red {lvl qs : nat} :
      prefix' (stored_triple A lvl) 2 ->
      cdeque A (S lvl) green ->
      suffix' (stored_triple A lvl) (5 + qs) ->
      triple A lvl 0 Right Right red

with packet (A : Type) : nat -> nat -> preferred_child -> kind -> Type :=
  | Only_child {lvl len : nat} {K : kind} {Y O} {left right : bool} :
      triple A lvl len Only K (Mix NoGreen Y O NoRed) ->
      packet A lvl len (Preferred left right) K
  | Left_child {lvl len : nat} {K : kind} {Y O C} :
      triple A lvl len Left K (Mix NoGreen Y O NoRed) ->
      path A lvl Right C ->
      packet A lvl len (Preferred true false) K
  | Right_child {lvl len : nat} {K : kind} {Y O} :
      path A lvl Left green ->
      triple A lvl len Right K (Mix NoGreen Y O NoRed) ->
      packet A lvl len (Preferred false true) K

with path (A : Type) : nat -> kind -> color -> Type := 
  | Children {lvl len nlvl : nat} {K1 K2 : kind} {G Y O R} :
      triple A lvl len K1 K2 (Mix NoGreen Y O NoRed) ->
      triple A nlvl 0 K2 K2 (Mix G NoYellow NoOrange R) ->
      nlvl = len + lvl ->
      path A lvl K1 (Mix G NoYellow NoOrange R)

with cdeque (A : Type) : nat -> color -> Type :=
  | Empty {lvl : nat} : cdeque A lvl green 
  | Only_path {lvl : nat} {G R} :
      path A lvl Only (Mix G NoYellow NoOrange R) ->
      cdeque A lvl (Mix G NoYellow NoOrange R)
  | Pair_green {lvl : nat} :
      path A lvl Left green ->
      path A lvl Right green ->
      cdeque A lvl green
  | Pair_red {lvl : nat} {Cl Cr : color} :
      path A lvl Left Cl ->
      path A lvl Right Cr ->
      cdeque A lvl red.

Definition prefix (A : Type) (lvl : nat) := prefix' (stored_triple A lvl).
Definition suffix (A : Type) (lvl : nat) := suffix' (stored_triple A lvl).

Definition only_triple (A : Type) (lvl len : nat) := triple A lvl len Only.
Definition left_triple (A : Type) (lvl len : nat) := triple A lvl len Left.
Definition right_triple (A : Type) (lvl len : nat) := triple A lvl len Right.

Inductive sdeque (A : Type) (lvl : nat) : Type :=
  S : forall (C : color), cdeque A lvl C -> sdeque A lvl.

Inductive deque (A : Type) : Type :=
  T : cdeque A 0 green -> deque A.

Opaque app.
Definition singleton {A : Type} (x : A) : list A := [x].
Opaque singleton.

(* A list of tactics to be used when trying to resolve obligations generated by
   Equations. *)

#[export] Hint Rewrite <-app_assoc : rlist.
#[export] Hint Rewrite <-app_comm_cons : rlist.
#[export] Hint Rewrite app_nil_r : rlist.

#[local] Obligation Tactic :=
  try first [ done | cbn; hauto db:rlist ].