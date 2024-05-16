From Coq Require Import ssreflect.
From Coq Require Import Program List Lia.
Import ListNotations.
From Equations Require Import Equations.
From Hammer Require Import Tactics.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Dequeue Require Import lvlproof.

(* Types *)

(* Here, [green_hue], [yellow_hue], and [red_hue] will be utilized to generate 
   the colors essential for our program. They function as boolean variables, 
   indicating whether or not a specific hue is present in our color. *)

Inductive green_hue  : Type := SomeGreen  | NoGreen.
Inductive yellow_hue : Type := SomeYellow | NoYellow.
Inductive red_hue    : Type := SomeRed    | NoRed.

(* Colors are generated through the constructor [Mix], which accepts amount 
   of each hue as arguments. *)

Inductive color : Type :=
  | Mix : green_hue -> yellow_hue -> red_hue -> color.

(* In order for [Equations] to work on hues and colors, instances of 
   [NoConfusion] are added to these types. *)

Derive NoConfusion for green_hue.
Derive NoConfusion for yellow_hue.
Derive NoConfusion for red_hue.
Derive NoConfusion for color.

(* Some basic colors that we'll need. *)

Notation green := (Mix SomeGreen NoYellow NoRed).
Notation yellow := (Mix NoGreen SomeYellow NoRed).
Notation orange := (Mix NoGreen SomeYellow SomeRed).
Notation red := (Mix NoGreen NoYellow SomeRed).
Notation uncolored := (Mix NoGreen NoYellow NoRed).

(* A type for suffixes, simply the final type of the previous structure. *)

Inductive suffix (A : Type) : Type := 
  | Suff : deque A -> suffix A.
Arguments Suff {A}.

(* A type for prefixes, possibly of length 2, 3 or 4 and more. The color will
   be given by the number of elements. *)

Inductive prefix (A : Type) : color -> Type := 
  | Pre2 : A -> A -> prefix A red
  | Pre3 : A -> A -> A -> prefix A yellow
  | Pre4 : A -> A -> A -> A -> deque A -> prefix A green.
Arguments Pre2 {A}.
Arguments Pre3 {A}.
Arguments Pre4 {A}.

(* A relation between the packet, the following steque and the current steque 
   colors. *)

Inductive csteque_color : color -> color -> color -> Type := 
  | CCGreen {G R} : csteque_color green (Mix G NoYellow R) green
  | CCYellow : csteque_color yellow green yellow 
  | CCOrange : csteque_color yellow red orange
  | CCRed : csteque_color red green red.

(* The mutally recursive definition of elements, packets and colored steque. 
   
   Elements represents the types of elements stored. At level 0, elements of 
   type A are stored. When the level increase, elements of the new level are 
   made of a prefix of elements of the previous level and a colored steque of 
   the new level. *)
      
Inductive element (A : Type) : nat -> nat -> Type := 
  | ZElt {dpt : nat} : A -> element A 0 dpt
  | SElt {lvl dpt : nat} {C1 C2 : color} : 
      prefix (element A lvl dpt) C1 -> 
      lvl_csteque A (S lvl) dpt C2 -> 
      element A (S lvl) (S dpt)
 
   (* Packets represents the same concept as before : either a Hole, the end of 
   the packet, or a triple prefix - next packet - suffix, with the next packet
   being of one level higher, and yellow or uncolored. *)

with lvl_packet (A : Type) : nat -> nat -> nat -> color -> Type := 
  | Hole {lvl dpt : nat} : lvl_packet A lvl 0 dpt uncolored 
  | Triple {lvl len dpt : nat} {Y : yellow_hue} {C : color} : 
      prefix (element A lvl dpt) C -> 
      lvl_packet A (S lvl) len dpt (Mix NoGreen Y NoRed) ->
      suffix (element A lvl dpt) ->
      lvl_packet A lvl (S len) (S dpt) C

   (* Colored steques also look similar to colored deque in our previous structure,
   it is either Small, only made of a suffix, or big, made of one packet and a 
   following colored steque. *)

with lvl_csteque (A : Type) : nat -> nat -> color -> Type := 
  | Small {lvl dpt : nat} : 
      suffix (element A lvl dpt) -> 
      lvl_csteque A lvl (S dpt) green 
  | Big {lvl len dpt nlvl : nat} {C1 C2 C3 : color} :
      lvl_packet A lvl len dpt C1 ->
      lvl_csteque A nlvl dpt C2 ->
      nlvl = len + lvl ->
      csteque_color C1 C2 C3 ->
      lvl_csteque A lvl (S (len + dpt)) C3.
    
Arguments ZElt {A}.
Arguments SElt {A lvl dpt C1 C2}.
Arguments Hole {A lvl dpt}.
Arguments Triple {A lvl len dpt Y C}.
Arguments Small {A lvl dpt}.
Arguments Big {A lvl} len dpt {nlvl C1 C2 C3}.

(* A type for colored steque. *)

Definition csteque (A : Type) := lvl_csteque A 0.

(* A type for steque. *)

Inductive steque (A : Type) : Type := 
  T : forall (dpt : nat) (G : green_hue) (Y : yellow_hue), 
      csteque A dpt (Mix G Y NoRed) -> 
      steque A.
Arguments T {A dpt G Y}.

(* Models *)