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

Inductive suffix' (A : Type) : Type := 
  | Suff : deque A -> suffix' A.
Arguments Suff {A}.

(* A type for prefixes, possibly of length 2, 3 or 4 and more. The color will
   be given by the number of elements. *)

Inductive prefix' (A : Type) : color -> Type := 
  | Pre2 : A -> A -> prefix' A red
  | Pre3 : A -> A -> A -> prefix' A yellow
  | Pre4 : A -> A -> A -> A -> deque A -> prefix' A green.
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
      
Inductive element (A : Type) : nat -> Type := 
  | ZElt : A -> element A 0 
  | SElt {lvl : nat} {C1 C2 : color} : 
      prefix' (element A lvl) C1 -> 
      csteque A (S lvl) C2 -> 
      element A (S lvl)
 
   (* Packets represents the same concept as before : either a Hole, the end of 
   the packet, or a triple prefix - next packet - suffix, with the next packet
   being of one level higher, and yellow or uncolored. *)

with packet (A : Type) : nat -> nat -> color -> Type := 
  | Hole {lvl : nat} : packet A lvl 0 uncolored 
  | Triple {lvl len : nat} {Y : yellow_hue} {C : color} : 
      prefix' (element A lvl) C -> 
      packet A (S lvl) len (Mix NoGreen Y NoRed) ->
      suffix' (element A lvl) ->
      packet A lvl (S len) C

   (* Colored steques also look similar to colored deque in our previous structure,
   it is either Small, only made of a suffix, or big, made of one packet and a 
   following colored steque. *)

with csteque (A : Type) : nat -> color -> Type := 
  | Small {lvl : nat} : 
      suffix' (element A lvl) -> 
      csteque A lvl green 
  | Big {lvl len nlvl : nat} {C1 C2 C3 : color} :
      packet A lvl len C1 ->
      csteque A nlvl C2 ->
      nlvl = len + lvl ->
      csteque_color C1 C2 C3 ->
      csteque A lvl C3.
    
Arguments ZElt {A}.
Arguments SElt {A lvl C1 C2}.
Arguments Hole {A lvl}.
Arguments Triple {A lvl len Y C}.
Arguments Small {A lvl}.
Arguments Big {A lvl len nlvl C1 C2 C3}.

Definition suffix A lvl := suffix' (element A lvl).
Definition prefix A lvl := prefix' (element A lvl).

(* A type for steque. *)

Inductive steque (A : Type) : Type := 
  T : forall (G : green_hue) (Y : yellow_hue), 
      csteque A 0 (Mix G Y NoRed) -> 
      steque A.
Arguments T {A G Y}.

(* Models *)

Set Equations Transparent.

Fixpoint element_seq {A lvl} (e : element A lvl) : list A :=
  let fix prodN_seq {lvle lvlp} (p : prodN (element A lvle) lvlp) : list A :=
    match p with 
    | prodZ e => element_seq e
    | prodS p1 p2 => prodN_seq p1 ++ prodN_seq p2
    end in
  let buffer_seq {lvle lvlp C} (b : buffer (element A lvle) lvlp C) : list A :=
    match b with 
    | B0 => []
    | B1 p1 => prodN_seq p1
    | B2 p1 p2 => prodN_seq p1 ++ prodN_seq p2 
    | B3 p1 p2 p3 => prodN_seq p1 ++ prodN_seq p2 ++ prodN_seq p3
    | B4 p1 p2 p3 p4 => prodN_seq p1 ++ prodN_seq p2 ++ prodN_seq p3 ++ prodN_seq p4
    | B5 p1 p2 p3 p4 p5 => prodN_seq p1 ++ prodN_seq p2 ++ prodN_seq p3 ++ prodN_seq p4 ++ prodN_seq p5
    end in 
  let fix dpacket_front_seq {lvle lvlp len C} (pkt : lvl_packet (element A lvle) lvlp len C) : list A :=
    match pkt with 
    | lvlproof.Hole => []
    | lvlproof.Triple p pkt _ _ => buffer_seq p ++ dpacket_front_seq pkt 
    end in
  let fix dpacket_rear_seq {lvle lvlp len C} (pkt : lvl_packet (element A lvle) lvlp len C) : list A :=
    match pkt with 
    | lvlproof.Hole => []
    | lvlproof.Triple _ pkt s _ => dpacket_rear_seq pkt ++ buffer_seq s
    end in
  let fix cdeque_seq {lvle lvlp C} (cd : lvl_cdeque (element A lvle) lvlp C) : list A :=
    match cd with
    | lvlproof.Small b => buffer_seq b
    | lvlproof.Big pkt cd _ _ => dpacket_front_seq pkt ++ cdeque_seq cd ++ dpacket_rear_seq pkt
    end in
  let prefix_seq {lvl C} (p : prefix A lvl C) : list A :=
    match p with 
    | Pre2 e1 e2 => element_seq e1 ++ element_seq e2 
    | Pre3 e1 e2 e3 => element_seq e1 ++ element_seq e2 ++ element_seq e3
    | Pre4 e1 e2 e3 e4 (lvlproof.T d) => 
      element_seq e1 ++ element_seq e2 ++ element_seq e3 ++ element_seq e4 ++ cdeque_seq d
    end in
  let fix packet_front_seq {lvl len C} (pkt : packet A lvl len C) : list A :=
    match pkt with
    | Hole => []
    | Triple p pkt _ => prefix_seq p ++ packet_front_seq pkt
    end in
  let fix packet_rear_seq {lvl len C} (pkt : packet A lvl len C) : list A :=
    match pkt with
    | Hole => []
    | Triple _ pkt (Suff (lvlproof.T d)) => packet_rear_seq pkt ++ cdeque_seq d
    end in
  let fix csteque_seq {lvl C} (cs : csteque A lvl C) : list A :=
    match cs with 
    | Small (Suff (lvlproof.T d)) => cdeque_seq d
    | Big pkt cs _ _ => packet_front_seq pkt ++ csteque_seq cs ++ packet_rear_seq pkt
    end in
  match e with 
  | ZElt a => [a]
  | SElt p cs => prefix_seq p ++ csteque_seq cs 
  end.

Equations suffix_seq {A lvl} : suffix A lvl -> list A := 
suffix_seq (Suff d) := concat (map element_seq (deque_seq d)).

Equations prefix_seq {A lvl C} : prefix A lvl C -> list A :=
prefix_seq (Pre2 e1 e2) := element_seq e1 ++ element_seq e2;
prefix_seq (Pre3 e1 e2 e3) := element_seq e1 ++ element_seq e2 ++ element_seq e3;
prefix_seq (Pre4 e1 e2 e3 e4 d) := element_seq e1 ++ element_seq e2 ++ element_seq e3 ++ element_seq e4 ++
                                   concat (map element_seq (deque_seq d)).

Equations packet_front_seq {A lvl len C} : packet A lvl len C -> list A :=
packet_front_seq Hole := [];
packet_front_seq (Triple p pkt _) := prefix_seq p ++ packet_front_seq pkt.

Equations packet_rear_seq {A lvl len C} : packet A lvl len C -> list A :=
packet_rear_seq Hole := [];
packet_rear_seq (Triple _ pkt s) := packet_rear_seq pkt ++ suffix_seq s.

Equations csteque_seq {A lvl C} : csteque A lvl C -> list A :=
csteque_seq (Small s) := suffix_seq s;
csteque_seq (Big pkt cs eq_refl _) := packet_front_seq pkt ++ csteque_seq cs ++ packet_rear_seq pkt.

Unset Equations Transparent.

Notation "? x" := (@exist _ _ x _) (at level 100).

(* Functions *)