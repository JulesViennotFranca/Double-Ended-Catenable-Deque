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
      lvl_csteque A (S lvl) C2 -> 
      element A (S lvl)
 
   (* Packets represents the same concept as before : either a Hole, the end of 
   the packet, or a triple prefix - next packet - suffix, with the next packet
   being of one level higher, and yellow or uncolored. *)

with lvl_packet (A : Type) : nat -> nat -> color -> Type := 
  | Hole {lvl : nat} : lvl_packet A lvl 0 uncolored 
  | Triple {lvl len : nat} {Y : yellow_hue} {C : color} : 
      prefix' (element A lvl) C -> 
      lvl_packet A (S lvl) len (Mix NoGreen Y NoRed) ->
      suffix' (element A lvl) ->
      lvl_packet A lvl (S len) C

   (* Colored steques also look similar to colored deque in our previous structure,
   it is either Small, only made of a suffix, or big, made of one packet and a 
   following colored steque. *)

with lvl_csteque (A : Type) : nat -> color -> Type := 
  | Small {lvl : nat} : 
      suffix' (element A lvl) -> 
      lvl_csteque A lvl green 
  | Big {lvl len nlvl : nat} {C1 C2 C3 : color} :
      lvl_packet A lvl len C1 ->
      lvl_csteque A nlvl C2 ->
      nlvl = len + lvl ->
      csteque_color C1 C2 C3 ->
      lvl_csteque A lvl C3.
    
Arguments ZElt {A}.
Arguments SElt {A lvl C1 C2}.
Arguments Hole {A lvl}.
Arguments Triple {A lvl len Y C}.
Arguments Small {A lvl}.
Arguments Big {A lvl len nlvl C1 C2 C3}.

Definition suffix A lvl := suffix' (element A lvl).
Definition prefix A lvl := prefix' (element A lvl).

(* A type for colored steque. *)

Definition csteque (A : Type) := lvl_csteque A 0.

(* A type for steque. *)

Inductive steque (A : Type) : Type := 
  T : forall (G : green_hue) (Y : yellow_hue), 
      csteque A (Mix G Y NoRed) -> 
      steque A.
Arguments T {A G Y}.

(* Models *)

Set Equations Transparent.

Opaque app.
Definition singleton {A : Type} (x : A) : list A := [x].
Opaque singleton.

Program Fixpoint prodN_concat_map {A B lvle lvlp} (f : A -> list B) (p : prodN (element A lvle) lvlp) : list B :=
    match p with 
    | prodZ a => element_concat_map f a 
    | prodS (p1, p2) => prodN_concat_map f p1 ++ prodN_concat_map f p2 
    end

with buffer_concat_map {A B lvle lvlp C} (f : A -> list B) (b : buffer (element A lvle) lvlp C) : list B :=
    match b with 
    | B0 => []
    | (B1 a) => prodN_concat_map f a
    | (B2 a b) => prodN_concat_map f a ++ prodN_concat_map f b
    | (B3 a b c) => prodN_concat_map f a ++ prodN_concat_map f b ++ prodN_concat_map f c
    | (B4 a b c d) => prodN_concat_map f a ++ prodN_concat_map f b ++ prodN_concat_map f c ++ prodN_concat_map f d
    | (B5 a b c d e) => prodN_concat_map f a ++ prodN_concat_map f b ++ prodN_concat_map f c ++ prodN_concat_map f d ++ prodN_concat_map f e
    end 

with dpacket_front_concat_map {A B lvle lvlp len C} (f : A -> list B) (pkt : lvlproof.lvl_packet (element A lvle) lvlp len C) : list B :=
    match pkt with 
    | lvlproof.Hole => []
    | (lvlproof.Triple p pkt _ _) => buffer_concat_map f p ++ dpacket_front_concat_map f pkt
    end

with dpacket_rear_concat_map {A B lvle lvlp len C} (f : A -> list B) (pkt : lvlproof.lvl_packet (element A lvle) lvlp len C) : list B :=
    match pkt with 
    | lvlproof.Hole => []
    | (lvlproof.Triple _ pkt s _) => dpacket_rear_concat_map f pkt ++ buffer_concat_map f s
    end

with cdeque_concat_map {A B lvle lvlp C} (f : A -> list B) (cd : lvl_cdeque (element A lvle) lvlp C) : list B :=
    match cd with 
    | (lvlproof.Small b) => buffer_concat_map f b
    | (lvlproof.Big pkt cd _ _) => 
        dpacket_front_concat_map f pkt ++
        cdeque_concat_map f cd ++
        dpacket_rear_concat_map f pkt
    end

with deque_concat_map {A B lvle} (f : A -> list B) (d : deque (element A lvle)) : list B :=
    match d with lvlproof.T dq => cdeque_concat_map f dq end

with suffix_concat_map {A B lvl} (f : A -> list B) (s : suffix A lvl) : list B := 
    match s with Suff d => deque_concat_map f d end

with prefix_concat_map {A B lvl C} (f : A -> list B) (p : prefix A lvl C) : list B := 
    match p with 
    | (Pre2 a b) => element_concat_map f a ++ element_concat_map f b
    | (Pre3 a b c) => element_concat_map f a ++ element_concat_map f b ++ element_concat_map f c
    | (Pre4 a b c d e) => element_concat_map f a ++ element_concat_map f b ++ element_concat_map f c ++ element_concat_map f d ++ deque_concat_map f e
    end

with element_concat_map {A B lvl} (f : A -> list B) (elt : element A lvl) : list B := 
    match elt with
    | (ZElt a) => f a
    | (SElt p cs) => prefix_concat_map f p ++ csteque_concat_map f cs
    end

with packet_front_concat_map {A B lvl len C} (f : A -> list B) (pkt : lvl_packet A lvl len C) : list B := 
    match pkt with
    | Hole => []
    | (Triple p pkt _) => prefix_concat_map f p ++ packet_front_concat_map f pkt
    end

with packet_rear_concat_map {A B lvl len C} (f : A -> list B) (pkt : lvl_packet A lvl len C) : list B :=
    match pkt with
    | Hole => []
    | (Triple _ pkt s) => packet_rear_concat_map f pkt ++ suffix_concat_map f s 
    end

with csteque_concat_map {A B lvl C} (f : A -> list B) (cs : lvl_csteque A lvl C) : list B :=
    match cs with
    | (Small s) => suffix_concat_map f s
    | (Big pkt cs _ _) => 
        packet_front_concat_map f pkt ++
        csteque_concat_map f cs ++
        packet_rear_concat_map f pkt
    end.

Equations prodN_concat_map {A B lvl} : (A -> list B) -> prodN A lvl -> list B := 
prodN_concat_map f (prodZ a) := f a;
prodN_concat_map f (prodS (p1, p2)) := prodN_concat_map f p1 ++ prodN_concat_map f p2.

Equations buffer_concat_map {A B lvl C} : (A -> list B) -> buffer A lvl C -> list B :=
buffer_concat_map _ B0 := [];
buffer_concat_map f (B1 a) := prodN_concat_map f a;
buffer_concat_map f (B2 a b) := prodN_concat_map f a ++ prodN_concat_map f b;
buffer_concat_map f (B3 a b c) := prodN_concat_map f a ++ prodN_concat_map f b ++ prodN_concat_map f c;
buffer_concat_map f (B4 a b c d) := prodN_concat_map f a ++ prodN_concat_map f b ++ prodN_concat_map f c ++ prodN_concat_map f d;
buffer_concat_map f (B5 a b c d e) := prodN_concat_map f a ++ prodN_concat_map f b ++ prodN_concat_map f c ++ prodN_concat_map f d ++ prodN_concat_map f e.

Equations dpacket_front_concat_map {A B lvl len C} : (A -> list B) -> lvlproof.lvl_packet A lvl len C -> list B :=
dpacket_front_concat_map _ lvlproof.Hole := [];
dpacket_front_concat_map f (lvlproof.Triple p pkt _ _) := 
  buffer_concat_map f p ++ dpacket_front_concat_map f pkt.

Equations dpacket_rear_concat_map {A B lvl len C} : (A -> list B) -> lvlproof.lvl_packet A lvl len C -> list B :=
dpacket_rear_concat_map _ lvlproof.Hole := [];
dpacket_rear_concat_map f (lvlproof.Triple _ pkt s _) := 
  dpacket_rear_concat_map f pkt ++ buffer_concat_map f s.

Equations cdeque_concat_map {A B lvl C} : (A -> list B) -> lvl_cdeque A lvl C -> list B :=
cdeque_concat_map f (lvlproof.Small b) := buffer_concat_map f b;
cdeque_concat_map f (lvlproof.Big pkt cd _ _) := 
    dpacket_front_concat_map f pkt ++
    cdeque_concat_map f cd ++
    dpacket_rear_concat_map f pkt.

Equations deque_concat_map {A B} : (A -> list B) -> deque A -> list B :=
deque_concat_map f (lvlproof.T dq) := cdeque_concat_map f dq.

Equations suffix'_concat_map {A B} : (A -> list B) -> suffix' A -> list B :=
suffix'_concat_map f (Suff d) := deque_concat_map f d.

Equations prefix'_concat_map {A B C} : (A -> list B) -> prefix' A C -> list B := 
prefix'_concat_map f (Pre2 a b) := f a ++ f b;
prefix'_concat_map f (Pre3 a b c) := f a ++ f b ++ f c;
prefix'_concat_map f (Pre4 a b c d e) := f a ++ f b ++ f c ++ f d ++ deque_concat_map f e.

(* Program Fixpoint element_concat_map {A B lvl} (f : A -> list B) (elt : element A lvl) {struct elt} : list B := 
    match elt with
    | (ZElt a) => f a
    | (SElt p cs) => prefix'_concat_map (fun elt => element_concat_map f elt) p ++ csteque_concat_map f cs
    end

with packet_front_concat_map {A B lvl len C} (f : A -> list B) (pkt : lvl_packet A lvl len C) {struct pkt} : list B := 
    match pkt with
    | Hole => []
    | (Triple p pkt _) => prefix'_concat_map (fun elt => element_concat_map f elt) p ++ packet_front_concat_map f pkt
    end

with packet_rear_concat_map {A B lvl len C} (f : A -> list B) (pkt : lvl_packet A lvl len C) {struct pkt} : list B :=
    match pkt with
    | Hole => []
    | (Triple _ pkt s) => packet_rear_concat_map f pkt ++ suffix'_concat_map (fun elt => element_concat_map f elt) s 
    end

with csteque_concat_map {A B lvl C} (f : A -> list B) (cs : lvl_csteque A lvl C) {struct cs} : list B :=
    match cs with
    | (Small s) => suffix'_concat_map (fun elt => element_concat_map f elt) s
    | (Big pkt cs _ _) => 
        packet_front_concat_map f pkt ++
        csteque_concat_map f cs ++
        packet_rear_concat_map f pkt
    end. *)

Inductive seq_kind : Type := Element | FPacket | RPacket | CSteque.

Definition seq_struct (k : seq_kind) A lvl len C :=
    match k with 
    | Element => element A lvl
    | FPacket | RPacket => lvl_packet A lvl len C 
    | CSteque => lvl_csteque A lvl C
      end.

#[local] Obligation Tactic := try first [assumption | exact uncolored | lia].

Equations structure_seq (k : seq_kind) {A lvl len C}
    (s : seq_struct k A lvl len C) : list A := 
structure_seq Element (ZElt a) := [a];
structure_seq Element (SElt p cs) := 
    prefix'_concat_map (structure_seq Element) p ++
    structure_seq CSteque cs;
structure_seq FPacket Hole := [];
structure_seq FPacket (Triple p pkt _) := 
    prefix'_concat_map (structure_seq Element) p ++   
    structure_seq FPacket pkt;
structure_seq RPacket Hole := [];
structure_seq RPacket (Triple _ pkt s) :=
    structure_seq RPacket pkt ++
    suffix'_concat_map (structure_seq Element) s;
structure_seq CSteque (Small s) := 
    suffix'_concat_map (structure_seq Element) s;
structure_seq CSteque (Big pkt cs eq_refl _) := 
    structure_seq FPacket pkt ++
    structure_seq CSteque cs ++
    structure_seq RPacket pkt.