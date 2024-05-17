From Coq Require Import ssreflect.
From Coq Require Import Program List Lia.
Import ListNotations.
From Equations Require Import Equations.
From Hammer Require Import Tactics.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Dequeue Require Import lvlproof rectP.

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

Equations suffix'_seq {A} : suffix' A -> list A := 
suffix'_seq (Suff d) := deque_seq d.

Equations prefix'_seq {A C} : prefix' A C -> list A := 
prefix'_seq (Pre2 a b) := [a] ++ [b];
prefix'_seq (Pre3 a b c) := [a] ++ [b] ++ [c];
prefix'_seq (Pre4 a b c d e) := [a] ++ [b] ++ [c] ++ [d] ++ deque_seq e.

Section rect.

  Variable A : Type.

  Variable PprodN : forall {B lvl}, prodN B lvl -> Type.
  Variable Pbuffer : forall {B lvl C}, buffer B lvl C -> Type.
  Variable Pdpacket : forall {B lvl len C}, lvl_packet B lvl len C -> Type.
  Variable Pcdeque : forall {B lvl C}, lvl_cdeque B lvl C -> Type.
  Variable Pdeque : forall{B}, deque B -> Type.
  
  Print deque_rectP.

  Variable Pprefix'

  Variable Pelement : forall {lvl : nat}, element A lvl -> Type.
  Variable Ppacket : forall {lvl len : nat} {C : color}, packet A lvl len C -> Type.
  Variable Pcsteque : forall {lvl : nat} {C : color}, csteque A lvl C -> Type.

  Variable P_Pre2 : 

  Variable P_ZElt : forall (a : A), Pelement (ZElt a).

  Variable P_SElt : 
    forall {lvl : nat} {C1 C2 : color} {p : prefix A lvl C1} {cs : csteque A (S lvl) C2},
      (* list_rect (fun _ => Type) unit (fun e l tl => Pelement lvl e -> tl) (prefix'_seq p) -> *)
      Forallt Pelement (prefix'_seq p) ->
      Pcsteque cs ->
      Pelement (SElt p cs).
  (* Arguments P_SElt {lvl C1 C2 p cs}. *)

  Variable P_Hole :
    forall {lvl : nat}, Ppacket (lvl := lvl) Hole.
  (* Arguments P_Hole {lvl}. *)

  Variable P_Triple :
    forall {lvl len : nat} {Y : yellow_hue} {C : color}
           {p : prefix A lvl C} {pkt : packet A (S lvl) len (Mix NoGreen Y NoRed)} {s : suffix A lvl},
      (* list_rect (fun _ => Type) unit (fun e l tl => Pelement lvl e -> tl) (prefix'_seq p) -> *)
      Forallt Pelement (prefix'_seq p) ->
      Ppacket pkt ->
      (* list_rect (fun _ => Type) unit (fun e l tl => Pelement lvl e -> tl) (suffix'_seq s) -> *)
      Forallt Pelement (suffix'_seq s) ->
      Ppacket (Triple p pkt s).
  (* Arguments P_Triple {lvl len Y C p pkt s}. *)

  Variable P_Small :
    forall {lvl : nat} {s : suffix A lvl}, 
      (* list_rect (fun _ => Type) unit (fun e l tl => Pelement lvl e -> tl) (suffix'_seq s) -> *)
      Forallt Pelement (suffix'_seq s) ->
      Pcsteque (Small s).
  (* Arguments P_Small {lvl s}. *)

  Variable P_Big : 
    forall {lvl len nlvl : nat} {C1 C2 C3 : color} {pkt : packet A lvl len C1} 
           {cs : csteque A nlvl C2} {eq : nlvl = len + lvl} {cc : csteque_color C1 C2 C3},
      Ppacket pkt ->
      Pcsteque cs ->
      Pcsteque (Big pkt cs eq cc).
  (* Arguments P_Big {lvl len nlvl C1 C2 C3 pkt cs eq cc}. *)

  (* Fixpoint list_forallt {A : Type} {P : A -> Type} (f : forall (a : A), P a) (l : list A) : Forallt P l :=
    match l with 
    | [] => Forallt_nil P
    | x :: l => Forallt_cons P (f x) (list_forallt f l)
    end. *)

  Fixpoint element_rect {lvl : nat} (e : element A lvl) {struct e} : Pelement e :=
    match e with 
    | ZElt a => P_ZElt a
    | SElt p cs => 
      P_SElt (list_forallt (prefix'_seq p)) (csteque_rect cs)
    end

  with packet_rect {lvl len : nat} {C : color} (pkt : packet A lvl len C) {struct pkt} : Ppacket pkt :=
    match pkt with 
    | Hole => P_Hole
    | Triple p pkt s => 
      P_Triple (list_forallt (prefix'_seq p))
               (packet_rect pkt) 
               (list_forallt (suffix'_seq s))
    end

  with csteque_rect {lvl : nat} {C : color} (cs : csteque A lvl C) {struct cs} : Pcsteque cs :=
    match cs with 
    | Small s => P_Small (list_forallt (suffix'_seq s))
    | Big pkt cs eq cc => P_Big (packet_rect pkt) (csteque_rect cs)
    end
    
  with list_forallt {lvl : nat} (l : list (element A lvl)) {struct l} : Forallt Pelement l :=
    match l with 
    | [] => Forallt_nil Pelement
    | e :: l => Forallt_cons Pelement (element_rect e) (list_forallt l)
    end.