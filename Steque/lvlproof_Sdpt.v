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
      
Inductive element (A : Type) : nat -> nat -> Type := 
  | ZElt {dpt : nat} : A -> element A 0 dpt
  | SElt {lvl dpt : nat} {C1 C2 : color} : 
      prefix' (element A lvl dpt) C1 -> 
      lvl_csteque A (S lvl) dpt C2 -> 
      element A (S lvl) (S dpt)
 
   (* Packets represents the same concept as before : either a Hole, the end of 
   the packet, or a triple prefix - next packet - suffix, with the next packet
   being of one level higher, and yellow or uncolored. *)

with lvl_packet (A : Type) : nat -> nat -> nat -> color -> Type := 
  | Hole {lvl dpt : nat} : lvl_packet A lvl 0 dpt uncolored 
  | Triple {lvl len dpt : nat} {Y : yellow_hue} {C : color} : 
      prefix' (element A lvl dpt) C -> 
      lvl_packet A (S lvl) len dpt (Mix NoGreen Y NoRed) ->
      suffix' (element A lvl dpt) ->
      lvl_packet A lvl (S len) (S dpt) C

   (* Colored steques also look similar to colored deque in our previous structure,
   it is either Small, only made of a suffix, or big, made of one packet and a 
   following colored steque. *)

with lvl_csteque (A : Type) : nat -> nat -> color -> Type := 
  | Small {lvl dpt : nat} : 
      suffix' (element A lvl dpt) -> 
      lvl_csteque A lvl (S dpt) green 
  | Big {lvl len dpt nlvl : nat} {C1 C2 C3 : color} :
      lvl_packet A lvl len dpt C1 ->
      lvl_csteque A nlvl dpt C2 ->
      nlvl = len + lvl ->
      csteque_color C1 C2 C3 ->
      lvl_csteque A lvl (S dpt) C3.
    
Arguments ZElt {A dpt}.
Arguments SElt {A lvl dpt C1 C2}.
Arguments Hole {A lvl dpt}.
Arguments Triple {A lvl len dpt Y C}.
Arguments Small {A lvl dpt}.
Arguments Big {A lvl len dpt nlvl C1 C2 C3}.

Definition suffix A lvl dpt := suffix' (element A lvl dpt).
Definition prefix A lvl dpt := prefix' (element A lvl dpt).

(* A type for colored steque. *)

Definition csteque (A : Type) := lvl_csteque A 0.

(* A type for steque. *)

Inductive steque (A : Type) : Type := 
  T : forall (dpt : nat) (G : green_hue) (Y : yellow_hue), 
      csteque A dpt (Mix G Y NoRed) -> 
      steque A.
Arguments T {A dpt G Y}.

(* Models *)

Set Equations Transparent.

Opaque app.
Definition singleton {A : Type} (x : A) : list A := [x].
Opaque singleton.

Equations suffix'_seq {A} : suffix' A -> list A := 
suffix'_seq (Suff d) := deque_seq d.

Equations prefix'_seq {A C} : prefix' A C -> list A := 
prefix'_seq (Pre2 a b) := [a] ++ [b];
prefix'_seq (Pre3 a b c) := [a] ++ [b] ++ [c];
prefix'_seq (Pre4 a b c d e) := [a] ++ [b] ++ [c] ++ [d] ++ deque_seq e.

Equations map_concat {A B : Type} (f : A -> list B) (l : list A) : list B := 
map_concat f [] := [];
map_concat f (a :: l) := f a ++ map_concat f l.

(* Equations element_seq {A lvl} (dpt : nat) : element A lvl dpt -> list A :=
element_seq _ (ZElt a) := [a];
element_seq _ (SElt dpt p cs) :=
    map_concat (element_seq dpt) (prefix_seq p) ++
    csteque_seq dpt cs 

with packet_front_seq {A lvl len C} (dpt : nat) : lvl_packet A lvl len dpt C -> list A :=
packet_front_seq _ Hole := [];
packet_front_seq _ (Triple dpt p pkt _) :=
    map_concat (element_seq dpt) (prefix_seq p) ++
    packet_front_seq dpt pkt;
  
with packet_rear_seq {A lvl len C} (dpt : nat) : lvl_packet A lvl len dpt C -> list A :=
packet_rear_seq _ Hole := [];
packet_rear_seq _ (Triple dpt _ pkt s) :=
    packet_rear_seq dpt pkt ++
    map_concat (element_seq dpt) (suffix_seq s)
    
with csteque_seq {A lvl C} (dpt : nat) : lvl_csteque A lvl dpt C -> list A :=
csteque_seq (S dpt) (Small s) :=
    map_concat (element_seq dpt) (suffix_seq s);
csteque_seq _ (Big dpt pkt cs eq_refl _) :=
    packet_front_seq dpt pkt ++
    csteque_seq dpt cs ++
    packet_rear_seq dpt pkt. *)

Inductive seq_kind : Type := Element | FPacket | RPacket | CSteque.

Definition seq_struct (k : seq_kind) A lvl len dpt C :=
    match k with 
    | Element => element A lvl dpt 
    | FPacket | RPacket => lvl_packet A lvl len dpt C 
    | CSteque => lvl_csteque A lvl dpt C
    end.

#[local] Obligation Tactic := try first [assumption | exact uncolored | lia].

Equations structure_seq (k : seq_kind) {A lvl len dpt C}
    (s : seq_struct k A lvl len dpt C) : list A by wf dpt := 
structure_seq Element (ZElt a) := [a];
structure_seq Element (SElt p cs) := 
    map_concat (fun elt => structure_seq Element elt) (prefix'_seq p) ++
    structure_seq CSteque cs;
structure_seq FPacket Hole := [];
structure_seq FPacket (Triple p pkt _) := 
    map_concat (fun elt => structure_seq Element elt) (prefix'_seq p) ++   
    structure_seq FPacket pkt;
structure_seq RPacket Hole := [];
structure_seq RPacket (Triple _ pkt s) :=
    structure_seq RPacket pkt ++
    map_concat (fun elt => structure_seq Element elt) (suffix'_seq s);
structure_seq CSteque (Small s) := 
    map_concat (fun elt => structure_seq Element elt) (suffix'_seq s);
structure_seq CSteque (Big pkt cs eq_refl _) := 
    structure_seq FPacket pkt ++
    structure_seq CSteque cs ++
    structure_seq RPacket pkt.

Definition element_seq {A lvl dpt} := 
    structure_seq Element (A := A) (C := uncolored) (lvl := lvl) (len := 0) (dpt := dpt).
Definition csteque_seq {A C lvl dpt} := 
    structure_seq CSteque (A := A) (C := C) (lvl := lvl) (len := 0) (dpt := dpt).

Definition suffix_seq {A lvl dpt} (s : suffix A lvl dpt) := 
    map_concat element_seq (suffix'_seq s).
Definition prefix_seq {A lvl dpt C} (p : prefix A lvl dpt C) :=
    map_concat element_seq (prefix'_seq p).

Equations steque_seq {A} : steque A -> list A :=
steque_seq (T cs) := csteque_seq cs.

Unset Equations Transparent.

(* Elements *)

Notation "? x" := (@exist _ _ x _) (at level 100).

(* The empty colored steque. *)

Equations cempty {A lvl dpt} : { cs : lvl_csteque A lvl (S dpt) green | csteque_seq cs = [] } :=
cempty with dempty => { | ? d := ? Small (Suff d) }.
Next Obligation.
  intros * e. cbn beta in *.
  cbn. rewrite e. reflexivity.
Qed.

(* Functions *)  

Equations make_green {A lvl dpt C}
    (p : prefix A lvl dpt green)
    (cs : lvl_csteque A (S lvl) (S dpt) C)
    (s : suffix A lvl dpt) :
    { cs' : lvl_csteque A lvl (S (S dpt)) green | csteque_seq cs' = prefix_seq p ++
                                                                csteque_seq cs ++
                                                                suffix_seq s } :=
make_green p (Small s') s := ? Big (Triple p Hole s) (Small s') _ _;
make_green p (Big pkt cs eq_refl CCGreen) s :=
    ? Big (Triple p Hole s) (Big pkt cs _ CCGreen) _ CCGreen;
make_green p (Big pkt cs eq_refl CCYellow) s :=
    ? Big (Triple p pkt s) cs _ CCGreen;
make_green p (Big pkt cs eq_refl CCOrange) s :=
    ? Big (Triple p pkt s) cs _ CCGreen;
make_green p (Big pkt cs eq_refl CCRed) s :=
    ? Big (Triple p Hole s) (Big pkt cs _ CCRed) _ CCGreen.

(* let green
: type a c.
  (a, [`green]) prefix -> (a pair, c) csteque -> a suffix -> (a, [`green]) csteque
= fun p csteque s ->
  match csteque with
  | Suffix small -> G (Triple (p, HOLE, s), Suffix small)
  | Y (triple, k) -> G (Triple (p, triple, s), k)
  | Yr (triple, k) -> G (Triple (p, triple, s), k)
  | G (triple, k) -> G (Triple (p, HOLE, s), G (triple, k))
  | R (triple, k) -> G (Triple (p, HOLE, s), R (triple, k)) *)