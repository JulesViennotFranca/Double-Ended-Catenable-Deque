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



Equations element_seq {A lvl} (elt : element A lvl) : list A by struct elt := {
element_seq (ZElt a) := [a];
element_seq (lvl := _) (SElt p cs) := prefix_seq p ++ csteque_seq cs }

where prodN_seq {A lvle lvlp} (p : prodN (element A lvle) lvlp) : list A by struct p := { 
prodN_seq (prodZ a) := element_seq a;
prodN_seq (prodS (p1, p2)) := prodN_seq p1 ++ prodN_seq p2 }

where buffer_seq {A lvle lvlp C} (b : buffer (element A lvle) lvlp C) : list A by struct b := {
buffer_seq B0 := ([] : list A);
buffer_seq (B1 a) := prodN_seq a;
buffer_seq (B2 a b) := prodN_seq a ++ prodN_seq b;
buffer_seq (B3 a b c) := prodN_seq a ++ prodN_seq b ++ prodN_seq c;
buffer_seq (B4 a b c d) := prodN_seq a ++ prodN_seq b ++ prodN_seq c ++ prodN_seq d;
buffer_seq (B5 a b c d e) := prodN_seq a ++ prodN_seq b ++ prodN_seq c ++ prodN_seq d ++ prodN_seq e }

where dpacket_front_seq {A lvle lvlp len C} (pkt : lvlproof.lvl_packet (element A lvle) lvlp len C) : list A by struct pkt := {
dpacket_front_seq lvlproof.Hole := ([] : list A);
dpacket_front_seq (lvlproof.Triple p pkt _ _) := 
  buffer_seq p ++ dpacket_front_seq pkt }

where dpacket_rear_seq {A lvle lvlp len C} (pkt : lvlproof.lvl_packet (element A lvle) lvlp len C) : list A by struct pkt := {
dpacket_rear_seq lvlproof.Hole := [];
dpacket_rear_seq (lvlproof.Triple _ pkt s _) := 
  dpacket_rear_seq pkt ++ buffer_seq s }

where cdeque_seq {A lvle lvlp C} (cd : lvl_cdeque (element A lvle) lvlp C) : list A by struct cd := {
cdeque_seq (lvlproof.Small b) := buffer_seq b;
cdeque_seq (lvlproof.Big pkt cd _ _) := 
    dpacket_front_seq pkt ++
    cdeque_seq cd ++
    dpacket_rear_seq pkt }

where prefix_seq {A lvl C} (p : prefix A lvl C) : list A by struct p := {
prefix_seq (Pre2 a b) := element_seq a ++ element_seq b;
prefix_seq (Pre3 a b c) := element_seq a ++ element_seq b ++ element_seq c;
prefix_seq (Pre4 a b c d (lvlproof.T e)) := element_seq a ++ element_seq b ++ element_seq c ++ element_seq d ++ cdeque_seq e }

where suffix_seq {A lvl} (s : suffix A lvl) : list A by struct s := { 
suffix_seq (Suff (lvlproof.T d)) := cdeque_seq d }

where packet_front_seq {A lvl len C} (pkt : lvl_packet A lvl len C) : list A by struct pkt := { 
packet_front_seq Hole := [];
packet_front_seq (Triple p pkt _) := 
    prefix_seq p ++ packet_front_seq pkt }

where packet_rear_seq {A lvl len C} (pkt : lvl_packet A lvl len C) : list A by struct pkt := {
packet_rear_seq Hole := [];
packet_rear_seq (Triple _ pkt s) :=
    packet_rear_seq pkt ++ suffix_seq s }

where csteque_seq {A lvl C} (cs : lvl_csteque A lvl C) : list A by struct cs := {
csteque_seq (Small s) := suffix_seq s;
csteque_seq (Big pkt cs eq_refl _) := 
    packet_front_seq pkt ++
    csteque_seq cs ++
    packet_rear_seq pkt }.











(* Fixpoint prodN_depth {A lvlp} (f : A -> nat) (p : prodN A lvlp) {struct p} : nat :=
    match p with 
    | prodS (p1, p2) => prodN_depth f p1 + prodN_depth f p2 
    | prodZ a => f a 
    end.

Definition buffer_depth {A lvlp C} (f : A -> nat) (b : buffer A lvlp C) : nat :=
    match b with 
    | B0 => 0
    | (B1 a) => prodN_depth f a
    | (B2 a b) => prodN_depth f a + prodN_depth f b
    | (B3 a b c) => prodN_depth f a + prodN_depth f b + prodN_depth f c
    | (B4 a b c d) => prodN_depth f a + prodN_depth f b + prodN_depth f c + prodN_depth f d
    | (B5 a b c d e) => prodN_depth f a + prodN_depth f b + prodN_depth f c + prodN_depth f d + prodN_depth f e
    end.

Fixpoint dpacket_front_depth {A lvlp len C} (f : A -> nat) (pkt : lvlproof.lvl_packet A lvlp len C) {struct pkt} : nat :=
    match pkt with 
    | lvlproof.Hole => 0
    | (lvlproof.Triple p pkt _ _) => buffer_depth f p + dpacket_front_depth f pkt
    end.

Fixpoint dpacket_rear_depth {A lvlp len C} (f : A -> nat) (pkt : lvlproof.lvl_packet A lvlp len C) {struct pkt} : nat :=
    match pkt with 
    | lvlproof.Hole => 0
    | (lvlproof.Triple _ pkt s _) => dpacket_rear_depth f pkt + buffer_depth f s
    end.

Fixpoint cdeque_depth {A lvlp C} (f : A -> nat) (cd : lvl_cdeque A lvlp C) {struct cd} : nat :=
    match cd with 
    | (lvlproof.Small b) => buffer_depth f b
    | (lvlproof.Big pkt cd _ _) => 
        dpacket_front_depth f pkt +
        cdeque_depth f cd +
        dpacket_rear_depth f pkt
    end.

Definition deque_depth {A} (f : A -> nat) (d : deque A) : nat :=
    match d with lvlproof.T dq => cdeque_depth f dq end.

Fixpoint suffix_depth {A lvl} (f : A -> nat) (s : suffix A lvl) {struct s} : nat := 
    match s with Suff d => deque_depth (fun elt => element_depth f elt) d end

with prefix_depth {A lvl C} (f : A -> nat) (p : prefix A lvl C) {struct p} : nat := 
    match p with 
    | (Pre2 a b) => element_depth f a + element_depth f b
    | (Pre3 a b c) => element_depth f a + element_depth f b + element_depth f c
    | (Pre4 a b c d e) => element_depth f a + element_depth f b + element_depth f c + element_depth f d + deque_depth (fun elt => element_depth f elt) e
    end

with element_depth {A lvl} (f : A -> nat) (elt : element A lvl) {struct elt} : nat := 
    match elt with
    | (ZElt a) => f a
    | (SElt p cs) => prefix_depth f p + csteque_depth f cs
    end

with packet_front_depth {A lvl len C} (f : A -> nat) (pkt : lvl_packet A lvl len C) {struct pkt} : nat := 
    match pkt with
    | Hole => 0
    | (Triple p pkt _) => prefix_depth f p + packet_front_depth f pkt
    end

with packet_rear_depth {A lvl len C} (f : A -> nat) (pkt : lvl_packet A lvl len C) {struct pkt} : nat :=
    match pkt with
    | Hole => 0
    | (Triple _ pkt s) => packet_rear_depth f pkt + suffix_depth f s 
    end

with csteque_depth {A lvl C} (f : A -> nat) (cs : lvl_csteque A lvl C) {struct cs} : nat :=
    match cs with
    | (Small s) => suffix_depth f s
    | (Big pkt cs _ _) => 
        packet_front_depth f pkt +
        csteque_depth f cs +
        packet_rear_depth f pkt
    end. *)



Equations buffer_concat_map {A B : Type} {lvle lvlp C} (f : forall lvle lvlp, prodN (element A lvle) lvlp -> list B) 
    (b : buffer (element A lvle) lvlp C) : list B by struct b := 
buffer_concat_map f B0 := [];
buffer_concat_map f (B1 a) := f _ _ a;
buffer_concat_map f (B2 a b) := f _ _ a ++ f _ _ b;
buffer_concat_map f (B3 a b c) := f _ _ a ++ f _ _ b ++ f _ _ c;
buffer_concat_map f (B4 a b c d) := f _ _ a ++ f _ _ b ++ f _ _ c ++ f _ _ d;
buffer_concat_map f (B5 a b c d e) := f _ _ a ++ f _ _ b ++ f _ _ c ++ f _ _ d ++ f _ _ e.

Equations dpacket_front_concat_map {A B : Type} {lvle lvlp} len {C} (f : forall lvle lvlp, prodN (element A lvle) lvlp -> list B) 
    (pkt : lvlproof.lvl_packet (element A lvle) lvlp len C) : list B by struct len :=
dpacket_front_concat_map 0 f lvlproof.Hole := [];
dpacket_front_concat_map (S len) f (lvlproof.Triple p pkt _ _) := 
    buffer_concat_map f p ++ dpacket_front_concat_map len f pkt.
Arguments dpacket_front_concat_map {A B lvle lvlp len C}.

Equations dpacket_rear_concat_map {A B : Type} {lvle lvlp} len {C} (f : forall lvle lvlp, prodN (element A lvle) lvlp -> list B) 
    (pkt : lvlproof.lvl_packet (element A lvle) lvlp len C) : list B by struct len :=
dpacket_rear_concat_map 0 f lvlproof.Hole := [];
dpacket_rear_concat_map (S len) f (lvlproof.Triple _ pkt s _) :=
    dpacket_rear_concat_map len f pkt ++ buffer_concat_map f s.
Arguments dpacket_rear_concat_map {A B lvle lvlp len C}.

Equations cdeque_concat_map {A B : Type} {lvle lvlp C} (f : forall lvle lvlp, prodN (element A lvle) lvlp -> list B) 
    (cd : lvlproof.lvl_cdeque (element A lvle) lvlp C) : list B by struct cd :=
cdeque_concat_map f (lvlproof.Small b) := buffer_concat_map f b;
cdeque_concat_map f (lvlproof.Big pkt cd eq_refl _) :=
    dpacket_front_concat_map f pkt ++
    cdeque_concat_map f cd ++
    dpacket_rear_concat_map f pkt.

Equations suffix_concat_map {A B : Type} {lvl} (f : forall lvle lvlp, prodN (element A lvle) lvlp -> list B) 
    (s : suffix A lvl) : list B by struct s :=
suffix_concat_map f (Suff (lvlproof.T d)) := cdeque_concat_map f d.

Equations packet_rear_concat_map {A B : Type} {lvl} len {C} (f : forall lvle lvlp, prodN (element A lvle) lvlp -> list B) 
    (pkt : lvl_packet A lvl len C) : list B :=
packet_rear_concat_map 0 f Hole := [];
packet_rear_concat_map (S len) f (Triple _ pkt s) :=
    packet_rear_concat_map len f pkt ++ suffix_concat_map f s.
Arguments packet_rear_concat_map {A B lvl len C}.

Equations element_seq {A lvl} (elt : element A lvl) : list A by struct elt := {
element_seq (ZElt a) := [a];
element_seq (SElt pref cs) := prefix_seq pref ++ csteque_seq cs }

where prodN_seq {A} lvle lvlp (p : prodN (element A lvle) lvlp) : list A by struct lvlp := {
prodN_seq lvle 0 (prodZ a) := element_seq a;
prodN_seq lvle (S lvlp) (prodS (p1, p2)) := prodN_seq lvle lvlp p1 ++ prodN_seq lvle lvlp p2 }

where prefix_seq {A lvl C} (p : prefix A lvl C) : list A by struct p := {
prefix_seq (Pre2 a b) := element_seq a ++ element_seq b;
prefix_seq (Pre3 a b c) := element_seq a ++ element_seq b ++ element_seq c;
prefix_seq (Pre4 a b c d (lvlproof.T e)) := 
    element_seq a ++ element_seq b ++ element_seq c ++ element_seq d ++ cdeque_concat_map prodN_seq e }

where packet_front_seq {A lvl len C} (pkt : lvl_packet A lvl len C) : list A by struct len := {
packet_front_seq Hole := [];
packet_front_seq (Triple p pkt _) := 
    prefix_seq p ++ packet_front_seq pkt }

where csteque_seq {A lvl C} (cs : lvl_csteque A lvl C) : list A by struct cs := {
csteque_seq (Small suff) := suffix_concat_map prodN_seq suff;
csteque_seq (Big pkt cs eq_refl _) := 
    packet_front_seq pkt ++
    csteque_seq cs ++
    packet_rear_concat_map prodN_seq pkt }.










Equations packet_front_concat_map {A B : Type} {lvl len C} (f : forall lvl C, prefix A lvl C -> list B) 
    (pkt : lvl_packet A lvl len C) : list B by struct pkt :=
packet_front_concat_map f Hole := [];
packet_front_concat_map f (Triple p pkt _) := 
    f _ _ p ++ packet_front_concat_map f pkt.

Equations packet_rear_concat_map {A B : Type} {lvl len C} (f : forall lvle lvlp, prodN (element A lvle) lvlp -> list B) 
    (pkt : lvl_packet A lvl len C) : list B by struct pkt :=
packet_rear_concat_map f Hole := [];
packet_rear_concat_map f (Triple _ pkt s) :=
    packet_rear_concat_map f pkt ++ suffix_concat_map f s.

Equations element_seq {A : Type} (lvl : nat) (elt : element A lvl) : list A by struct elt := {
element_seq 0 (ZElt a) := [a];
element_seq (S lvl) (SElt pref cs) := prefix_seq lvl _ pref ++ csteque_seq cs }

where prodN_seq {A} lvle lvlp (p : prodN (element A lvle) lvlp) : list A by struct p := {
prodN_seq lvle 0 (prodZ a) := element_seq lvle a;
prodN_seq lvle (S lvlp) (prodS (p1, p2)) := prodN_seq lvle lvlp p1 ++ prodN_seq lvle lvlp p2 }

where prefix_seq {A} lvl C (p : prefix A lvl C) : list A by struct p := {
prefix_seq lvl red (Pre2 a b) := element_seq lvl a ++ element_seq lvl b;
prefix_seq lvl yellow (Pre3 a b c) := element_seq lvl a ++ element_seq lvl b ++ element_seq lvl c;
prefix_seq lvl green (Pre4 a b c d (lvlproof.T e)) := 
    element_seq lvl a ++ element_seq lvl b ++ element_seq lvl c ++ element_seq lvl d ++ cdeque_concat_map prodN_seq e }

where csteque_seq {A lvl C} (cs : lvl_csteque A lvl C) : list A by struct cs := {
csteque_seq (Small suff) := suffix_concat_map prodN_seq suff;
csteque_seq (Big pkt cs eq_refl _) := 
    packet_front_concat_map prefix_seq pkt ++
    csteque_seq cs ++
    packet_rear_concat_map prodN_seq pkt }.






Equations element_seq {A lvl} (elt : element A lvl) : list A by struct elt := 
element_seq (ZElt a) := [a];
element_seq (SElt p cs) := prefix_seq p ++ csteque_seq cs

with prefix_seq {A lvl C} (p : prefix A lvl C) : list A by struct p := 
prefix_seq (Pre2 a b) := element_seq a ++ element_seq b;
prefix_seq (Pre3 a b c) := element_seq a ++ element_seq b ++ element_seq c;
prefix_seq (Pre4 a b c d (lvlproof.T e)) := element_seq a ++ element_seq b ++ element_seq c ++ element_seq d ++ cdeque_seq e

with cdeque_seq {A lvle lvlp C} (cd : lvl_cdeque (element A lvle) lvlp C) : list A by struct cd :=
cdeque_seq (lvlproof.Small b) := buffer_seq b;
cdeque_seq (lvlproof.Big pkt cd _ _) := 
    dpacket_front_seq pkt ++
    cdeque_seq cd ++
    dpacket_rear_seq pkt

with dpacket_front_seq {A lvle lvlp len C} (pkt : lvlproof.lvl_packet (element A lvle) lvlp len C) : list A by struct pkt :=
dpacket_front_seq lvlproof.Hole := [];
dpacket_front_seq (lvlproof.Triple p pkt _ _) := 
  buffer_seq p ++ dpacket_front_seq pkt

with dpacket_rear_seq {A lvle lvlp len C} (pkt : lvlproof.lvl_packet (element A lvle) lvlp len C) : list A by struct pkt :=
dpacket_rear_seq lvlproof.Hole := [];
dpacket_rear_seq (lvlproof.Triple _ pkt s _) := 
  dpacket_rear_seq pkt ++ buffer_seq s

with buffer_seq {A lvle lvlp C} (b : buffer (element A lvle) lvlp C) : list A by struct b :=
buffer_seq B0 := [];
buffer_seq (B1 a) := prodN_seq a;
buffer_seq (B2 a b) := prodN_seq a ++ prodN_seq b;
buffer_seq (B3 a b c) := prodN_seq a ++ prodN_seq b ++ prodN_seq c;
buffer_seq (B4 a b c d) := prodN_seq a ++ prodN_seq b ++ prodN_seq c ++ prodN_seq d;
buffer_seq (B5 a b c d e) := prodN_seq a ++ prodN_seq b ++ prodN_seq c ++ prodN_seq d ++ prodN_seq e

with prodN_seq {A lvle lvlp} (p : prodN (element A lvle) lvlp) : list A by struct p := 
prodN_seq (prodZ a) := element_seq a;
prodN_seq (prodS (p1, p2)) := prodN_seq p1 ++ prodN_seq p2

with csteque_seq {A lvl C} (cs : lvl_csteque A lvl C) : list A by struct cs :=
csteque_seq (Small s) := suffix_seq s;
csteque_seq (Big pkt cs eq_refl _) := 
    packet_front_seq pkt ++
    csteque_seq cs ++
    packet_rear_seq pkt

with suffix_seq {A lvl} (s : suffix A lvl) : list A by struct s := 
suffix_seq (Suff (lvlproof.T d)) := cdeque_seq d

with packet_front_seq {A lvl len C} (pkt : lvl_packet A lvl len C) : list A by struct pkt := 
packet_front_seq Hole := [];
packet_front_seq (Triple p pkt _) := 
    prefix_seq p ++ packet_front_seq pkt

with packet_rear_seq {A lvl len C} (pkt : lvl_packet A lvl len C) : list A by struct pkt :=
packet_rear_seq Hole := [];
packet_rear_seq (Triple _ pkt s) :=
    packet_rear_seq pkt ++ suffix_seq s.










(* Equations element_seq {A lvl} (elt : element A lvl) : list A by struct elt :=
element_seq (ZElt a) := [a];
element_seq (SElt p cs) := 
        let fix prodN_seq {A lvle lvlp} (p : prodN (element A lvle) lvlp) {struct p} : list A :=
            match p with 
            | prodZ a => element_seq a 
            | prodS (p1, p2) => prodN_seq p1 ++ prodN_seq p2 
            end in 
        let buffer_seq {A lvle lvlp C} (b : buffer (element A lvle) lvlp C) {struct b} : list A :=
            match b with 
            | B0 => []
            | (B1 a) => prodN_seq a
            | (B2 a b) => prodN_seq a ++ prodN_seq b
            | (B3 a b c) => prodN_seq a ++ prodN_seq b ++ prodN_seq c
            | (B4 a b c d) => prodN_seq a ++ prodN_seq b ++ prodN_seq c ++ prodN_seq d
            | (B5 a b c d e) => prodN_seq a ++ prodN_seq b ++ prodN_seq c ++ prodN_seq d ++ prodN_seq e
            end in
        let fix dpacket_front_seq {A lvle lvlp len C} (pkt : lvlproof.lvl_packet (element A lvle) lvlp len C) {struct pkt} : list A :=
            match pkt with 
            | lvlproof.Hole => []
            | (lvlproof.Triple p pkt _ _) => buffer_seq p ++ dpacket_front_seq pkt
            end in 
        let fix dpacket_rear_seq {A lvle lvlp len C} (pkt : lvlproof.lvl_packet (element A lvle) lvlp len C) {struct pkt} : list A :=
            match pkt with 
            | lvlproof.Hole => []
            | (lvlproof.Triple _ pkt s _) => dpacket_rear_seq pkt ++ buffer_seq s
            end in 
        let fix cdeque_seq {A lvle lvlp C} (cd : lvl_cdeque (element A lvle) lvlp C) {struct cd} : list A :=
            match cd with 
            | (lvlproof.Small b) => buffer_seq b
            | (lvlproof.Big pkt cd _ _) => 
                dpacket_front_seq pkt ++
                cdeque_seq cd ++
                dpacket_rear_seq pkt
            end in 
        let deque_seq {A lvle} (d : deque (element A lvle)) {struct d} : list A :=
            match d with lvlproof.T dq => cdeque_seq dq end 
        in
        let suffix_seq {A lvl} (s : suffix A lvl) {struct s} : list A := 
            match s with Suff d => deque_seq d end
        in
        let prefix_seq {A lvl C} (p : prefix A lvl C) {struct p} : list A := 
            match p with 
            | (Pre2 a b) => element_seq a ++ element_seq b
            | (Pre3 a b c) => element_seq a ++ element_seq b ++ element_seq c
            | (Pre4 a b c d e) => element_seq a ++ element_seq b ++ element_seq c ++ element_seq d ++ deque_seq e
            end in 
        let fix packet_front_seq {A lvl len C} (pkt : lvl_packet A lvl len C) {struct pkt} : list A := 
            match pkt with
            | Hole => []
            | (Triple p pkt _) => prefix_seq p ++ packet_front_seq pkt
            end in 
        let fix packet_rear_seq {A lvl len C} (pkt : lvl_packet A lvl len C) {struct pkt} : list A :=
            match pkt with
            | Hole => []
            | (Triple _ pkt s) => packet_rear_seq pkt ++ suffix_seq s 
            end in 
        let fix csteque_seq {A lvl C} (cs : lvl_csteque A lvl C) {struct cs} : list A :=
            match cs with
            | (Small s) => suffix_seq s
            | (Big pkt cs _ _) => 
                packet_front_seq pkt ++
                csteque_seq cs ++
                packet_rear_seq pkt
            end in
        prefix_seq p ++ csteque_seq cs. *)

Program Fixpoint element_seq {A} lvl (elt : element A lvl) {struct elt} : list A := 
    match elt with
    | (ZElt a) => [a]
    | (SElt p cs) => 
        let fix prodN_seq {A} lvle lvlp (p : prodN (element A lvle) lvlp) {struct p} : list A :=
            match p with 
            | prodZ a => element_seq lvle a 
            | prodS (p1, p2) => prodN_seq lvle _ p1 ++ prodN_seq lvle _ p2 
            end in 
        let buffer_seq {A} lvle lvlp C (b : buffer (element A lvle) lvlp C) {struct b} : list A :=
            match b with 
            | B0 => []
            | (B1 a) => prodN_seq lvle lvlp a
            | (B2 a b) => prodN_seq lvle lvlp a ++ prodN_seq lvle lvlp b
            | (B3 a b c) => prodN_seq lvle lvlp a ++ prodN_seq lvle lvlp b ++ prodN_seq lvle lvlp c
            | (B4 a b c d) => prodN_seq lvle lvlp a ++ prodN_seq lvle lvlp b ++ prodN_seq lvle lvlp c ++ prodN_seq lvle lvlp d
            | (B5 a b c d e) => prodN_seq lvle lvlp a ++ prodN_seq lvle lvlp b ++ prodN_seq lvle lvlp c ++ prodN_seq lvle lvlp d ++ prodN_seq lvle lvlp e
            end in
        let fix dpacket_front_seq {A} lvle lvlp len C (pkt : lvlproof.lvl_packet (element A lvle) lvlp len C) {struct pkt} : list A :=
            match pkt with 
            | lvlproof.Hole => []
            | (lvlproof.Triple p pkt _ _) => buffer_seq lvle lvlp _ p ++ dpacket_front_seq lvle (S lvlp) _ _ pkt
            end in 
        let fix dpacket_rear_seq {A} lvle lvlp len C (pkt : lvlproof.lvl_packet (element A lvle) lvlp len C) {struct pkt} : list A :=
            match pkt with 
            | lvlproof.Hole => []
            | (lvlproof.Triple _ pkt s _) => dpacket_rear_seq lvle (S lvlp) _ _ pkt ++ buffer_seq lvle lvlp _ s
            end in 
        let fix cdeque_seq {A} lvle lvlp C (cd : lvl_cdeque (element A lvle) lvlp C) {struct cd} : list A :=
            match cd with 
            | (lvlproof.Small b) => buffer_seq lvle lvlp _ b
            | (lvlproof.Big pkt cd _ _) => 
                dpacket_front_seq lvle lvlp _ _ pkt ++
                cdeque_seq lvle _ _ cd ++
                dpacket_rear_seq lvle lvlp _ _ pkt
            end in 
        let deque_seq {A} lvle (d : deque (element A lvle)) {struct d} : list A :=
            match d with lvlproof.T dq => cdeque_seq lvle 0 _ dq end 
        in
        let suffix_seq {A} lvl (s : suffix A lvl) {struct s} : list A := 
            match s with Suff d => deque_seq lvl d end
        in
        let prefix_seq {A} lvl C (p : prefix A lvl C) {struct p} : list A := 
            match p with 
            | (Pre2 a b) => element_seq lvl a ++ element_seq lvl b
            | (Pre3 a b c) => element_seq lvl a ++ element_seq lvl b ++ element_seq lvl c
            | (Pre4 a b c d e) => element_seq lvl a ++ element_seq lvl b ++ element_seq lvl c ++ element_seq lvl d ++ deque_seq lvl e
            end in 
        let fix packet_front_seq {A} lvl len C (pkt : lvl_packet A lvl len C) {struct pkt} : list A := 
            match pkt with
            | Hole => []
            | (Triple p pkt _) => prefix_seq lvl _ p ++ packet_front_seq (S lvl) _ _ pkt
            end in 
        let fix packet_rear_seq {A} lvl len C (pkt : lvl_packet A lvl len C) {struct pkt} : list A :=
            match pkt with
            | Hole => []
            | (Triple _ pkt s) => packet_rear_seq pkt ++ suffix_seq s 
            end in 
        let fix csteque_seq {A} lvl C (cs : lvl_csteque A lvl C) {struct cs} : list A :=
            match cs with
            | (Small s) => suffix_seq s
            | (Big pkt cs _ _) => 
                packet_front_seq pkt ++
                csteque_seq cs ++
                packet_rear_seq pkt
            end in
        prefix_seq p ++ csteque_seq cs
    end.

(* Fixpoint element_concat_map {A B lvl} (f : A -> list B) (elt : element A lvl) {struct elt} : list B := 
    match elt with
    | (ZElt a) => f a
    | (SElt p cs) => prefix_concat_map f p ++ csteque_concat_map f cs
    end

with prodN_concat_map {A B lvle lvlp} (f : A -> list B) (pro : prodN (element A lvle) lvlp) {struct pro} : list B :=
    match pro with 
    | prodZ a => element_concat_map f a 
    | prodS (p1, p2) => prodN_concat_map f p1 ++ prodN_concat_map f p2 
    end

with buffer_concat_map {A B lvle lvlp C} (f : A -> list B) (b : buffer (element A lvle) lvlp C) {struct b} : list B :=
    match b with 
    | B0 => []
    | (B1 a) => prodN_concat_map f a
    | (B2 a b) => prodN_concat_map f a ++ prodN_concat_map f b
    | (B3 a b c) => prodN_concat_map f a ++ prodN_concat_map f b ++ prodN_concat_map f c
    | (B4 a b c d) => prodN_concat_map f a ++ prodN_concat_map f b ++ prodN_concat_map f c ++ prodN_concat_map f d
    | (B5 a b c d e) => prodN_concat_map f a ++ prodN_concat_map f b ++ prodN_concat_map f c ++ prodN_concat_map f d ++ prodN_concat_map f e
    end 

with dpacket_front_concat_map {A B lvle lvlp len C} (f : A -> list B) (pkt : lvlproof.lvl_packet (element A lvle) lvlp len C) {struct pkt} : list B :=
    match pkt with 
    | lvlproof.Hole => []
    | (lvlproof.Triple p pkt _ _) => buffer_concat_map f p ++ dpacket_front_concat_map f pkt
    end

with dpacket_rear_concat_map {A B lvle lvlp len C} (f : A -> list B) (pkt : lvlproof.lvl_packet (element A lvle) lvlp len C) {struct pkt} : list B :=
    match pkt with 
    | lvlproof.Hole => []
    | (lvlproof.Triple _ pkt s _) => dpacket_rear_concat_map f pkt ++ buffer_concat_map f s
    end

with cdeque_concat_map {A B lvle lvlp C} (f : A -> list B) (cd : lvl_cdeque (element A lvle) lvlp C) {struct cd} : list B :=
    match cd with 
    | (lvlproof.Small b) => buffer_concat_map f b
    | (lvlproof.Big pkt cd _ _) => 
        dpacket_front_concat_map f pkt ++
        cdeque_concat_map f cd ++
        dpacket_rear_concat_map f pkt
    end

with deque_concat_map {A B lvle} (f : A -> list B) (d : deque (element A lvle)) {struct d} : list B :=
    match d with lvlproof.T dq => cdeque_concat_map f dq end

with suffix_concat_map {A B lvl} (f : A -> list B) (s : suffix A lvl) {struct s} : list B := 
    match s with Suff d => deque_concat_map f d end

with prefix_concat_map {A B lvl C} (f : A -> list B) (p : prefix A lvl C) {struct p} : list B := 
    match p with 
    | (Pre2 a b) => element_concat_map f a ++ element_concat_map f b
    | (Pre3 a b c) => element_concat_map f a ++ element_concat_map f b ++ element_concat_map f c
    | (Pre4 a b c d e) => element_concat_map f a ++ element_concat_map f b ++ element_concat_map f c ++ element_concat_map f d ++ deque_concat_map f e
    end

with packet_front_concat_map {A B lvl len C} (f : A -> list B) (pkt : lvl_packet A lvl len C) {struct pkt} : list B := 
    match pkt with
    | Hole => []
    | (Triple p pkt _) => prefix_concat_map f p ++ packet_front_concat_map f pkt
    end

with packet_rear_concat_map {A B lvl len C} (f : A -> list B) (pkt : lvl_packet A lvl len C) {struct pkt} : list B :=
    match pkt with
    | Hole => []
    | (Triple _ pkt s) => packet_rear_concat_map f pkt ++ suffix_concat_map f s 
    end

with csteque_concat_map {A B lvl C} (f : A -> list B) (cs : lvl_csteque A lvl C) {struct cs} : list B :=
    match cs with
    | (Small s) => suffix_concat_map f s
    | (Big pkt cs _ _) => 
        packet_front_concat_map f pkt ++
        csteque_concat_map f cs ++
        packet_rear_concat_map f pkt
    end. *)

Inductive P (A : Type) : Type :=
    | PI : A -> P A.
Arguments PI {A}.

Inductive E (A : Type) : Type := 
    | EZ : A -> E A
    | ES : P (E A) -> E A.
Arguments EZ {A}.
Arguments ES {A}.

Fixpoint occ_e {A} (e : E A) {struct e} : nat :=
    match e with 
    | EZ _ => 0
    | ES p => 1 + occ_p p 
    end 

with occ_p {A} (p : P (E A)) {struct p} : nat :=
    match p with 
    | PI e => 1 + occ_e e 
    end.

Equations e_nat {A} (e : E A) : nat by struct e :=
e_nat (EZ a) := 0;
e_nat (ES e) := 1 + e_nat e

with p_nat {A} (p : P (E A)) : nat by struct p := 
p_nat (PZ e) := 1 + e_nat e;
p_nat (PS p) := 1 + p_nat p.


Equations prodN_concat_map {A B lvle lvlp} (f : A -> list B) (p : prodN (element A lvle) lvlp) : list B by struct p := 
prodN_concat_map f (prodZ e) := element_concat_map f e;
prodN_concat_map f (prodS (p1, p2)) := prodN_concat_map f p1 ++ prodN_concat_map f p2

with buffer_concat_map {A B lvle lvlp C} (f : A -> list B) (b : buffer (element A lvle) lvlp C) : list B by struct b :=
buffer_concat_map _ B0 := [];
buffer_concat_map f (B1 a) := prodN_concat_map f a;
buffer_concat_map f (B2 a b) := prodN_concat_map f a ++ prodN_concat_map f b;
buffer_concat_map f (B3 a b c) := prodN_concat_map f a ++ prodN_concat_map f b ++ prodN_concat_map f c;
buffer_concat_map f (B4 a b c d) := prodN_concat_map f a ++ prodN_concat_map f b ++ prodN_concat_map f c ++ prodN_concat_map f d;
buffer_concat_map f (B5 a b c d e) := prodN_concat_map f a ++ prodN_concat_map f b ++ prodN_concat_map f c ++ prodN_concat_map f d ++ prodN_concat_map f e

with dpacket_front_concat_map {A B lvle lvlp len C} (f : A -> list B) (pkt : lvlproof.lvl_packet (element A lvle) lvlp len C) : list B by struct pkt :=
dpacket_front_concat_map _ lvlproof.Hole := [];
dpacket_front_concat_map f (lvlproof.Triple p pkt _ _) := 
  buffer_concat_map f p ++ dpacket_front_concat_map f pkt

with dpacket_rear_concat_map {A B lvle lvlp len C} (f : A -> list B) (pkt : lvlproof.lvl_packet (element A lvle) lvlp len C) : list B by struct pkt :=
dpacket_rear_concat_map _ lvlproof.Hole := [];
dpacket_rear_concat_map f (lvlproof.Triple _ pkt s _) := 
  dpacket_rear_concat_map f pkt ++ buffer_concat_map f s

with cdeque_concat_map {A B lvle lvlp C} (f : A -> list B) (cd : lvl_cdeque (element A lvle) lvlp C) : list B by struct cd :=
cdeque_concat_map f (lvlproof.Small b) := buffer_concat_map f b;
cdeque_concat_map f (lvlproof.Big pkt cd _ _) := 
    dpacket_front_concat_map f pkt ++
    cdeque_concat_map f cd ++
    dpacket_rear_concat_map f pkt

with deque_concat_map {A B lvle} (f : A -> list B) (d : deque (element A lvle)) : list B by struct d :=
deque_concat_map f (lvlproof.T dq) := cdeque_concat_map f dq

with suffix_concat_map {A B lvl} (f : A -> list B) (s : suffix A lvl) : list B by struct s := 
suffix_concat_map f (Suff d) := deque_concat_map f d

with prefix_concat_map {A B lvl C} (f : A -> list B) (p : prefix A lvl C) : list B by struct p := 
prefix_concat_map f (Pre2 a b) := element_concat_map f a ++ element_concat_map f b;
prefix_concat_map f (Pre3 a b c) := element_concat_map f a ++ element_concat_map f b ++ element_concat_map f c;
prefix_concat_map f (Pre4 a b c d e) := element_concat_map f a ++ element_concat_map f b ++ element_concat_map f c ++ element_concat_map f d ++ deque_concat_map f e

with element_concat_map {A B lvl} (f : A -> list B) (e : element A lvl) : list B by struct e := 
element_concat_map f (ZElt a) := f a;
element_concat_map f (SElt p cs) := prefix_concat_map f p ++ csteque_concat_map f cs

with packet_front_concat_map {A B lvl len C} (f : A -> list B) (pkt : lvl_packet A lvl len C) : list B by struct pkt := 
packet_front_concat_map _ Hole := [];
packet_front_concat_map f (Triple p pkt _) := 
    prefix_concat_map f p ++ packet_front_concat_map f pkt

with packet_rear_concat_map {A B lvl len C} (f : A -> list B) (pkt : lvl_packet A lvl len C) : list B by struct pkt :=
packet_rear_concat_map _ Hole := [];
packet_rear_concat_map f (Triple _ pkt s) :=
    packet_rear_concat_map f pkt ++ suffix_concat_map f s 

with csteque_concat_map {A B lvl C} (f : A -> list B) (cs : lvl_csteque A lvl C) : list B by struct cs :=
csteque_concat_map f (Small s) := suffix_concat_map f s;
csteque_concat_map f (Big pkt cs eq_refl _) := 
    packet_front_concat_map f pkt ++
    csteque_concat_map f cs ++
    packet_rear_concat_map f pkt.








(* Equations prodN_seq {A lvle lvlp} : prodN (element A lvle) lvlp -> list A := 
prodN_seq (prodZ a) := element_seq a;
prodN_seq (prodS (p1, p2)) := prodN_seq p1 ++ prodN_seq p2

with buffer_seq {A lvle lvlp C} : buffer (element A lvle) lvlp C -> list A :=
buffer_seq B0 := [];
buffer_seq (B1 a) := prodN_seq a;
buffer_seq (B2 a b) := prodN_seq a ++ prodN_seq b;
buffer_seq (B3 a b c) := prodN_seq a ++ prodN_seq b ++ prodN_seq c;
buffer_seq (B4 a b c d) := prodN_seq a ++ prodN_seq b ++ prodN_seq c ++ prodN_seq d;
buffer_seq (B5 a b c d e) := prodN_seq a ++ prodN_seq b ++ prodN_seq c ++ prodN_seq d ++ prodN_seq e

with dpacket_front_seq {A lvle lvlp len C} : lvlproof.lvl_packet (element A lvle) lvlp len C -> list A :=
dpacket_front_seq lvlproof.Hole := [];
dpacket_front_seq (lvlproof.Triple p pkt _ _) := 
  buffer_seq p ++ dpacket_front_seq pkt

with dpacket_rear_seq {A lvle lvlp len C} : lvlproof.lvl_packet (element A lvle) lvlp len C -> list A :=
dpacket_rear_seq lvlproof.Hole := [];
dpacket_rear_seq (lvlproof.Triple _ pkt s _) := 
  dpacket_rear_seq pkt ++ buffer_seq s

with cdeque_seq {A lvle lvlp C} : lvl_cdeque (element A lvle) lvlp C -> list A :=
cdeque_seq (lvlproof.Small b) := buffer_seq b;
cdeque_seq (lvlproof.Big pkt cd _ _) := 
    dpacket_front_seq pkt ++
    cdeque_seq cd ++
    dpacket_rear_seq pkt

with deque_seq {A lvle} : deque (element A lvle) -> list A :=
deque_seq (lvlproof.T dq) := cdeque_seq dq

with suffix_seq {A lvl} : suffix A lvl -> list A := 
suffix_seq (Suff d) := deque_seq d

with prefix_seq {A lvl C} : prefix A lvl C -> list A := 
prefix_seq (Pre2 a b) := element_seq a ++ element_seq b;
prefix_seq (Pre3 a b c) := element_seq a ++ element_seq b ++ element_seq c;
prefix_seq (Pre4 a b c d e) := element_seq a ++ element_seq b ++ element_seq c ++ element_seq d ++ deque_seq e

with element_seq {A lvl} : element A lvl -> list A := 
element_seq (ZElt a) := [a];
element_seq (SElt p cs) := prefix_seq p ++ csteque_seq cs

with packet_front_seq {A lvl len C} : lvl_packet A lvl len C -> list A := 
packet_front_seq Hole := [];
packet_front_seq (Triple p pkt _) := 
    prefix_seq p ++ packet_front_seq pkt

with packet_rear_seq {A lvl len C} : lvl_packet A lvl len C -> list A :=
packet_rear_seq Hole := [];
packet_rear_seq (Triple _ pkt s) :=
    packet_rear_seq pkt ++ suffix_seq s 

with csteque_seq {A lvl C} : lvl_csteque A lvl C -> list A :=
csteque_seq (Small s) := suffix_seq s;
csteque_seq (Big pkt cs eq_refl _) := 
    packet_front_seq pkt ++
    csteque_seq cs ++
    packet_rear_seq pkt. *)








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

Equations suffix_seq {A lvl} : suffix A lvl -> list A := 
suffix_seq (Suff d) := deque_concat_map element_seq d

with prefix_seq {A lvl C} : prefix A lvl C -> list A := 
prefix_seq (Pre2 a b) := element_seq a ++ element_seq b;
prefix_seq (Pre3 a b c) := element_seq a ++ element_seq b ++ element_seq c;
prefix_seq (Pre4 a b c d e) := element_seq a ++ element_seq b ++ element_seq c ++ element_seq d ++ deque_concat_map element_seq e

with element_seq {A lvl} : element A lvl -> list A := 
element_seq (ZElt a) := [a];
element_seq (SElt p cs) := prefix_seq p ++ csteque_seq cs

with packet_front_seq {A lvl len C} : lvl_packet A lvl len C -> list A := 
packet_front_seq Hole := [];
packet_front_seq (Triple p pkt _) := 
    prefix_seq p ++ packet_front_seq pkt

with packet_rear_seq {A lvl len C} : lvl_packet A lvl len C -> list A :=
packet_rear_seq Hole := [];
packet_rear_seq (Triple _ pkt s) :=
    packet_rear_seq pkt ++ suffix_seq s 

with csteque_seq {A lvl C} : lvl_csteque A lvl C -> list A :=
csteque_seq (Small s) := suffix_seq s;
csteque_seq (Big pkt cs eq_refl _) := 
    packet_front_seq pkt ++
    csteque_seq cs ++
    packet_rear_seq pkt.