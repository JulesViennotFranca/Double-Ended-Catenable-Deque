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

Inductive struct_kind : Type := Element | Packet | Csteque.
Derive NoConfusion for struct_kind.

Inductive structure (A : Type) : struct_kind -> nat -> nat -> color -> Type := 
  | ZElt : A -> structure A Element 0 0 uncolored 
  | SElt {lvl : nat} {C1 C2 : color} : 
      prefix' (structure A Element lvl 0 uncolored) C1 ->
      structure A Csteque (S lvl) 0 C2 ->
      structure A Element (S lvl) 0 uncolored
  | Hole {lvl : nat} : structure A Packet lvl 0 uncolored 
  | Triple {lvl len : nat} {Y : yellow_hue} {C : color} :
      prefix' (structure A Element lvl 0 uncolored) C ->
      structure A Packet (S lvl) len (Mix NoGreen Y NoRed) ->
      suffix' (structure A Element lvl 0 uncolored) ->
      structure A Packet lvl (S len) C 
  | Small {lvl : nat} : 
      suffix' (structure A Element lvl 0 uncolored) ->
      structure A Csteque lvl 0 green 
  | Big {lvl len nlvl : nat} {C1 C2 C3 : color} : 
      structure A Packet lvl len C1 ->
      structure A Csteque nlvl 0 C2 ->
      nlvl = len + lvl ->
      csteque_color C1 C2 C3 ->
      structure A Csteque lvl 0 C3.
    
Arguments ZElt {A}.
Arguments SElt {A} lvl {C1 C2}.
Arguments Hole {A lvl}.
Arguments Triple {A} lvl len {Y C}.
Arguments Small {A} lvl.
Arguments Big {A} lvl len {nlvl C1 C2 C3}.

Derive NoConfusion for structure.
Derive Subterm for structure.

Definition element (A : Type) (lvl : nat) := structure A Element lvl 0 uncolored.
Definition lvl_packet (A : Type) := structure A Packet.
Definition lvl_csteque (A : Type) (lvl : nat) (C : color) := structure A Csteque lvl 0 C.

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

Equations suffix'_seq {A} : suffix' A -> list A := 
suffix'_seq (Suff d) := deque_seq d.

Equations prefix'_seq {A C} : prefix' A C -> list A := 
prefix'_seq (Pre2 a b) := [a] ++ [b];
prefix'_seq (Pre3 a b c) := [a] ++ [b] ++ [c];
prefix'_seq (Pre4 a b c d e) := [a] ++ [b] ++ [c] ++ [d] ++ deque_seq e.

Equations map_concat {A B : Type} (f : A -> list B) (l : list A) : list B := 
map_concat f [] := [];
map_concat f (a :: l) := f a ++ map_concat f l.

Inductive seq_kind : Type := SElement | FPacket | RPacket | SCsteque.

Definition seq_kind_to_struct (sk : seq_kind) : struct_kind := 
    match sk with 
    | SElement => Element 
    | FPacket | RPacket => Packet 
    | SCsteque => Csteque 
    end.

Equations to_seq (sk : seq_kind) {A C} (lvl len : nat)
    (s : structure A (seq_kind_to_struct sk) lvl len C) :
    list A by struct := 
to_seq SElement 0 0 (ZElt a) := [a];
to_seq SElement _ 0 (SElt lvl p cs) := 
    map_concat (to_seq SElement lvl 0) (prefix'_seq p) ++
    to_seq SCsteque (S lvl) 0 cs;
to_seq FPacket lvl 0 Hole := [];
to_seq FPacket lvl (S len) (Triple lvl len p pkt _) := 
    map_concat (to_seq SElement lvl 0) (prefix'_seq p) ++
    to_seq FPacket (S lvl) len pkt;
to_seq RPacket lvl 0 Hole := [];
to_seq RPacket lvl (S len) (Triple lvl len _ pkt s) :=
    to_seq RPacket (S lvl) len pkt ++
    map_concat (to_seq SElement lvl 0) (suffix'_seq s);
to_seq SCsteque lvl 0 (Small lvl s) := 
    map_concat (to_seq SElement lvl 0) (suffix'_seq s);
to_seq SCsteque lvl 0 (Big lvl len pkt cs eq_refl _) :=
    to_seq FPacket lvl len pkt ++
    to_seq SCsteque (len + lvl) 0 cs ++
    to_seq RPacket lvl len pkt.

Lemma to_seq {A len} lvl C (sk : seq_kind) : structure A (seq_kind_to_struct sk) lvl len C -> list A.
Proof.
  revert lvl C sk. induction len.
  - intros lvl C sk s. destruct sk; dependent destruction s; [exact [a] | exact [] | exact []].
  - intros lvl C sk s. destruct sk; dependent destruction s.
    + exact [a].
    + apply (IHlen (S lvl) C2 SCsteque) in s.
      apply prefix'_seq in p.
      apply (map_concat (IHlen lvl uncolored SElement)) in p.
      exact (p ++ s).
    + apply (IHlen (S lvl) (Mix NoGreen Y NoRed) FPacket) in s.
      apply prefix'_seq in p.
      apply (map_concat (IHlen lvl uncolored SElement)) in p.
      exact (p ++ s).
    + apply (IHlen (S lvl) (Mix NoGreen Y NoRed) RPacket) in s.
      apply suffix'_seq in s0.
      apply (map_concat (IHlen lvl uncolored SElement)) in s0.
      exact (s ++ s0).
    + apply suffix'_seq in s.
      apply (map_concat (IHlen lvl uncolored SElement)) in s.
      exact s.
    + apply (IHlen (len + lvl) C2 SCsteque) in s2.
      apply (IHlen lvl C1 FPacket) in s1 as p.
      apply (IHlen lvl C1 RPacket) in s1 as s.
      exact (p ++ s2 ++ s).
Defined.

Print to_seq.
      
(* 

Equations to_seq (sk : seq_kind) {A lvl len C} :
    structure A (seq_kind_to_struct sk) lvl len C -> list A by wf len := 
to_seq SElement (ZElt a) := [a];
to_seq SElement (SElt p cs) := 
    map_concat (fun elt => to_seq SElement elt) (prefix'_seq p) ++
    to_seq SCsteque cs;
to_seq FPacket Hole := [];
to_seq FPacket (Triple p pkt _) := 
    map_concat (fun elt => to_seq SElement elt) (prefix'_seq p) ++
    to_seq FPacket pkt;
to_seq RPacket Hole := [];
to_seq RPacket (Triple _ pkt s) :=
    to_seq RPacket pkt ++
    map_concat (fun elt => to_seq SElement elt) (suffix'_seq s);
to_seq SCsteque (Small s) := 
    map_concat (fun elt => to_seq SElement elt) (suffix'_seq s);
to_seq SCsteque (Big pkt cs eq_refl _) :=
    to_seq FPacket pkt ++
    to_seq SCsteque cs ++
    to_seq RPacket pkt.

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
    structure_seq RPacket pkt. *)

Definition element_seq {A lvl len} := 
    to_seq (A := A) (len := len) lvl uncolored SElement.
Print element_seq.
Definition csteque_seq {A C lvl dpt} := 
    to_seq CSteque (A := A) (C := C) (lvl := lvl) (len := 0) (dpt := dpt).

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