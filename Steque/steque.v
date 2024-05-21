From Coq Require Import ssreflect.
From Coq Require Import Program List Lia.
Import ListNotations.
From Equations Require Import Equations.
From Hammer Require Import Tactics.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Dequeue Require Import deque.

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

Inductive any_prefix A lvl :=
| Any_prefix {C : color} : prefix A lvl C -> any_prefix A lvl.
Arguments Any_prefix {A lvl C}.

Inductive gy_prefix A lvl :=
| GY_prefix {G Y} : prefix A lvl (Mix G Y NoRed) -> gy_prefix A lvl.
Arguments GY_prefix {A lvl G Y}.

Inductive any_csteque A lvl :=
| Any_csteque {C : color} : csteque A lvl C -> any_csteque A lvl.
Arguments Any_csteque {A lvl C}.

Inductive gy_csteque A lvl :=
| GY_csteque {G Y} : csteque A lvl (Mix G Y NoRed) -> gy_csteque A lvl.
Arguments GY_csteque {A lvl G Y}.

Inductive partition (A : Type) (lvl : nat) : Type :=
| PSmall : suffix A lvl -> partition A lvl
| PBig {C1 C2 : color} : prefix A lvl C1 -> csteque A (S lvl) C2 -> suffix A lvl -> partition A lvl.
Arguments PSmall {A lvl}.
Arguments PBig {A lvl C1 C2}.

(* A type for steque. *)

Inductive steque (A : Type) : Type := 
  T : gy_csteque A 0 -> 
      steque A.
Arguments T {A}.

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
    | deque.Hole => []
    | deque.Triple p pkt _ _ => buffer_seq p ++ dpacket_front_seq pkt 
    end in
  let fix dpacket_rear_seq {lvle lvlp len C} (pkt : lvl_packet (element A lvle) lvlp len C) : list A :=
    match pkt with 
    | deque.Hole => []
    | deque.Triple _ pkt s _ => dpacket_rear_seq pkt ++ buffer_seq s
    end in
  let fix cdeque_seq {lvle lvlp C} (cd : lvl_cdeque (element A lvle) lvlp C) : list A :=
    match cd with
    | deque.Small b => buffer_seq b
    | deque.Big pkt cd _ _ => dpacket_front_seq pkt ++ cdeque_seq cd ++ dpacket_rear_seq pkt
    end in
  let prefix_seq {lvl C} (p : prefix A lvl C) : list A :=
    match p with 
    | Pre2 e1 e2 => element_seq e1 ++ element_seq e2 
    | Pre3 e1 e2 e3 => element_seq e1 ++ element_seq e2 ++ element_seq e3
    | Pre4 e1 e2 e3 e4 (deque.T d) => 
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
    | Triple _ pkt (Suff (deque.T d)) => packet_rear_seq pkt ++ cdeque_seq d
    end in
  let fix csteque_seq {lvl C} (cs : csteque A lvl C) : list A :=
    match cs with 
    | Small (Suff (deque.T d)) => cdeque_seq d
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

Equations any_prefix_seq {A lvl} : any_prefix A lvl -> list A :=
any_prefix_seq (Any_prefix p) := prefix_seq p.

Equations gy_prefix_seq {A lvl} : gy_prefix A lvl -> list A :=
gy_prefix_seq (GY_prefix p) := prefix_seq p.

Equations packet_front_seq {A lvl len C} : packet A lvl len C -> list A :=
packet_front_seq Hole := [];
packet_front_seq (Triple p pkt _) := prefix_seq p ++ packet_front_seq pkt.

Equations packet_rear_seq {A lvl len C} : packet A lvl len C -> list A :=
packet_rear_seq Hole := [];
packet_rear_seq (Triple _ pkt s) := packet_rear_seq pkt ++ suffix_seq s.

Equations csteque_seq {A lvl C} : csteque A lvl C -> list A :=
csteque_seq (Small s) := suffix_seq s;
csteque_seq (Big pkt cs _ _) := packet_front_seq pkt ++ csteque_seq cs ++ packet_rear_seq pkt.

Equations any_csteque_seq {A lvl} : any_csteque A lvl -> list A :=
any_csteque_seq (Any_csteque cs) := csteque_seq cs.

Equations gy_csteque_seq {A lvl} : gy_csteque A lvl -> list A :=
gy_csteque_seq (GY_csteque cs) := csteque_seq cs.

Equations partition_seq {A lvl} : partition A lvl -> list A :=
partition_seq (PSmall s) := suffix_seq s;
partition_seq (PBig p child s) := prefix_seq p ++ csteque_seq child ++ suffix_seq s.

Equations steque_seq {A} : steque A -> list A :=
steque_seq (T cs) := gy_csteque_seq cs.

Unset Equations Transparent.

Notation "? x" := (@exist _ _ x _) (at level 100).

(* Element *)

Opaque app.
Definition singleton {A : Type} (x : A) : list A := [x].
Opaque singleton.

Lemma Selement_seq : forall [A lvl C1 C2] 
    (p : prefix A lvl C1)
    (cs : csteque A (S lvl) C2),
    element_seq (SElt p cs) = prefix_seq p ++ csteque_seq cs.
Proof. Admitted.

(* A list of tactics to be used when trying to resolve obligations generated by
   Equations. *)

#[export] Hint Rewrite <-app_assoc : rlist.
#[export] Hint Rewrite <-app_comm_cons : rlist.
#[export] Hint Rewrite app_nil_r : rlist.
#[export] Hint Rewrite map_app : rlist.
#[export] Hint Rewrite concat_app : rlist.
#[export] Hint Rewrite Selement_seq : rlist.

#[local] Obligation Tactic :=
  try first [ done | cbn; hauto db:rlist ].

Equations cempty {A lvl} : { cs : csteque A lvl green | csteque_seq cs = [] } :=
cempty with deque.empty => {
    | ? d := ? Small (Suff d) }.

(* Functions *)

Equations green_steque {A lvl C} 
    (p : prefix A lvl green)
    (cs : csteque A (S lvl) C)
    (s : suffix A lvl) :
    { cs' : csteque A lvl green | 
        csteque_seq cs' = prefix_seq p ++ csteque_seq cs ++ suffix_seq s } :=
green_steque p (Small s') s := ? Big (Triple p Hole s) (Small s') eq_refl CCGreen;
green_steque p (Big pkt cs' eq_refl CCGreen) s := 
    ? Big (Triple p Hole s) (Big pkt cs' eq_refl CCGreen) eq_refl CCGreen;
green_steque p (Big pkt cs' eq_refl CCYellow) s :=
    ? Big (Triple p pkt s) cs' _ CCGreen;
green_steque p (Big pkt cs' eq_refl CCOrange) s :=
    ? Big (Triple p pkt s) cs' _ CCGreen;
green_steque p (Big pkt cs' eq_refl CCRed) s :=
    ? Big (Triple p Hole s) (Big pkt cs' eq_refl CCRed) eq_refl CCGreen. 

Equations yellow_steque {A lvl G Y}
    (p : prefix A lvl yellow)
    (cs : csteque A (S lvl) (Mix G Y NoRed))
    (s : suffix A lvl) : 
    { cs' : csteque A lvl yellow | 
        csteque_seq cs' = prefix_seq p ++ csteque_seq cs ++ suffix_seq s } :=
yellow_steque p (Small s') s := ? Big (Triple p Hole s) (Small s') eq_refl CCYellow;
yellow_steque p (Big pkt cs' eq_refl CCGreen) s :=
    ? Big (Triple p Hole s) (Big pkt cs' eq_refl CCGreen) eq_refl CCYellow;
yellow_steque p (Big pkt cs' eq_refl CCYellow) s :=
    ? Big (Triple p pkt s) cs' _ CCYellow.

Equations orange_steque {A lvl}
    (p : prefix A lvl yellow)
    (cs : any_csteque A (S lvl))
    (s : suffix A lvl) :
    { cs' : any_csteque A lvl | 
        any_csteque_seq cs' = prefix_seq p ++ any_csteque_seq cs ++ suffix_seq s } :=
orange_steque p (Any_csteque (Small s')) s := 
    ? Any_csteque (Big (Triple p Hole s) (Small s') eq_refl CCYellow);
orange_steque p (Any_csteque (Big pkt cs' eq_refl CCGreen)) s := 
    ? Any_csteque (Big (Triple p Hole s) (Big pkt cs' eq_refl CCGreen) eq_refl CCYellow);
orange_steque p (Any_csteque (Big pkt cs' eq_refl CCYellow)) s :=
    ? Any_csteque (Big (Triple p pkt s) cs' _ CCYellow);
orange_steque p (Any_csteque (Big pkt cs' eq_refl CCOrange)) s :=
    ? Any_csteque (Big (Triple p pkt s) cs' _ CCOrange);
orange_steque p (Any_csteque (Big pkt cs' eq_refl CCRed)) s :=
    ? Any_csteque (Big (Triple p Hole s) (Big pkt cs' eq_refl CCRed) eq_refl CCOrange).

Equations red_steque {A lvl G Y}
    (p : prefix A lvl red)
    (cs : csteque A (S lvl) (Mix G Y NoRed))
    (s : suffix A lvl) :
    { cs' : csteque A lvl red |
        csteque_seq cs' = prefix_seq p ++ csteque_seq cs ++ suffix_seq s } :=
red_steque p (Small s') s := ? Big (Triple p Hole s) (Small s') eq_refl CCRed;
red_steque p (Big pkt cs' eq_refl CCGreen) s :=
    ? Big (Triple p Hole s) (Big pkt cs' eq_refl CCGreen) eq_refl CCRed;
red_steque p (Big pkt cs' eq_refl CCYellow) s := 
    ? Big (Triple p pkt s) cs' _ CCRed.

Equations green_prefix_push {A lvl} 
    (e : element A lvl)
    (p : prefix A lvl green) :
    { p' : prefix A lvl green | prefix_seq p' = element_seq e ++ prefix_seq p } :=
green_prefix_push e (Pre4 e1 e2 e3 e4 d) with deque.push e4 d => {
    | ? d' := ? Pre4 e e1 e2 e3 d' }.

Equations yellow_prefix_push {A lvl}
    (e : element A lvl)
    (p : prefix A lvl yellow) :
    { p' : prefix A lvl green | prefix_seq p' = element_seq e ++ prefix_seq p } :=
yellow_prefix_push e (Pre3 e1 e2 e3) with deque.empty => {
    | ? d := ? Pre4 e e1 e2 e3 d }.

Equations red_prefix_push {A lvl}
    (e : element A lvl)
    (p : prefix A lvl red) :
    { p' : prefix A lvl yellow | prefix_seq p' = element_seq e ++ prefix_seq p } :=
red_prefix_push e (Pre2 e1 e2) := ? Pre3 e e1 e2.

Equations prefix_push {A lvl C}
    (e : element A lvl)
    (p : prefix A lvl C) :
    { p' : gy_prefix A lvl | gy_prefix_seq p' = element_seq e ++ prefix_seq p } :=
prefix_push e (Pre2 e1 e2) := ? GY_prefix (Pre3 e e1 e2);
prefix_push e (Pre3 e1 e2 e3) with deque.empty => {
    | ? d := ? GY_prefix (Pre4 e e1 e2 e3 d) };
prefix_push e (Pre4 e1 e2 e3 e4 d) with deque.push e4 d => {
    | ? d' := ? GY_prefix (Pre4 e e1 e2 e3 d') }.

Equations push_gy {A lvl C}
    (e : element A lvl)
    (cs : csteque A lvl C) :
    { cs' : gy_csteque A lvl | 
        gy_csteque_seq cs' = element_seq e ++ csteque_seq cs } :=
push_gy e (Small (Suff d)) with deque.push e d => {
    | ? d' := ? GY_csteque (Small (Suff d')) };
push_gy e (Big (Triple p pkt s) cs eq_refl CCGreen) with green_prefix_push e p => {
    | ? p' := ? GY_csteque (Big (Triple p' pkt s) cs eq_refl CCGreen) };
push_gy e (Big (Triple p pkt s) cs eq_refl CCYellow) with yellow_prefix_push e p => {
    | ? p' := ? GY_csteque (Big (Triple p' pkt s) cs eq_refl CCGreen) };
push_gy e (Big (Triple p pkt s) cs eq_refl CCOrange) with yellow_prefix_push e p => {
    | ? p' := ? GY_csteque (Big (Triple p' pkt s) cs eq_refl CCGreen) };
push_gy e (Big (Triple p pkt s) cs eq_refl CCRed) with red_prefix_push e p => {
    | ? p' := ? GY_csteque (Big (Triple p' pkt s) cs eq_refl CCYellow) }.

Equations any_push_gy {A lvl}
    (e : element A lvl)
    (cs : any_csteque A lvl) :
    { cs' : gy_csteque A lvl | 
        gy_csteque_seq cs' = element_seq e ++ any_csteque_seq cs } :=
any_push_gy e (Any_csteque cs) := push_gy e cs.

Equations any_push_any {A lvl}
    (e : element A lvl)
    (cs : any_csteque A lvl) :
    { cs' : any_csteque A lvl | 
        any_csteque_seq cs' = element_seq e ++ any_csteque_seq cs } :=
any_push_any e acs with any_push_gy e acs => {
    | ? GY_csteque cs' := ? Any_csteque cs' }.

Equations gy_push_gy {A lvl}
    (e : element A lvl)
    (cs : gy_csteque A lvl) :
    { cs' : gy_csteque A lvl |
        gy_csteque_seq cs' = element_seq e ++ gy_csteque_seq cs } :=
gy_push_gy e (GY_csteque cs) := push_gy e cs.

Equations push {A} (a : A) (s : steque A) :
    { s' : steque A | steque_seq s' = [a] ++ steque_seq s } :=
push a (T cs) with gy_push_gy (ZElt a) cs => {
    | ? cs' := ? (T cs') }.

Equations cinject {A lvl C}
    (cs : csteque A lvl C)
    (e : element A lvl) :
    { cs' : csteque A lvl C | 
        csteque_seq cs' = csteque_seq cs ++ element_seq e } :=
cinject (Small (Suff d)) e with deque.inject d e => {
    | ? d' := ? Small (Suff d') };
cinject (Big (Triple p pkt (Suff d)) cs eq_refl CCGreen) e 
  with deque.inject d e => {
    | ? d' := ? Big (Triple p pkt (Suff d')) cs eq_refl CCGreen };
cinject (Big (Triple p pkt (Suff d)) cs eq_refl CCYellow) e 
  with deque.inject d e => {
    | ? d' := ? Big (Triple p pkt (Suff d')) cs eq_refl CCYellow };
cinject (Big (Triple p pkt (Suff d)) cs eq_refl CCOrange) e 
  with deque.inject d e => {
    | ? d' := ? Big (Triple p pkt (Suff d')) cs eq_refl CCOrange };
cinject (Big (Triple p pkt (Suff d)) cs eq_refl CCRed) e 
  with deque.inject d e => {
    | ? d' := ? Big (Triple p pkt (Suff d')) cs eq_refl CCRed }.

(* Equations any_inject_any {A lvl}
    (cs : any_csteque A lvl)
    (e : element A lvl) :
    { cs' : any_csteque A lvl | 
        any_csteque_seq cs' = any_csteque_seq cs ++ element_seq e } :=
any_inject_any (Any_csteque (Small (Suff d))) e with deque.inject d e => {
    | ? d' := ? Any_csteque (Small (Suff d')) };
any_inject_any (Any_csteque (Big (Triple p pkt (Suff d)) cs eq_refl cc)) e 
  with deque.inject d e => {
    | ? d' := ? Any_csteque (Big (Triple p pkt (Suff d')) cs eq_refl cc) }.

Equations gy_inject_gy {A lvl} 
    (cs : gy_csteque A lvl)
    (e : element A lvl) :
    { cs' : gy_csteque A lvl | 
        gy_csteque_seq cs' = gy_csteque_seq cs ++ element_seq e } :=
gy_inject_gy (GY_csteque (Small (Suff d))) e with deque.inject d e => {
    | ? d' := ? GY_csteque (Small (Suff d')) };
gy_inject_gy (GY_csteque (Big (Triple p pkt (Suff d)) cs eq_refl cc)) e 
  with deque.inject d e => {
    | ? d' := ? GY_csteque (Big (Triple p pkt (Suff d')) cs eq_refl cc) }. *)

Equations inject {A} (s : steque A) (a : A) :
    { s' : steque A | steque_seq s' = steque_seq s ++ [a] } :=
inject (T (GY_csteque cs)) a with cinject cs (ZElt a) => {
    | ? cs' := ? T (GY_csteque cs') }.

Equations cinject_SElt {A lvl C1 C2 C3}
    (child : csteque A (S lvl) C1)
    (p : prefix A lvl C2)
    (cs : csteque A (S lvl) C3) :
    { child' : csteque A (S lvl) C1 |
        csteque_seq child' = csteque_seq child ++ prefix_seq p ++ csteque_seq cs } :=
cinject_SElt child p cs with cinject child (SElt p cs) => {
    | ? child' := ? child' }.
Next Obligation.
  cbn beta. intros * Hchild'.
  rewrite Hchild'. rewrite Selement_seq. reflexivity.
Qed.

Equations suffix_to_prefix {A lvl}
    (e1 e2 : element A lvl)
    (s : suffix A lvl) : 
    { p : any_prefix A lvl | 
        any_prefix_seq p = element_seq e1 ++ element_seq e2 ++ suffix_seq s } :=
suffix_to_prefix e1 e2 (Suff d) with deque.pop d => {
  | ? None := ? Any_prefix (Pre2 e1 e2);
  | ? Some (e3, d') with deque.pop d' => {
    | ? None := ? Any_prefix (Pre3 e1 e2 e3);
    | ? Some (e4, d'') := ? Any_prefix (Pre4 e1 e2 e3 e4 d'') } }.

Equations remove_suffix {A lvl C} 
    (child : csteque A (S lvl) C)
    (s : suffix A lvl)
    (cs2 : any_csteque A lvl) :
    { '(child', cs2') : csteque A (S lvl) C * any_csteque A lvl |
        csteque_seq child' ++ any_csteque_seq cs2' =
            csteque_seq child ++ suffix_seq s ++ any_csteque_seq cs2 } :=
remove_suffix child (Suff d) cs2 with deque.pop d => {
  | ? None => ? (child, cs2);
  | ? Some (e1, d') with deque.pop d' => {
    | ? None with any_push_any e1 cs2 => {
      | ? cs2' := ? (child, cs2') };
    | ? Some (e2, d'') with suffix_to_prefix e1 e2 (Suff d''), cempty => {
      | ? Any_prefix p, ? cs with cinject_SElt child p cs => {
        | ? child' := ? (child', cs2) } } } }.

Equations split_any {A lvl len nlvl G Y R} 
    (pkt : packet A lvl len (Mix NoGreen Y NoRed))
    (cs : csteque A nlvl (Mix G NoYellow R)) :
    nlvl = len + lvl ->
    { cs' : any_csteque A lvl |
        any_csteque_seq cs' = packet_front_seq pkt ++ csteque_seq cs ++ packet_rear_seq pkt } :=
split_any Hole cs eq_refl := ? Any_csteque cs;
split_any (Y := SomeYellow) (Triple p pkt s) (Small suff) eq_refl := 
    ? Any_csteque (Big (Triple p pkt s) (Small suff) eq_refl CCYellow);
split_any (Y := SomeYellow) (Triple p pkt s) (Big pkt' cs' eq_refl CCGreen) eq_refl := 
    ? Any_csteque (Big (Triple p pkt s) (Big pkt' cs' eq_refl CCGreen) eq_refl CCYellow);
split_any (Y := SomeYellow) (Triple p pkt s) (Big pkt' cs' eq_refl CCRed) eq_refl := 
    ? Any_csteque (Big (Triple p pkt s) (Big pkt' cs' eq_refl CCRed) eq_refl CCOrange).

Equations join {A lvl C}
    (child : csteque A (S lvl) C)
    (s : suffix A lvl)
    (cs2 : any_csteque A lvl) :
    { '(child', s') : csteque A (S lvl) C * suffix A lvl |
        csteque_seq child' ++ suffix_seq s' =
            csteque_seq child ++ suffix_seq s ++ any_csteque_seq cs2 } :=
join child s cs2 with remove_suffix child s cs2 => {
    | ? (child', Any_csteque cs2') with cs2' => {
      | Small s' := ? (child', s');
      | Big (Triple p' pkt' s') cs' eq_refl CCGreen with split_any pkt' cs' _ => {
        | ? Any_csteque child2' with cinject_SElt child' p' child2' => {
          | ? child'' := ? (child'', s') } };
      | Big (Triple p' pkt' s') cs' eq_refl CCYellow with split_any pkt' cs' _ => {
        | ? Any_csteque child2' with cinject_SElt child' p' child2' => {
          | ? child'' := ? (child'', s') } };
      | Big (Triple p' pkt' s') cs' eq_refl CCOrange with split_any pkt' cs' _ => {
        | ? Any_csteque child2' with cinject_SElt child' p' child2' => {
          | ? child'' := ? (child'', s') } };
      | Big (Triple p' pkt' s') cs' eq_refl CCRed with split_any pkt' cs' _ => {
        | ? Any_csteque child2' with cinject_SElt child' p' child2' => {
          | ? child'' := ? (child'', s') } } } }.

Equations partitioned {A lvl} (cs : any_csteque A lvl) :
    { p : partition A lvl | partition_seq p = any_csteque_seq cs } :=
partitioned (Any_csteque (Small s)) := ? PSmall s;
partitioned (Any_csteque (Big (Triple p Hole s) cs eq_refl _)) :=
    ? PBig p cs s;
partitioned (Any_csteque (Big (Triple (Y := SomeYellow) p (Triple p' pkt s') s) (Small suff) eq_refl CCGreen)) :=
    ? PBig p (Big (Triple p' pkt s') (Small suff) _ CCYellow) s;
partitioned (Any_csteque (Big (Triple (Y := SomeYellow) p (Triple p' pkt s') s) (Big pkt' cs' eq_refl CCGreen) eq_refl CCGreen)) :=
    ? PBig p (Big (Triple p' pkt s') (Big pkt' cs' eq_refl CCGreen) _ CCYellow) s;
partitioned (Any_csteque (Big (Triple (Y := SomeYellow) p (Triple p' pkt s') s) (Big pkt' cs' eq_refl CCRed) eq_refl CCGreen)) :=
    ? PBig p (Big (Triple p' pkt s') (Big pkt' cs' eq_refl CCRed) _ CCOrange) s;
partitioned (Any_csteque (Big (Triple (Y := SomeYellow) p (Triple p' pkt s') s) cs eq_refl CCYellow)) :=
    ? PBig p (Big (Triple p' pkt s') cs _ CCYellow) s;
partitioned (Any_csteque (Big (Triple (Y := SomeYellow) p (Triple p' pkt s') s) cs eq_refl CCOrange)) :=
    ? PBig p (Big (Triple p' pkt s') cs _ CCOrange) s;
partitioned (Any_csteque (Big (Triple (Y := SomeYellow) p (Triple p' pkt s') s) cs eq_refl CCRed)) :=
    ? PBig p (Big (Triple p' pkt s') cs _ CCYellow) s.

Equations concat_csteque {A lvl C}
    (cs1 : csteque A lvl C)
    (cs2 : any_csteque A lvl) :
    { cs3 : any_csteque A lvl | 
        any_csteque_seq cs3 = csteque_seq cs1 ++ any_csteque_seq cs2 } :=
concat_csteque (Small (Suff d)) cs2 with deque.pop d => {
  | ? None := ? cs2;
  | ? Some (e1, d1) with deque.pop d1 => {
    | ? None with any_push_any e1 cs2 => { | ? cs3 := ? cs3 };
    | ? Some (e2, d2) with deque.pop d2 => {
      | ? None with any_push_any e2 cs2 => {
        | ? cs3' with any_push_any e1 cs3' => { | ? cs3 := ? cs3 } };
      | ? Some (e3, d3) with deque.pop d3 => {
        | ? None with any_push_any e3 cs2 => {
          | ? cs3'' with any_push_any e2 cs3'' => {
            | ? cs3' with any_push_any e1 cs3' => { | ? cs3 := ? cs3 } } };
        | ? Some (e4, d4) with partitioned cs2, cempty => {
          | ? PSmall s2, ? cs := 
            ? Any_csteque (Big (Triple (Pre4 e1 e2 e3 e4 d4) Hole s2) cs eq_refl CCGreen);
          | ? PBig p2 child2 s2, ? cs with any_push_gy (SElt p2 cs) child2 => {
            | ? GY_csteque child2' with green_steque (Pre4 e1 e2 e3 e4 d4) child2' s2 => {
              | ? cs3 := ? Any_csteque cs3 } } } } } } }.

(*
let concat_csteque
: type a c. (a, c) csteque -> a any_csteque -> a any_csteque
= fun x ty ->
  match x with
  (* If our first colored steque is only a suffix, we look at the number of 
     elements it contains. *)
  | Suffix small ->
      begin match Deque.pop small with
      (* No elements, return ty. *)
      | None -> ty
      | Some (x, small) ->
          match Deque.pop small with
          (* One element, push it onto ty. *)
          | None -> push_any x ty
          | Some (y, small) ->
              match Deque.pop small with
              (* Two elements, push them in the right order onto ty. *)
              | None -> push_any x (push_any y ty)
              | Some (z, small) ->
                  match Deque.pop small with
                  (* Three elements, push them in the right order onto ty. *)
                  | None -> push_any x (push_any y (push_any z ty))
                  | Some (w, small) ->
                      (* If we have four or more elements, x can be considered
                         a green prefix. *)
                      let prefix = P4 (x, y, z, w, small) in
                      (* We look wether ty is a suffix or not. *)
                      match partitioned ty with
                      (* If it is the case, we can directly return the green 
                         steque (x, empty, ty) = (prefix, empty, c) here. *)
                      | Small c ->
                          Any_csteque (G (Triple (prefix, HOLE, c), empty_csteque))
                      (* If ty is a triple, its prefix is pushed onto its child 
                         and the final steque is simply (x, child(ty), suffix(ty))
                         = (prefix, child, suffix) here. *)
                      | Parts (p, child, suffix) ->
                          let T child =
                            push_any' (Pair (p, empty_csteque)) (Any_csteque child)
                          in
                          Any_csteque (green prefix child suffix)
      end
  (* Otherwise, we get the child of x with a split function, and use a join 
     function to concatenate the two steques. *)
  | G (Triple (prefix, child, s), csteque) ->
      let Any_csteque child = split_csteque Green_or_red child csteque in
      let Any_csteque rest, suffix = join_any child s ty in
      Any_csteque (green prefix rest suffix)

  | Y (Triple (prefix, child, s), csteque) ->
      let child = split_green child csteque in
      let child, suffix = join_t child s ty in
      Any_csteque (yellow prefix child suffix)

  | Yr (Triple (prefix, child, s), csteque) ->
      let Any_csteque child = split_red child csteque in
      let child, suffix = join_any child s ty in
      orange prefix child suffix

  | R (Triple (prefix, child, s), csteque) ->
      let child = split_green child csteque in
      let child, suffix = join_t child s ty in
      Any_csteque (red prefix child suffix)
*)
