From Coq Require Import ssreflect.
From Coq Require Import Program List Lia.
Import ListNotations.
From Equations Require Import Equations.
From Hammer Require Import Tactics.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deq Require Import deque.

(* Types *)

(* A new color is introduced. *)

Notation orange := (Mix NoGreen SomeYellow SomeRed).

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

(* Types for suffix and prefix containing elements. *)

Definition suffix A lvl := suffix' (element A lvl).
Definition prefix A lvl := prefix' (element A lvl).

(* A type for prefix of any color. *)

Inductive any_prefix A lvl :=
| Any_prefix {C : color} : prefix A lvl C -> any_prefix A lvl.
Arguments Any_prefix {A lvl C}.

(* A type for green or yellow prefix. *)

Inductive gy_prefix A lvl :=
| GY_prefix {G Y} : prefix A lvl (Mix G Y NoRed) -> gy_prefix A lvl.
Arguments GY_prefix {A lvl G Y}.

(* A type for steque of any color. *)

Inductive any_csteque A lvl :=
| Any_csteque {C : color} : csteque A lvl C -> any_csteque A lvl.
Arguments Any_csteque {A lvl C}.

(* A type for green or yellow steque. *)

Inductive gy_csteque A lvl :=
| GY_csteque {G Y} : csteque A lvl (Mix G Y NoRed) -> gy_csteque A lvl.
Arguments GY_csteque {A lvl G Y}.

(* A type for colored steque partition. A partition of a colored steque is its 
   natural representation : without the packet type. It is either a suffix, 
   [PSmall], or a triple prefix - child - suffix, [PBig]. *)

Inductive partition (A : Type) (lvl : nat) : Type :=
| PSmall : suffix A lvl -> partition A lvl
| PBig {C1 C2 : color} : prefix A lvl C1 -> csteque A (S lvl) C2 -> suffix A lvl -> partition A lvl.
Arguments PSmall {A lvl}.
Arguments PBig {A lvl C1 C2}.

(* A type for steque. *)

Inductive steque (A : Type) : Type := 
| T {G : green_hue} {Y : yellow_hue} : 
    csteque A 0 (Mix G Y NoRed) -> 
    steque A.
Arguments T {A G Y}.

(* Models *)

Set Equations Transparent.

(* Returns the sequence contained in an element. *)

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
    | B4 p1 p2 p3 p4 => 
      prodN_seq p1 ++ prodN_seq p2 ++ prodN_seq p3 ++ prodN_seq p4
    | B5 p1 p2 p3 p4 p5 => 
      prodN_seq p1 ++ prodN_seq p2 ++ prodN_seq p3 ++ prodN_seq p4 ++ prodN_seq p5
    end in 
  let fix dpacket_front_seq {lvle lvlp len C} 
      (pkt : lvl_packet (element A lvle) lvlp len C) : list A :=
    match pkt with 
    | deque.Hole => []
    | deque.Triple p pkt _ _ => buffer_seq p ++ dpacket_front_seq pkt 
    end in
  let fix dpacket_rear_seq {lvle lvlp len C} 
      (pkt : lvl_packet (element A lvle) lvlp len C) : list A :=
    match pkt with 
    | deque.Hole => []
    | deque.Triple _ pkt s _ => dpacket_rear_seq pkt ++ buffer_seq s
    end in
  let fix cdeq_seq {lvle lvlp C} 
      (cd : lvl_cdeque (element A lvle) lvlp C) : list A :=
    match cd with
    | deque.Small b => buffer_seq b
    | deque.Big pkt cd _ _ => 
      dpacket_front_seq pkt ++ 
      cdeq_seq cd ++ 
      dpacket_rear_seq pkt
    end in
  let prefix_seq {lvl C} (p : prefix A lvl C) : list A :=
    match p with 
    | Pre2 e1 e2 => element_seq e1 ++ element_seq e2 
    | Pre3 e1 e2 e3 => element_seq e1 ++ element_seq e2 ++ element_seq e3
    | Pre4 e1 e2 e3 e4 (deque.T d) => 
      element_seq e1 ++ element_seq e2 ++ element_seq e3 ++ element_seq e4 ++ 
      cdeq_seq d
    end in
  let fix packet_front_seq {lvl len C} (pkt : packet A lvl len C) : list A :=
    match pkt with
    | Hole => []
    | Triple p pkt _ => prefix_seq p ++ packet_front_seq pkt
    end in
  let fix packet_rear_seq {lvl len C} (pkt : packet A lvl len C) : list A :=
    match pkt with
    | Hole => []
    | Triple _ pkt (Suff (deque.T d)) => packet_rear_seq pkt ++ cdeq_seq d
    end in
  let fix csteque_seq {lvl C} (cs : csteque A lvl C) : list A :=
    match cs with 
    | Small (Suff (deque.T d)) => cdeq_seq d
    | Big pkt cs _ _ => 
      packet_front_seq pkt ++ 
      csteque_seq cs ++ 
      packet_rear_seq pkt
    end in
  match e with 
  | ZElt a => [a]
  | SElt p cs => prefix_seq p ++ csteque_seq cs 
  end.

(* Returns the sequence contained in a suffix. *)

Equations suffix_seq {A lvl} : suffix A lvl -> list A := 
suffix_seq (Suff d) := concat (map element_seq (deque_seq d)).

(* Returns the sequence contained in a prefix. *)

Equations prefix_seq {A lvl C} : prefix A lvl C -> list A :=
prefix_seq (Pre2 e1 e2) := element_seq e1 ++ element_seq e2;
prefix_seq (Pre3 e1 e2 e3) := element_seq e1 ++ element_seq e2 ++ element_seq e3;
prefix_seq (Pre4 e1 e2 e3 e4 d) := 
    element_seq e1 ++ element_seq e2 ++ element_seq e3 ++ element_seq e4 ++
    concat (map element_seq (deque_seq d)).

(* Returns the sequence contained in a prefix of any color. *)

Equations any_prefix_seq {A lvl} : any_prefix A lvl -> list A :=
any_prefix_seq (Any_prefix p) := prefix_seq p.

(* Returns the sequence contained in a green or yellow prefix. *)

Equations gy_prefix_seq {A lvl} : gy_prefix A lvl -> list A :=
gy_prefix_seq (GY_prefix p) := prefix_seq p.

(* Returns the sequence of elements stored in prefixes along a packet. *)

Equations packet_front_seq {A lvl len C} : packet A lvl len C -> list A :=
packet_front_seq Hole := [];
packet_front_seq (Triple p pkt _) := prefix_seq p ++ packet_front_seq pkt.

(* Returns the sequence of elements stored in suffixes along a packet. *)

Equations packet_rear_seq {A lvl len C} : packet A lvl len C -> list A :=
packet_rear_seq Hole := [];
packet_rear_seq (Triple _ pkt s) := packet_rear_seq pkt ++ suffix_seq s.

(* Returns the sequence contained in a colored steque. *)

Equations csteque_seq {A lvl C} : csteque A lvl C -> list A :=
csteque_seq (Small s) := suffix_seq s;
csteque_seq (Big pkt cs _ _) := packet_front_seq pkt ++ csteque_seq cs ++ packet_rear_seq pkt.

(* Returns the sequence contained in a steque of any color. *)

Equations any_csteque_seq {A lvl} : any_csteque A lvl -> list A :=
any_csteque_seq (Any_csteque cs) := csteque_seq cs.

(* Returns the sequence contained in a green or yellow steque. *)

Equations gy_csteque_seq {A lvl} : gy_csteque A lvl -> list A :=
gy_csteque_seq (GY_csteque cs) := csteque_seq cs.

(* Returns the sequence contained in a parition. *)

Equations partition_seq {A lvl} : partition A lvl -> list A :=
partition_seq (PSmall s) := suffix_seq s;
partition_seq (PBig p child s) := prefix_seq p ++ csteque_seq child ++ suffix_seq s.

(* Returns the sequence contained in a steque. *)

Equations steque_seq {A} : steque A -> list A :=
steque_seq (T cs) := csteque_seq cs.

Unset Equations Transparent.

Notation "? x" := (@exist _ _ x _) (at level 100).

(* Element *)

Opaque app.
Definition singleton {A : Type} (x : A) : list A := [x].
Opaque singleton.

(* A list of tactics to be used when trying to resolve obligations generated by
   Equations. *)

#[export] Hint Rewrite <-app_assoc : rlist.
#[export] Hint Rewrite <-app_comm_cons : rlist.
#[export] Hint Rewrite app_nil_r : rlist.
#[export] Hint Rewrite map_app : rlist.
#[export] Hint Rewrite concat_app : rlist.

(* A lemma that destructs an equality of one app into 2 subgoals. *)

Lemma div_app2 {A : Type} {l1 l1' l2 l2' : list A} : 
    l1 = l1' -> l2 = l2' -> l1 ++ l2 = l1' ++ l2'.
Proof. intros [] []. reflexivity. Qed.

(* A tactic that cleans the removes the useless hypothesis. *)

Local Ltac clear_h := 
  repeat 
  match goal with
  | H : _ |- _ => clear H
  end.

(* A lemma proving that we have the desired relation between 
   element_seq (SElt p cs), prefix_seq p and csteque_seq cs. *)

Lemma Selement_seq [A lvl C1 C2] 
    (p : prefix A lvl C1) (cs : csteque A (S lvl) C2) :
    element_seq (SElt p cs) = prefix_seq p ++ csteque_seq cs.
Proof. 
  simpl element_seq.
  (* We start by destroying the prefix. *)
  destruct p as [e1 e2 | e1 e2 e3 | e1 e2 e3 e4 [G Y c]];
  (* Format for simplification. *)
  cbn; autorewrite with rlist;
  (* Remove element sequences at the beginning. *)
  repeat apply (f_equal (fun l => _ ++ l));
  (* Split the cdeq and csteque parts from the Pre4 case. *)
  try (apply div_app2; clear_h);
  (* For csteques cases, we start an induction. *)
  try (induction cs as [ ? [[G Y c]] | ?????? pkt cs ? e cc ]; simpl csteque_seq);
  (* Then when we have a packet and a following csteque. *)
  try (repeat apply div_app2;
  (* The following csteque is handled by the induction hypothesis. *)
  [clear_h | apply IHcs | clear_h];
  (* Proof by induction on the packet. *)
  induction pkt as [ | ?? Y' ? p pkt ? s];
  (* First handle the trivial cases when we have a [Hole]. *)
  try reflexivity;
  (* Depending on the case, destruct the prefix or suffix deque. *)
  [destruct p as [e1' e2' | e1' e2' e3' | e1' e2' e3' e4' [G Y c]] | 
   destruct s as [[G Y c]]];
  (* Format for simplification. *)
  cbn; autorewrite with rlist;
  (* Remove front element sequences in the prefix cases. *)
  repeat apply (f_equal (fun l => _ ++ l));
  (* Apply the induction hypothesis. *)
  try rewrite IHpkt;
  (* Solve simple cases Pre2 and Pre3. *)
  try reflexivity);
  (* Remove parts about packet in case Pre4. *)
  try apply (f_equal (fun l => l ++ _));
  (* Remove parts about packet in case Suff. *)
  try apply (f_equal (fun l => _ ++ l));
  (* Now we only need to proove things for cdeqs. *)
  clear_h;
  (* Handle cdeqs by induction. *)
  induction c as [?? b | ????? dpkt cd ? e cc];
  (* Format for simplification. *)
  cbn; autorewrite with rlist;
  (* We try to simplify Big pkt cs cases. *)
  try (repeat apply div_app2;
  (* Cases with cs can be prooved by induction. *)
  [clear_h | apply IHc | clear_h];
  (* For dpackets, we make a new induction. *)
  [induction dpkt as [ | ?? Y' ??? b dpkt ? sb] | 
   induction dpkt as [ | ?? Y' ??? pb dpkt ? b]];
  (* Hole cases are trivial. *)
  try reflexivity;
  (* Format for simplification. *)
  cbn; autorewrite with rlist;
  (* Dpackets parts are simplified by induction. *)
  rewrite IHdpkt;
  (* Remove dpackets in front cases. *)
  [apply (f_equal (fun l => l ++ _)) |
  (* Remove dpackets in rear cases. *) 
  apply (f_equal (fun l => _ ++ l))];
  (* Clear anything related to dpackets. *)
  clear_h);
  (* Now we only have simple buffer cases. *)
  destruct b;
  (* Format for simplification. *)
  cbn; autorewrite with rlist;
  (* Simple B0 cases are handled. *)
  try reflexivity;
  (* Destruct the multi-app goals into simpler subgoals. *)
  repeat apply div_app2;
  (* Clear the hypothesis. *)
  clear_h;
  (* We prove the remaining by induction on the right prodN elements. *)
  (match goal with 
  | _ : _ |- _ = concat (map element_seq (prodN_seq ?p)) => induction p
  end); 
  (* Finish the 900 goals with hauto. *)
  cbn; hauto db:rlist.
Qed.

(* element_seq is made opaque to prevent hauto from opening it when trying to
   solve Equations obligations. *)

Opaque element_seq.

(* So we add Selement_seq to rlist to handle the case element_seq (SElt p cs). *)

#[export] Hint Rewrite Selement_seq : rlist.

#[local] Obligation Tactic :=
  try first [ done | cbn beta; hauto db:rlist ].

(* The empty colored steque. *)

Equations cempty {A lvl} : { cs : csteque A lvl green | csteque_seq cs = [] } :=
cempty with deque.empty => {
    | ? d := ? Small (Suff d) }.

(* Functions *)

(* Takes a green prefix, a child and a suffix and returns the green steque 
   corresponding. *)

Equations make_green {A lvl C} 
    (p : prefix A lvl green)
    (cs : csteque A (S lvl) C)
    (s : suffix A lvl) :
    { cs' : csteque A lvl green | 
        csteque_seq cs' = prefix_seq p ++ csteque_seq cs ++ suffix_seq s } :=
make_green p (Small s') s := ? Big (Triple p Hole s) (Small s') eq_refl CCGreen;
make_green p (Big pkt cs' eq_refl CCGreen) s := 
    ? Big (Triple p Hole s) (Big pkt cs' eq_refl CCGreen) eq_refl CCGreen;
make_green p (Big pkt cs' eq_refl CCYellow) s :=
    ? Big (Triple p pkt s) cs' _ CCGreen;
make_green p (Big pkt cs' eq_refl CCOrange) s :=
    ? Big (Triple p pkt s) cs' _ CCGreen;
make_green p (Big pkt cs' eq_refl CCRed) s :=
    ? Big (Triple p Hole s) (Big pkt cs' eq_refl CCRed) eq_refl CCGreen.

(* Takes a yellow prefix, a child and a suffix and returns the yellow steque 
   corresponding. *) 

Equations make_yellow {A lvl G Y}
    (p : prefix A lvl yellow)
    (cs : csteque A (S lvl) (Mix G Y NoRed))
    (s : suffix A lvl) : 
    { cs' : csteque A lvl yellow | 
        csteque_seq cs' = prefix_seq p ++ csteque_seq cs ++ suffix_seq s } :=
make_yellow p (Small s') s := ? Big (Triple p Hole s) (Small s') eq_refl CCYellow;
make_yellow p (Big pkt cs' eq_refl CCGreen) s :=
    ? Big (Triple p Hole s) (Big pkt cs' eq_refl CCGreen) eq_refl CCYellow;
make_yellow p (Big pkt cs' eq_refl CCYellow) s :=
    ? Big (Triple p pkt s) cs' _ CCYellow.

(* Takes an orange prefix, a child and a suffix and returns the orange steque
   corresponding. *)

Equations make_orange {A lvl}
    (p : prefix A lvl yellow)
    (cs : any_csteque A (S lvl))
    (s : suffix A lvl) :
    { cs' : any_csteque A lvl | 
        any_csteque_seq cs' = prefix_seq p ++ any_csteque_seq cs ++ suffix_seq s } :=
make_orange p (Any_csteque (Small s')) s := 
    ? Any_csteque (Big (Triple p Hole s) (Small s') eq_refl CCYellow);
make_orange p (Any_csteque (Big pkt cs' eq_refl CCGreen)) s := 
    ? Any_csteque (Big (Triple p Hole s) (Big pkt cs' eq_refl CCGreen) eq_refl CCYellow);
make_orange p (Any_csteque (Big pkt cs' eq_refl CCYellow)) s :=
    ? Any_csteque (Big (Triple p pkt s) cs' _ CCYellow);
make_orange p (Any_csteque (Big pkt cs' eq_refl CCOrange)) s :=
    ? Any_csteque (Big (Triple p pkt s) cs' _ CCOrange);
make_orange p (Any_csteque (Big pkt cs' eq_refl CCRed)) s :=
    ? Any_csteque (Big (Triple p Hole s) (Big pkt cs' eq_refl CCRed) eq_refl CCOrange).

(* Takes a red prefix, a child and a suffix and returns the red steque 
   corresponding. *)

Equations make_red {A lvl G Y}
    (p : prefix A lvl red)
    (cs : csteque A (S lvl) (Mix G Y NoRed))
    (s : suffix A lvl) :
    { cs' : csteque A lvl red |
        csteque_seq cs' = prefix_seq p ++ csteque_seq cs ++ suffix_seq s } :=
make_red p (Small s') s := ? Big (Triple p Hole s) (Small s') eq_refl CCRed;
make_red p (Big pkt cs' eq_refl CCGreen) s :=
    ? Big (Triple p Hole s) (Big pkt cs' eq_refl CCGreen) eq_refl CCRed;
make_red p (Big pkt cs' eq_refl CCYellow) s := 
    ? Big (Triple p pkt s) cs' _ CCRed.

(* Pushes on a green prefix. *)

Equations green_prefix_push {A lvl} 
    (e : element A lvl)
    (p : prefix A lvl green) :
    { p' : prefix A lvl green | prefix_seq p' = element_seq e ++ prefix_seq p } :=
green_prefix_push e (Pre4 e1 e2 e3 e4 d) with deque.push e4 d => {
    | ? d' := ? Pre4 e e1 e2 e3 d' }.

(* Pushes on a yellow prefix. *)

Equations yellow_prefix_push {A lvl}
    (e : element A lvl)
    (p : prefix A lvl yellow) :
    { p' : prefix A lvl green | prefix_seq p' = element_seq e ++ prefix_seq p } :=
yellow_prefix_push e (Pre3 e1 e2 e3) with deque.empty => {
    | ? d := ? Pre4 e e1 e2 e3 d }.

(* Pushes on a red prefix. *)

Equations red_prefix_push {A lvl}
    (e : element A lvl)
    (p : prefix A lvl red) :
    { p' : prefix A lvl yellow | prefix_seq p' = element_seq e ++ prefix_seq p } :=
red_prefix_push e (Pre2 e1 e2) := ? Pre3 e e1 e2.

(* Pushes two elements on any prefix and returns a green one. *)

Equations prefix_push2 {A lvl C}
    (e1 e2 : element A lvl)
    (p : prefix A lvl C) :
    { p' : prefix A lvl green | 
        prefix_seq p' = element_seq e1 ++ element_seq e2 ++ prefix_seq p } :=
prefix_push2 e1 e2 (Pre2 e3 e4) with deque.empty => {
  | ? d := ? Pre4 e1 e2 e3 e4 d };
prefix_push2 e1 e2 (Pre3 e3 e4 e5) with deque.empty => {
  | ? d with deque.push e5 d => {
    | ? d1 := ? Pre4 e1 e2 e3 e4 d1 } };
prefix_push2 e1 e2 (Pre4 e3 e4 e5 e6 d) with deque.push e6 d => {
  | ? d1 with deque.push e5 d1 => {
    | ? d2 := ? Pre4 e1 e2 e3 e4 d2 } }.

(* Pushes on a colored steque and returns a green or yellow one. *)

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

(* Pushes on a steque of any color and returns a green or yellow one. *)

Equations any_push_gy {A lvl}
    (e : element A lvl)
    (cs : any_csteque A lvl) :
    { cs' : gy_csteque A lvl | 
        gy_csteque_seq cs' = element_seq e ++ any_csteque_seq cs } :=
any_push_gy e (Any_csteque cs) := push_gy e cs.

(* Pushes on a steque of any color and returns a steque of any color. *)

Equations any_push_any {A lvl}
    (e : element A lvl)
    (cs : any_csteque A lvl) :
    { cs' : any_csteque A lvl | 
        any_csteque_seq cs' = element_seq e ++ any_csteque_seq cs } :=
any_push_any e acs with any_push_gy e acs => {
    | ? GY_csteque cs' := ? Any_csteque cs' }.

(* Pushes on a green or yellow steque and returns a green or yellow one. *)

Equations gy_push_gy {A lvl}
    (e : element A lvl)
    (cs : gy_csteque A lvl) :
    { cs' : gy_csteque A lvl |
        gy_csteque_seq cs' = element_seq e ++ gy_csteque_seq cs } :=
gy_push_gy e (GY_csteque cs) := push_gy e cs.

(* Pushes on a steque. *)

Equations push {A} (a : A) (s : steque A) :
    { s' : steque A | steque_seq s' = [a] ++ steque_seq s } :=
push a (T cs) with gy_push_gy (ZElt a) (GY_csteque cs) => {
    | ? GY_csteque cs' := ? (T cs') }.

(* Injects on a colored steque and returns a colored steque of the same color. *)

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

(* Injects on a steque. *)

Equations inject {A} (s : steque A) (a : A) :
    { s' : steque A | steque_seq s' = steque_seq s ++ [a] } :=
inject (T cs) a with cinject cs (ZElt a) => {
    | ? cs' := ? T cs' }.

(* Converts two elements and a suffix to a prefix. *)

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

(* Takes a child steque, a suffix and a steque of any color, and returns a new
   child steque and steque of any color that contains the elements of the suffix
   in the right order. *)

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
      | ? Any_prefix p, ? cs with cinject child (SElt p cs) => {
        | ? child' := ? (child', cs2) } } } }.

(* Takes a packet and a green or red steque, and returns a steque of any color
   made of the packet followed by the argument steque. *)

Equations split_any {A lvl len nlvl G Y R} 
    (pkt : packet A lvl len (Mix NoGreen Y NoRed))
    (cs : csteque A nlvl (Mix G NoYellow R)) :
    nlvl = len + lvl ->
    { cs' : any_csteque A lvl | any_csteque_seq cs' = packet_front_seq pkt ++ 
                                                      csteque_seq cs ++ 
                                                      packet_rear_seq pkt } :=
split_any Hole cs eq_refl := ? Any_csteque cs;
split_any (Y := SomeYellow) (Triple p pkt s) (Small suff) eq_refl := 
  ? Any_csteque (Big (Triple p pkt s) (Small suff) eq_refl CCYellow);
split_any (Y := SomeYellow) (Triple p pkt s) (Big pkt' cs' eq_refl CCGreen) eq_refl := 
  ? Any_csteque (Big (Triple p pkt s) (Big pkt' cs' eq_refl CCGreen) eq_refl CCYellow);
split_any (Y := SomeYellow) (Triple p pkt s) (Big pkt' cs' eq_refl CCRed) eq_refl := 
  ? Any_csteque (Big (Triple p pkt s) (Big pkt' cs' eq_refl CCRed) eq_refl CCOrange).

(* Takes a packet and a green steque, and returns the green or yellow steque 
   made of the packet followed by the argument steque. *)

Equations split_gy {A lvl len nlvl Y} 
    (pkt : packet A lvl len (Mix NoGreen Y NoRed))
    (cs : csteque A nlvl green) :
    nlvl = len + lvl ->
    { cs' : gy_csteque A lvl | gy_csteque_seq cs' = packet_front_seq pkt ++ 
                                                    csteque_seq cs ++ 
                                                    packet_rear_seq pkt } :=
split_gy Hole cs eq_refl := ? GY_csteque cs;
split_gy (Y := SomeYellow) (Triple p pkt s) (Small suff) eq_refl := 
    ? GY_csteque (Big (Triple p pkt s) (Small suff) eq_refl CCYellow);
split_gy (Y := SomeYellow) (Triple p pkt s) (Big pkt' cs' eq_refl CCGreen) eq_refl := 
    ? GY_csteque (Big (Triple p pkt s) (Big pkt' cs' eq_refl CCGreen) eq_refl CCYellow).

(* Handles the first case of concatenation, when the first steque is a triple. 
   If [s] contains at least two elements, it is considered a prefix and can be 
   pushed in [child]. Otherwise, if [s] contains one elements, we push it on 
   [cs2]. If [cs2] is a triple, we inject its prefix and child in [child]. The 
   result of concat is then prefix(cs1) (not in the arguments), child and
   suffix(cs2). *)

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
        | ? Any_csteque child2' with cinject child' (SElt p' child2') => {
          | ? child'' := ? (child'', s') } };
      | Big (Triple p' pkt' s') cs' eq_refl CCYellow with split_any pkt' cs' _ => {
        | ? Any_csteque child2' with cinject child' (SElt p' child2') => {
          | ? child'' := ? (child'', s') } };
      | Big (Triple p' pkt' s') cs' eq_refl CCOrange with split_any pkt' cs' _ => {
        | ? Any_csteque child2' with cinject child' (SElt p' child2') => {
          | ? child'' := ? (child'', s') } };
      | Big (Triple p' pkt' s') cs' eq_refl CCRed with split_any pkt' cs' _ => {
        | ? Any_csteque child2' with cinject child' (SElt p' child2') => {
          | ? child'' := ? (child'', s') } } } }.

(* Takes a steque of any color and returns its partition form. *)

Equations partitioned {A lvl} (cs : any_csteque A lvl) :
    { p : partition A lvl | partition_seq p = any_csteque_seq cs } :=
partitioned (Any_csteque (Small s)) := ? PSmall s;
partitioned (Any_csteque (Big (Triple p Hole s) cs eq_refl _)) :=
    ? PBig p cs s;
partitioned (Any_csteque 
  (Big (Triple (Y := SomeYellow) p (Triple p' pkt s') s) 
    (Small suff) eq_refl CCGreen)) :=
      ? PBig p (Big (Triple p' pkt s') (Small suff) _ CCYellow) s;
partitioned (Any_csteque 
  (Big (Triple (Y := SomeYellow) p (Triple p' pkt s') s) 
    (Big pkt' cs' eq_refl CCGreen) eq_refl CCGreen)) :=
      ? PBig p (Big (Triple p' pkt s') (Big pkt' cs' eq_refl CCGreen) _ CCYellow) s;
partitioned (Any_csteque 
  (Big (Triple (Y := SomeYellow) p (Triple p' pkt s') s) 
    (Big pkt' cs' eq_refl CCRed) eq_refl CCGreen)) :=
      ? PBig p (Big (Triple p' pkt s') (Big pkt' cs' eq_refl CCRed) _ CCOrange) s;
partitioned (Any_csteque 
  (Big (Triple (Y := SomeYellow) p (Triple p' pkt s') s) cs eq_refl CCYellow)) :=
    ? PBig p (Big (Triple p' pkt s') cs _ CCYellow) s;
partitioned (Any_csteque 
  (Big (Triple (Y := SomeYellow) p (Triple p' pkt s') s) cs eq_refl CCOrange)) :=
    ? PBig p (Big (Triple p' pkt s') cs _ CCOrange) s;
partitioned (Any_csteque 
  (Big (Triple (Y := SomeYellow) p (Triple p' pkt s') s) cs eq_refl CCRed)) :=
    ? PBig p (Big (Triple p' pkt s') cs _ CCYellow) s.

(* Concatenates a colored steque and a steque of any color and returns a steque 
   of any color. *)

Equations concat_any {A lvl C}
    (cs1 : csteque A lvl C)
    (cs2 : any_csteque A lvl) :
    { cs3 : any_csteque A lvl | 
        any_csteque_seq cs3 = csteque_seq cs1 ++ any_csteque_seq cs2 } :=
concat_any (Small (Suff d)) cs2 with deque.pop d => {
  | ? None := ? cs2;
  | ? Some (w, d1) with deque.pop d1 => {
    | ? None with any_push_any w cs2 => { | ? cs3 := ? cs3 };
    | ? Some (x, d2) with deque.pop d2 => {
      | ? None with any_push_any x cs2 => {
        | ? cs3' with any_push_any w cs3' => { | ? cs3 := ? cs3 } };
      | ? Some (y, d3) with deque.pop d3 => {
        | ? None with any_push_any y cs2 => {
          | ? cs3'' with any_push_any x cs3'' => {
            | ? cs3' with any_push_any w cs3' => { | ? cs3 := ? cs3 } } };
        | ? Some (z, d4) with partitioned cs2, cempty => {
          | ? PSmall s2, ? cs := 
            ? Any_csteque 
              (Big (Triple (Pre4 w x y z d4) Hole s2) cs eq_refl CCGreen);
          | ? PBig p2 child2 s2, ? cs 
            with any_push_gy (SElt p2 cs) (Any_csteque child2) => {
              | ? GY_csteque child2' 
                with make_green (Pre4 w x y z d4) child2' s2 => {
                  | ? cs3 := ? Any_csteque cs3 } } } } } } };
concat_any (Big (Triple p pkt s) cs eq_refl CCGreen) cs2 
  with split_any pkt cs _ => {
    | ? Any_csteque child with join child s cs2 => {
      | ? (child', s') with make_green p child' s' => {
        | ? cs3 := ? Any_csteque cs3 } } };
concat_any (Big (Triple p pkt s) cs eq_refl CCYellow) cs2 
  with split_gy pkt cs _ => {
    | ? GY_csteque child with join child s cs2 => {
      | ? (child', s') with make_yellow p child' s' => {
        | ? cs3 := ? Any_csteque cs3 } } };
concat_any (Big (Triple p pkt s) cs eq_refl CCOrange) cs2 
  with split_any pkt cs _ => {
    | ? Any_csteque child with join child s cs2 => {
      | ? (child', s') with make_orange p (Any_csteque child') s' => {
        | ? cs3 := ? cs3 } } };
concat_any (Big (Triple p pkt s) cs eq_refl CCRed) cs2 
  with split_gy pkt cs _ => {
    | ? GY_csteque child with join child s cs2 => {
      | ? (child', s') with make_red p child' s' => {
        | ? cs3 := ? Any_csteque cs3 } } }.

(* Concatenates two steques. *)

Equations concat {A} (s1 : steque A) (s2 : steque A) :
    { s3 : steque A | steque_seq s3 = steque_seq s1 ++ steque_seq s2 } :=
concat (T (Small (Suff d))) (T cs2) with deque.pop d => {
  | ? None := ? T cs2;
  | ? Some (w, d1) with deque.pop d1 => {
    | ? None with gy_push_gy w (GY_csteque cs2) => { 
      | ? GY_csteque cs3 := ? T cs3 };
    | ? Some (x, d2) with deque.pop d2 => {
      | ? None with gy_push_gy x (GY_csteque cs2) => {
        | ? cs3' with gy_push_gy w cs3' => { 
          | ? GY_csteque cs3 := ? T cs3 } };
      | ? Some (y, d3) with deque.pop d3 => {
        | ? None with gy_push_gy y (GY_csteque cs2) => {
          | ? cs3'' with gy_push_gy x cs3'' => {
            | ? cs3' with gy_push_gy w cs3' => { 
              | ? GY_csteque cs3 := ? T cs3 } } };
        | ? Some (z, d4) with partitioned (Any_csteque cs2), cempty => {
          | ? PSmall s2, ? cs := 
            ? T (Big (Triple (Pre4 w x y z d4) Hole s2) cs eq_refl CCGreen);
          | ? PBig p2 child2 s2, ? cs 
            with any_push_gy (SElt p2 cs) (Any_csteque child2) => {
              | ? GY_csteque child2' 
                with make_green (Pre4 w x y z d4) child2' s2 => {
                  | ? cs3 := ? T cs3 } } } } } } };
concat (T (Big (Triple p pkt s) cs eq_refl CCGreen)) (T cs2) 
  with split_any pkt cs _ => {
    | ? Any_csteque child with join child s (Any_csteque cs2) => {
      | ? (child', s') with make_green p child' s' => {
        | ? cs3 := ? T cs3 } } };
concat (T (Big (Triple p pkt s) cs eq_refl CCYellow)) (T cs2) 
  with split_gy pkt cs _ => {
    | ? GY_csteque child with join child s (Any_csteque cs2) => {
      | ? (child', s') with make_yellow p child' s' => {
        | ? cs3 := ? T cs3 } } }.

(* Pops from a green prefix. *)

Equations green_prefix_pop {A lvl} (p : prefix A lvl green) :
    { '(e, p') : element A lvl * gy_prefix A lvl | 
        element_seq e ++ gy_prefix_seq p' = prefix_seq p } := 
green_prefix_pop (Pre4 e1 e2 e3 e4 ded) with deque.pop ded => {
  | ? None := ? (e1, GY_prefix (Pre3 e2 e3 e4));
  | ? Some (e5, deque') := ? (e1, GY_prefix (Pre4 e2 e3 e4 e5 deque')) }.

(* Pops from a yellow prefix. *)

Equations yellow_prefix_pop {A lvl Y} (p : prefix A lvl (Mix NoGreen Y NoRed)) :
    { '(e, p') : element A lvl * prefix A lvl red | 
        element_seq e ++ prefix_seq p' = prefix_seq p } :=
yellow_prefix_pop (Pre3 e1 e2 e3) := ? (e1, Pre2 e2 e3).

(* Takes a red steque and returns its green version. *)

Equations green_of_red {A lvl} (cs : csteque A lvl red) :
    { cs' : csteque A lvl green | csteque_seq cs' = csteque_seq cs } :=
green_of_red 
  (Big (Triple (Pre2 e1 e2) Hole (Suff s)) (Small (Suff child)) eq_refl CCRed) 
    with deque.pop child => {
      | ? None with deque.push e2 s => {
        | ? s1 with deque.push e1 s1 => {
          | ? s2 := ? Small (Suff s2) } };
      | ? Some (SElt p cs2, child1) with prefix_push2 e1 e2 p => {
        | ? p1 with concat_any cs2 (Any_csteque (Small (Suff child1))) => {
            | ? Any_csteque child' with make_green p1 child' (Suff s) => {
              | ? cs := ? cs } } } }; 
green_of_red (Big (Triple (Pre2 e1 e2) Hole (Suff s1)) 
  (Big (Triple p child s) cs eq_refl CCGreen) eq_refl CCRed) 
    with green_prefix_pop p => {
      | ? (SElt pref rest, GY_prefix p1) with prefix_push2 e1 e2 pref => {
        | ? pref1 with p1 => {
          | Pre4 a b c d deque
            with concat_any rest (Any_csteque 
              (Big (Triple (Pre4 a b c d deque) child s) cs _ CCGreen)) => {
                | ? Any_csteque child1 
                  with make_green pref1 child1 (Suff s1) => {
                    | ? cs' := ? cs' } };
          | Pre3 a b c with split_any (Triple (Pre3 a b c) child s) cs _ => {
            | ? child1 with concat_any rest child1 => {
              | ? Any_csteque child2 with make_green pref1 child2 (Suff s1) => {
                | ? cs' := ? cs' } } } } } };
green_of_red (Big (Triple (Pre2 e1 e2) (Triple p child s) s1) cs eq_refl CCRed) 
  with yellow_prefix_pop p => {
    | ? (SElt pref rest, p1) with prefix_push2 e1 e2 pref => {
      | ? pref1 with concat_any rest (Any_csteque 
        (Big (Triple p1 child s) cs _ CCRed)) => {
          | ? Any_csteque child1 with make_green pref1 child1 s1 => {
            | ? cs' := ? cs' } } } }.

(* Takes a green or red steque and returns its green version. *)

Equations ensure_green {A lvl G R} (cs : csteque A lvl (Mix G NoYellow R)) :
    { cs' : csteque A lvl green | csteque_seq cs' = csteque_seq cs } :=
ensure_green (Small s) := ? Small s;
ensure_green (Big pkt cs eq_refl CCGreen) := ? Big pkt cs eq_refl CCGreen;
ensure_green (Big pkt cs eq_refl CCRed) 
  with green_of_red (Big pkt cs eq_refl CCRed) => {
    | ? cs' := ? cs' }.

(* Pops from a steque. *)

Equations pop {A} (s : steque A) : 
    { o : option (A * steque A) | 
        steque_seq s = match o with 
            | None => []
            | Some (a, s') => [a] ++ steque_seq s' end } :=
pop (T (Small (Suff d))) with deque.pop d => {
  | ? None := ? None;
  | ? Some (ZElt a, d') := ? Some (a, T (Small (Suff d'))) };
pop (T (Big (Triple p child s) cs eq_refl CCGreen)) with green_prefix_pop p => {
  | ? (ZElt a, GY_prefix p') with p' => {
    | Pre3 b c d with ensure_green cs => {
      | ? cs' := 
        ? Some (a, T (Big (Triple (Pre3 b c d) child s) cs' eq_refl CCYellow)) };
    | Pre4 b c d e deque := 
      ? Some (a, T (Big (Triple (Pre4 b c d e deque) child s) cs eq_refl CCGreen)) } };
pop (T (Big (Triple p child s) cs eq_refl CCYellow)) with yellow_prefix_pop p => {
  | ? (ZElt a, p') with green_of_red (Big (Triple p' child s) cs eq_refl CCRed) => {
    | ? cs' := ? Some (a, T cs') } }.
