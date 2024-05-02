From Coq Require Import ssreflect.
From Coq Require Import Program List ZArith Lia.
Import ListNotations.
From Equations Require Import Equations.
From Hammer Require Import Tactics.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

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
Notation red := (Mix NoGreen NoYellow SomeRed).
Notation uncolored := (Mix NoGreen NoYellow NoRed).

(* A type for iterated products. *)

Inductive prodN (A : Type) : nat -> Type := 
  | prodZ : A -> prodN A 0 
  | prodS {n : nat} : prodN A n * prodN A n -> prodN A (S n).
Arguments prodZ {A}.
Arguments prodS {A n}.

(* A type for buffers. *)

Inductive buffer (A : Type) (lvl : nat) : color -> Type :=
  | B0       : buffer A lvl red
  | B1       : prodN A lvl -> buffer A lvl yellow
  | B2 {G Y} : prodN A lvl -> prodN A lvl -> buffer A lvl (Mix G Y NoRed)
  | B3 {G Y} : prodN A lvl -> prodN A lvl -> prodN A lvl -> buffer A lvl (Mix G Y NoRed)
  | B4       : prodN A lvl -> prodN A lvl -> prodN A lvl -> prodN A lvl -> buffer A lvl yellow
  | B5       : prodN A lvl -> prodN A lvl -> prodN A lvl -> prodN A lvl -> prodN A lvl -> buffer A lvl red.
Arguments B1 {A lvl}.
Arguments B0 {A lvl}.
Arguments B2 {A lvl G Y}.
Arguments B3 {A lvl G Y}.
Arguments B4 {A lvl}.
Arguments B5 {A lvl}.

(* A type for yellow buffers. *)

Inductive yellow_buffer (A: Type) (lvl : nat) : Type :=
  | Yellowish : forall {G Y},
  buffer A lvl (Mix G Y NoRed) ->
  yellow_buffer A lvl.
Arguments Yellowish {A lvl G Y}.

(* A type for any buffers. *)

Inductive any_buffer (A: Type) (lvl : nat) : Type :=
  | Any : forall {C}, buffer A lvl C -> any_buffer A lvl.
Arguments Any {A lvl C}.

(* A relation for colors appearing at a triple of packet. *)

Inductive packet_color : color -> color -> color -> Type := 
  | PCGreen : packet_color green green green
  | PCYellow {G1 Y1 G2 Y2} : packet_color (Mix G1 Y1 NoRed) (Mix G2 Y2 NoRed) yellow 
  | PCRed {C1 C2 : color} : packet_color C1 C2 red.

(* A type for leveled packet. *)

Inductive lvl_packet (A : Type) (lvl : nat) : nat -> color -> Type :=
  | Hole : lvl_packet A lvl 0 uncolored
  | Triple {len : nat} {Y : yellow_hue} {C1 C2 C3 : color} :
      buffer A lvl C1 ->
      lvl_packet A (S lvl) len (Mix NoGreen Y NoRed) ->
      buffer A lvl C2 ->
      packet_color C1 C2 C3 ->
      lvl_packet A lvl (S len) C3.
Arguments Hole {A lvl}.
Arguments Triple {A lvl len Y C1 C2 C3}.

(* A type for packet. *)

Definition packet A := lvl_packet A 0.

(* A relation for colors appearing in a big colored deque. *)

Inductive cdeque_color : color -> color -> Type := 
  | CCGreen {G R} : cdeque_color green (Mix G NoYellow R)
  | CCYellow : cdeque_color yellow green 
  | CCRed : cdeque_color red green.

(* A type for leveled colored deque. *)

Inductive lvl_cdeque (A : Type) (lvl : nat) : color -> Type :=
  | Small {C : color} : 
      buffer A lvl C -> 
      lvl_cdeque A lvl green
  | Big {len : nat} {C1 C2 : color} :
      lvl_packet A lvl len C1 -> 
      lvl_cdeque A (len + lvl) C2 -> 
      cdeque_color C1 C2 ->
      lvl_cdeque A lvl C1.
Arguments Small {A lvl C}.
Arguments Big {A lvl len C1 C2}.

(* A type for colored deque. *)

Definition cdeque (A : Type) := lvl_cdeque A 0.

(* The decompose type. *)

Inductive decompose (A : Type) (lvl : nat) : Type :=
| Underflow : option (prodN A lvl) -> decompose A lvl
| Ok : buffer A lvl green -> decompose A lvl
| Overflow : buffer A lvl green -> prodN A (S lvl) -> decompose A lvl.

Arguments Underflow {_ _}.
Arguments Ok {_ _}.
Arguments Overflow {_ _}.

(* The sandwich type. *)

Inductive sandwich (A : Type) (lvl : nat) : Type :=
| Alone : option (prodN A lvl) -> sandwich A lvl
| Sandwich {C} : prodN A lvl -> buffer A lvl C -> prodN A lvl -> sandwich A lvl.
Arguments Alone {A lvl}.
Arguments Sandwich {A lvl C}.

(* The not_yellow trait for colors. *)

Inductive not_yellow : color -> Type :=
| Not_yellow {G R} : not_yellow (Mix G NoYellow R).

(* A type for deque. *)

Inductive deque (A : Type) : Type := 
  T : forall (G : green_hue) (Y : yellow_hue), 
      cdeque A (Mix G Y NoRed) -> 
      deque A.
Arguments T {A G Y}.

(* Models *)

Set Equations Transparent.

(* The lemma [app_cons_one] is trivial but it is mandatory as ++ is later made
   opaque. *)

Lemma app_cons_one [A : Type] (a : A) (l : list A) : a :: l = [a] ++ l.
Proof.
  reflexivity.
Qed.

Opaque app.
Definition singleton {A : Type} (x : A) : list A := [x].
Opaque singleton.

(* Transforms a list of pairs into a list, preserving the order. *)

Equations flattenp {A n} (l : list (prodN A (S n))) : list (prodN A n) := 
flattenp [] := [];
flattenp (prodS (x, y) :: l) := [x] ++ [y] ++ flattenp l.

(* A simple lemma to prove the distributivity of flattenp over concatenation 
   of lists. *)

Require Import Coq.Program.Equality.

Lemma flattenp_app A n (l1 l2 : list (prodN A (S n))) : flattenp (l1 ++ l2) = flattenp l1 ++ flattenp l2.
Proof. 
  induction l1 as [ | p l].
  - eauto.
  - dependent destruction p; destruct p as [x y].
    rewrite <- app_comm_cons; cbn.
    rewrite IHl.
    aac_reflexivity.
Qed.

(* A list of tactics to be used when trying to resolve obligations generated by
   Equations. *)

#[export] Hint Rewrite <-app_assoc : rlist.
#[export] Hint Rewrite <-app_comm_cons : rlist.
#[export] Hint Rewrite flattenp_app : rlist.
#[export] Hint Rewrite app_nil_r : rlist.
#[export] Hint Rewrite compose_id_left : rlist.
#[export] Hint Rewrite map_app : rlist.

#[local] Obligation Tactic :=
  try first [ done | hauto db:rlist ].

(* Get a list from a pair. *)

Equations prodN_Sn_seq {A n} : prodN A (S n) -> list (prodN A n) := 
prodN_Sn_seq (prodS (a, b)) := [a] ++ [b].

(* Get a list from an option. *)

Equations option_seq {A} : option A -> list A :=
option_seq None := [];
option_seq (Some x) := [x].

(* Get a list from a buffer. *)

Equations buffer_seq {A lvl C} : buffer A lvl C -> list (prodN A lvl) :=
buffer_seq B0 := [];
buffer_seq (B1 a) := [a];
buffer_seq (B2 a b) := [a] ++ [b];
buffer_seq (B3 a b c) := [a] ++ [b] ++ [c];
buffer_seq (B4 a b c d) := [a] ++ [b] ++ [c] ++ [d];
buffer_seq (B5 a b c d e) := [a] ++ [b] ++ [c] ++ [d] ++ [e].

(* Get a list from a yellow buffer. *)

Equations yellow_buffer_seq {A lvl} : yellow_buffer A lvl -> list (prodN A lvl) :=
yellow_buffer_seq (Yellowish buf) := buffer_seq buf.

(* Get a list from any buffer. *)

Equations any_buffer_seq {A lvl} : any_buffer A lvl -> list (prodN A lvl) :=
any_buffer_seq (Any buf) := buffer_seq buf.

(* Get the list corresponding to elements stored in prefix buffers along a 
   packet. *)

Equations packet_front_seq {A lvl len C} : lvl_packet A lvl len C -> list (prodN A lvl) :=
packet_front_seq Hole := [];
packet_front_seq (Triple buf1 p _ _) := 
  buffer_seq buf1 ++ flattenp (packet_front_seq p).

(* Get the list corresponding to elements stored in suffix buffers along a 
   packet. *)

Equations packet_rear_seq {A lvl len C} : lvl_packet A lvl len C -> list (prodN A lvl) :=
packet_rear_seq Hole := [];
packet_rear_seq (Triple _ p buf2 _) := 
  flattenp (packet_rear_seq p) ++ buffer_seq buf2.

(* Constructs the function transforming a list B into a list A, given a packet
   A B _ _. It uses the induction relation of packets' Constructors to deduct 
   the right relation between A and B. *)

Equations flattenp_plus_m {A n} (m : nat) : list (prodN A (m + n)) -> list (prodN A n) := 
flattenp_plus_m 0 := id;
flattenp_plus_m (S m) := (flattenp_plus_m m) ∘ flattenp.
Arguments flattenp_plus_m {A n m}.

(* Get the list represented by a leveled colored deque. *)

Equations cdeque_seq {A lvl C} : lvl_cdeque A lvl C -> list (prodN A lvl) :=
cdeque_seq (Small buf) := buffer_seq buf;
cdeque_seq (Big p cd _) := 
    packet_front_seq p ++
    flattenp_plus_m (cdeque_seq cd) ++
    packet_rear_seq p.

(* Get the list of non-excess elements of an object of type decompose. *)

Equations decompose_main_seq {A lvl} (dec : decompose A lvl) : list (prodN A lvl) :=
decompose_main_seq (Underflow opt) := option_seq opt;
decompose_main_seq (Ok b) := buffer_seq b;
decompose_main_seq (Overflow b _) := buffer_seq b.

(* Get the list of excess elements of an object of type decompose. *)

Equations decompose_rest_seq {A lvl} (dec : decompose A lvl) : list (prodN A lvl) :=
decompose_rest_seq (Underflow _) := [];
decompose_rest_seq (Ok _) := [];
decompose_rest_seq (Overflow _ (prodS (x, y))) := [x] ++ [y].

(* Get the list of elements of an object of type sandwich. *)

Equations sandwich_seq {A lvl} (sw : sandwich A lvl) : list (prodN A lvl) :=
sandwich_seq (Alone opt) := option_seq opt;
sandwich_seq (Sandwich x b y) := [x] ++ buffer_seq b ++ [y].

Lemma prodN_0 {A} : prodN A 0 -> A.
Proof. intro p. dependent destruction p. assumption. Defined.

(* Get the list represented by a deque. *)

Equations deque_seq {A} : deque A -> list A :=
deque_seq (T dq) := map prodN_0 (cdeque_seq dq).

Unset Equations Transparent.

(* Functions *)

Notation "? x" := (@exist _ _ x _) (at level 100).

(* Pushing on a green buffer. *)

Equations green_push {A lvl} (x : prodN A lvl) (b : buffer A lvl green) :
  { b' : buffer A lvl yellow | buffer_seq b' = [x] ++ buffer_seq b } :=
green_push x (B2 a b) := ? B3 x a b;
green_push x (B3 a b c) := ? B4 x a b c.

(* Injecting on a green buffer. *)

Equations green_inject {A lvl} (b : buffer A lvl green) (x : prodN A lvl) :
  { b' : buffer A lvl yellow | buffer_seq b' = buffer_seq b ++ [x] } :=
green_inject (B2 a b) x := ? B3 a b x;
green_inject (B3 a b c) x := ? B4 a b c x.

(* Poping from a green buffer. *)

Equations green_pop {A lvl} (b : buffer A lvl green) :
  { '(x, b') : prodN A lvl * yellow_buffer A lvl | buffer_seq b = [x] ++ yellow_buffer_seq b' } :=
green_pop (B2 a b) => ? (a, (Yellowish (B1 b)));
green_pop (B3 a b c) => ? (a, (Yellowish (B2 b c))).

(* Ejecting from a green buffer. *)

Equations green_eject {A lvl} (b : buffer A lvl green) :
  { '(b', x) : yellow_buffer A lvl * prodN A lvl | buffer_seq b = yellow_buffer_seq b' ++ [x] } :=
green_eject (B2 a b) => ? ((Yellowish (B1 a)), b);
green_eject (B3 a b c) => ? ((Yellowish (B2 a b)), c).

(* Pushing on a yellow buffer. *)

#[derive(eliminator=no)]
Equations yellow_push {A lvl} (x : prodN A lvl) (b : yellow_buffer A lvl) :
  { b' : any_buffer A lvl | any_buffer_seq b' = [x] ++ yellow_buffer_seq b } :=
yellow_push x (Yellowish buf) with buf => {
  | B1 a => ? Any (B2 x a);
  | B2 a b => ? Any (B3 x a b);
  | B3 a b c => ? Any (B4 x a b c);
  | B4 a b c d => ? Any (B5 x a b c d)
}.

(* Injecting on a yellow buffer. *)

#[derive(eliminator=no)]
Equations yellow_inject {A lvl} (b : yellow_buffer A lvl) (x : prodN A lvl) :
  { b' : any_buffer A lvl | any_buffer_seq b' = yellow_buffer_seq b ++ [x] } :=
yellow_inject (Yellowish buf) x with buf := {
  | B1 a => ? Any (B2 a x);
  | B2 a b => ? Any (B3 a b x);
  | B3 a b c => ? Any (B4 a b c x);
  | B4 a b c d => ? Any (B5 a b c d x)
}.

(* Poping from a yellow buffer. *)

#[derive(eliminator=no)]
Equations yellow_pop {A lvl} (b : yellow_buffer A lvl) :
  { '(x, b') : prodN A lvl * any_buffer A lvl | yellow_buffer_seq b = [x] ++ any_buffer_seq b' } :=
yellow_pop (Yellowish buf) with buf => {
  | B1 a => ? (a, Any B0);
  | B2 a b => ? (a, Any (B1 b));
  | B3 a b c => ? (a, Any (B2 b c));
  | B4 a b c d => ? (a, Any (B3 b c d))
}.

(* Ejecting from a yellow buffer. *)

#[derive(eliminator=no)]
Equations yellow_eject {A lvl} (b : yellow_buffer A lvl) :
  { '(b', x) : any_buffer A lvl * prodN A lvl | yellow_buffer_seq b = any_buffer_seq b' ++ [x] } :=
yellow_eject (Yellowish buf) with buf => {
  | B1 a => ? (Any B0, a);
  | B2 a b => ? (Any (B1 a), b);
  | B3 a b c => ? (Any (B2 a b), c);
  | B4 a b c d => ? (Any (B3 a b c), d)
}.

(* Pushing on a buffer. *)

Equations buffer_push {A lvl C} (x : prodN A lvl) (b : buffer A lvl C) :
  { cd : lvl_cdeque A lvl green | cdeque_seq cd = [x] ++ buffer_seq b } :=
buffer_push x B0 := ? Small (B1 x);
buffer_push x (B1 a) := ? Small (B2 x a);
buffer_push x (B2 a b) := ? Small (B3 x a b);
buffer_push x (B3 a b c) := ? Small (B4 x a b c);
buffer_push x (B4 a b c d) := ? Small (B5 x a b c d);
buffer_push x (B5 a b c d e) := 
    ? Big (Triple (B3 x a b) Hole (B3 c d e) PCGreen) (Small B0) CCGreen. 

(* Injecting on a buffer. *)

Equations buffer_inject {A lvl C} (b : buffer A lvl C) (x : prodN A lvl) :
  { cd : lvl_cdeque A lvl green | cdeque_seq cd = buffer_seq b ++ [x] } :=
buffer_inject B0 x := ? Small (B1 x);
buffer_inject (B1 a) x := ? Small (B2 a x);
buffer_inject (B2 a b) x := ? Small (B3 a b x);
buffer_inject (B3 a b c) x := ? Small (B4 a b c x);
buffer_inject (B4 a b c d) x := ? Small (B5 a b c d x);
buffer_inject (B5 a b c d e) x := 
    ? Big (Triple (B3 a b c) Hole (B3 d e x) PCGreen)(Small B0) _.

(* Poping from a buffer. *)
  
Equations buffer_pop {A lvl C} (b : buffer A lvl C) :
  { o : option (prodN A lvl * any_buffer A lvl) |
    buffer_seq b =
    match o with
    | None => []
    | Some (x, b') => [x] ++ any_buffer_seq b'
    end } :=
buffer_pop B0 := ? None;
buffer_pop (B5 a b c d e) := ? Some (a, Any (B4 b c d e));
buffer_pop buf with yellow_pop (Yellowish buf) => { | ? o := ? Some o }.

(* Ejecting from a buffer. *)

Equations buffer_eject {A lvl C} (b : buffer A lvl C) :
  { o : option (any_buffer A lvl * prodN A lvl) |
    buffer_seq b =
    match o with
    | None => []
    | Some (b', x) => any_buffer_seq b' ++ [x]
    end } :=
buffer_eject (B5 a b c d e) := ? Some (Any (B4 a b c d), e);
buffer_eject B0 := ? None;
buffer_eject buf with yellow_eject (Yellowish buf) => { | ? o := ? Some o }.

(* Pushes then ejects. *)

Equations prefix_rot {A lvl C} (x : prodN A lvl) (b : buffer A lvl C) :
  { '(b', y) : buffer A lvl C * prodN A lvl | [x] ++ buffer_seq b = buffer_seq b' ++ [y] } :=
prefix_rot x B0 := ? (B0, x);
prefix_rot x (B1 a) := ? (B1 x, a);
prefix_rot x (B2 a b) := ? (B2 x a, b);
prefix_rot x (B3 a b c) := ? (B3 x a b, c);
prefix_rot x (B4 a b c d) := ? (B4 x a b c, d);
prefix_rot x (B5 a b c d e) := ? (B5 x a b c d, e).

(* Injects then pops. *)

Equations suffix_rot {A lvl C} (b : buffer A lvl C) (y : prodN A lvl) :
  { '(x, b') : prodN A lvl * buffer A lvl C | buffer_seq b ++ [y] = [x] ++ buffer_seq b' } :=
suffix_rot B0 x := ? (x, B0);
suffix_rot (B1 a) x := ? (a, B1 x);
suffix_rot (B2 a b) x := ? (a, B2 b x);
suffix_rot (B3 a b c) x := ? (a, B3 b c x);
suffix_rot (B4 a b c d) x := ? (a, B4 b c d x);
suffix_rot (B5 a b c d e) x := ? (a, B5 b c d e x).

(* Create a green buffer by injecting a pair onto an option. *)

Equations prefix23 {A lvl G Y} (o : option (prodN A lvl)) (p: prodN A (S lvl)) :
  { b : buffer A lvl (Mix G Y NoRed) |
    buffer_seq b = option_seq o ++ prodN_Sn_seq p } :=
prefix23 None (prodS (b, c)) := ? B2 b c;
prefix23 (Some a) (prodS (b, c)) := ? B3 a b c.

(* Create a green buffer by poping a pair onto an option. *)

Equations suffix23 {A lvl G Y} (p : prodN A (S lvl)) (o : option (prodN A lvl)) :
  { b : buffer A lvl (Mix G Y NoRed) |
    buffer_seq b = prodN_Sn_seq p ++ option_seq o } :=
suffix23 (prodS (a, b)) None := ? B2 a b;
suffix23 (prodS (a, b)) (Some c) := ? B3 a b c.

(* Create a yellow (or green) buffer by pushing an element onto an option. *)

Equations suffix12 {A lvl} (x : prodN A lvl) (o : option (prodN A lvl)) :
  { b : buffer A lvl yellow | buffer_seq b = [x] ++ option_seq o } :=
suffix12 x None := ? B1 x;
suffix12 x (Some y) := ? B2 x y.

(* Returns the decomposed version of a buffer. Here, it is a prefix 
   decomposition: when the buffer is overflowed, elements at the end are 
   removed. *)

Equations prefix_decompose {A lvl C} (b : buffer A lvl C) :
  { dec : decompose A lvl | buffer_seq b = decompose_main_seq dec ++ decompose_rest_seq dec } :=
prefix_decompose B0 := ? Underflow None;
prefix_decompose (B1 x) := ? Underflow (Some x);
prefix_decompose (B2 a b) := ? Ok (B2 a b);
prefix_decompose (B3 a b c) := ? Ok (B3 a b c);
prefix_decompose (B4 a b c d) := ? Overflow (B2 a b) (prodS (c, d));
prefix_decompose (B5 a b c d e) := ? Overflow (B3 a b c) (prodS (d, e)).

(* Returns the decomposed version of a buffer. Here, it is a suffix
   decomposition: when the buffer is overflowed, elements at the beginning are
   removed. *)

Equations suffix_decompose {A lvl C} (b : buffer A lvl C) :
  { dec : decompose A lvl | buffer_seq b = decompose_rest_seq dec ++ decompose_main_seq dec } :=
suffix_decompose B0 := ? Underflow None;
suffix_decompose (B1 x) := ? Underflow (Some x);
suffix_decompose (B2 a b) := ? Ok (B2 a b);
suffix_decompose (B3 a b c) := ? Ok (B3 a b c);
suffix_decompose (B4 a b c d) := ? Overflow (B2 c d) (prodS (a, b));
suffix_decompose (B5 a b c d e) := ? Overflow (B3 c d e) (prodS (a, b)).

(* Returns the sandwich representation of a buffer. *)

Equations buffer_unsandwich {A lvl C} (b : buffer A lvl C) :
  { sw : sandwich A lvl | buffer_seq b = sandwich_seq sw } :=
buffer_unsandwich B0 := ? Alone None;
buffer_unsandwich (B1 a) := ? Alone (Some a);
buffer_unsandwich (B2 a b) := ? Sandwich a B0 b;
buffer_unsandwich (B3 a b c) := ? Sandwich a (B1 b) c;
buffer_unsandwich (B4 a b c d) := ? Sandwich a (B2 b c) d;
buffer_unsandwich (B5 a b c d e) := ? Sandwich a (B3 b c d) e.

(* Translates a buffer to a pairs buffer. A additional option type is returned 
   to handle cases where the buffer contains an odd number of elements. *)

Equations buffer_halve {A lvl C} (b : buffer A lvl C) :
  { '(o, b') : option (prodN A lvl) * any_buffer A (S lvl) |
    buffer_seq b = option_seq o ++ flattenp (any_buffer_seq b') } :=
buffer_halve B0 := ? (None, Any B0);
buffer_halve (B1 a) := ? (Some a, Any B0);
buffer_halve (B2 a b) := ? (None, Any (B1 (prodS (a, b))));
buffer_halve (B3 a b c) := ? (Some a, Any (B1 (prodS (b, c))));
buffer_halve (B4 a b c d) := ? (None, Any (B2 (prodS (a, b)) (prodS (c, d))));
buffer_halve (B5 a b c d e) := ? (Some a, Any (B2 (prodS (b, c)) (prodS (d, e)))).

(* Takes any buffer and a pairs green one, and rearranges elements contained in 
   the two buffers to return one green buffer and a pairs yellow buffer. The 
   order of elements is preserved. *)

Equations green_prefix_concat {A lvl C}
  (buf1 : buffer A lvl C)
  (buf2 : buffer A (S lvl) green) :
  { '(buf1', buf2') : buffer A lvl green * yellow_buffer A (S lvl) |
    buffer_seq buf1 ++ flattenp (buffer_seq buf2) =
    buffer_seq buf1' ++ flattenp (yellow_buffer_seq buf2') } :=
green_prefix_concat buf1 buf2 with prefix_decompose buf1 => {
  | (? Ok buf) => ? (buf, Yellowish buf2);
  | (? Underflow opt) with green_pop buf2 => {
    | (? (ab, buf)) =>
        let '(? prefix) := prefix23 opt ab in
        ? (prefix, buf) };
  | (? Overflow buf ab) =>
    let '(? suffix) := green_push ab buf2 in
    ? (buf, Yellowish suffix)
}.

(* Takes a pairs green buffer and any one, and rearranges elements contained in 
   the two buffers to return one pairs yellow buffer and one green buffer. The 
   order of elements is preserved. *)

Equations green_suffix_concat {A lvl C}
  (buf1 : buffer A (S lvl) green)
  (buf2 : buffer A lvl C) :
  { '(buf1', buf2') : yellow_buffer A (S lvl) * buffer A lvl green |
    flattenp (buffer_seq buf1) ++ buffer_seq buf2 =
    flattenp (yellow_buffer_seq buf1') ++ buffer_seq buf2' } :=
green_suffix_concat buf1 buf2 with suffix_decompose buf2 => {
  | ? Ok buf => ? (Yellowish buf1, buf);
  | ? Underflow opt with green_eject buf1 => {
    | ? (buf, ab) =>
        let '(? suffix) := suffix23 ab opt in
        ? (buf, suffix) };
  | ? Overflow buf ab =>
    let '(? prefix) := green_inject buf1 ab in
    ? (Yellowish prefix, buf)
}.

(* Takes any buffer and a pairs yellow one, and rearranges elements contained 
   in the two buffers to return one green buffer and any pairs buffer. The 
   order of elements is preserved. *)

Equations yellow_prefix_concat {A lvl C}
  (buf1 : buffer A lvl C)
  (buf2 : yellow_buffer A (S lvl)) :
  { '(buf1', buf2') : buffer A lvl green * any_buffer A (S lvl) |
    buffer_seq buf1 ++ flattenp (yellow_buffer_seq buf2) =
    buffer_seq buf1' ++ flattenp (any_buffer_seq buf2') } :=
yellow_prefix_concat buf1 buf2 with prefix_decompose buf1 => {
  | ? (Ok buf) =>
    let '(Yellowish buf2) := buf2 in
    ? (buf, Any buf2);
  | ? (Underflow opt) with yellow_pop buf2 => {
    | ? (ab, buf) =>
      let '(? prefix) := prefix23 opt ab in
      ? (prefix, buf) };
  | ? (Overflow buf ab) =>
    let '(? suffix) := yellow_push ab buf2 in
    ? (buf, suffix)
}.

(* Takes a pairs yellow buffer and any one, and rearranges elements contained 
   in the two buffers to return any pairs buffer and one green buffer. The 
   order of elements is preserved. *)

Equations yellow_suffix_concat {A lvl C}
  (buf1 : yellow_buffer A (S lvl))
  (buf2 : buffer A lvl C) :
  { '(buf1', buf2') : any_buffer A (S lvl) * buffer A lvl green |
    flattenp (yellow_buffer_seq buf1) ++ buffer_seq buf2 =
    flattenp (any_buffer_seq buf1') ++ buffer_seq buf2' } :=
yellow_suffix_concat buf1 buf2 with suffix_decompose buf2 => {
  | ? (Ok buf) =>
    let '(Yellowish buf1) := buf1 in
    ? (Any buf1, buf);
  | ? (Underflow opt) with yellow_eject buf1 => {
    | ? (buf, ab) =>
      let '(? suffix) := suffix23 ab opt in
      ? (buf, suffix) };
  | ? (Overflow buf ab) =>
    let '(? prefix) := yellow_inject buf1 ab in
    ? (prefix, buf)
}.

(* Creates a green colored deque from three options, one being on a pair. *)

Equations cdeque_of_opt3 {A lvl} (o1 : option (prodN A lvl)) (o2 : option (prodN A (S lvl))) (o3 : option (prodN A lvl)) :
  { cd : lvl_cdeque A lvl green |
    cdeque_seq cd = option_seq o1 ++ flattenp (option_seq o2) ++ option_seq o3 } :=
cdeque_of_opt3 None None None := ? Small B0;
cdeque_of_opt3 (Some a) None None := ? Small (B1 a);
cdeque_of_opt3 None None (Some a) := ? Small (B1 a);
cdeque_of_opt3 (Some a) None (Some b) := ? Small (B2 a b);
cdeque_of_opt3 None (Some (prodS (a, b))) None := ? Small (B2 a b);
cdeque_of_opt3 (Some a) (Some (prodS (b, c))) None := ? Small (B3 a b c);
cdeque_of_opt3 None (Some (prodS (a, b))) (Some c) := ? Small (B3 a b c);
cdeque_of_opt3 (Some a) (Some (prodS (b, c))) (Some d) := ? Small (B4 a b c d).

(* Lemma rebarbatif {A lvl C} (rest : buffer A (S lvl) C) : map prodN_0_r (map prodN_n_Sm (buffer_seq (buffer_1_r rest))) = buffer_seq rest. *)

(* A new tactics, flattenp_lists is introduced. It is used when the context contains 
   an equality over lists of pairs. The tactic will destruct all the pairs, find 
   the hypothesis containing the equality, apply flattenp on it, simplify, and try
   to rewrite it in the goal. *)

Local Ltac destruct_prod :=
  repeat 
  match goal with 
  | ab : prodN _ (S _) |- _ => dependent destruction ab
  | p : _ * _ |- _ => destruct p
  end;
  cbn in *.

Local Ltac flattenp_eq H :=
  apply (f_equal flattenp) in H;
  rewrite !flattenp_app in H;
  cbn in H;
  try aac_rewrite H;
  try aac_rewrite <- H.

#[local] Obligation Tactic :=
  cbn; intros; destruct_prod; try (unfold id); try hauto db:rlist.

(* Takes a prefix buffer, a following buffer (when the next level is composed
   of only one buffer), and a suffix buffer. It allows to rearrange all 
   elements contained in those buffers into a green cdeque. *)

Equations make_small {A lvl C1 C2 C3}
  (b1 : buffer A lvl C1)
  (b2 : buffer A (S lvl) C2)
  (b3 : buffer A lvl C3) :
  { cd : lvl_cdeque A lvl green |
    cdeque_seq cd = buffer_seq b1 ++ flattenp (buffer_seq b2) ++ buffer_seq b3 } :=
make_small prefix1 buf suffix1 with (prefix_decompose prefix1), (suffix_decompose suffix1) => {
  | (? Ok p1), (? Ok s1) :=
    ? Big (Triple p1 Hole s1 PCGreen) (Small buf) _;
  | (? Ok p1), (? Underflow opt) with buffer_eject buf => {
    | ? None with opt => {
      | None := ? Small p1;
      | Some x with buffer_inject p1 x => { | ? cd := ? cd } };
    | ? Some (Any rest, cd) with suffix23 cd opt => {
      | ? suffix := ? Big (Triple p1 Hole suffix PCGreen) (Small rest) _ }
  };
  | (? Underflow opt), (? Ok s1) with buffer_pop buf => {
    | ? None with opt => {
      | None := ? Small s1;
      | Some x with buffer_push x s1 => { | ? cd := ? cd } };
    | ? Some (cd, Any rest) with prefix23 opt cd => {
      | ? prefix := ? Big (Triple prefix Hole s1 PCGreen) (Small rest) _ }
  };
  | (? Underflow p1), (? Underflow s1) with buffer_unsandwich buf => {
    | ? Sandwich ab rest cd with prefix23 p1 ab, suffix23 cd s1 => {
      | ? prefix, ? suffix := 
        ? Big (Triple prefix Hole suffix PCGreen) (Small rest) _ };
    | ? Alone opt with cdeque_of_opt3 p1 opt s1 => { | ? cd := ? cd } }
  | (? Overflow p1 ab), (? Ok s1) with buffer_push ab buf => {
    | ? rest => ? Big (Triple p1 Hole s1 PCGreen) rest _ };
  | (? Ok p1), (? Overflow s1 ab) with buffer_inject buf ab => {
    | ? rest => ? Big (Triple p1 Hole s1 PCGreen) rest _ };
  | (? Underflow opt), (? Overflow s1 ab) with suffix_rot buf ab => {
    | ? (cd, center) with prefix23 opt cd => {
      | ? prefix => ? Big (Triple prefix Hole s1 PCGreen) (Small center) _ } };
  | (? Overflow p1 ab), (? Underflow opt) with prefix_rot ab buf => {
    | ? (center, cd) with suffix23 cd opt => {
      | ? suffix => ? Big (Triple p1 Hole suffix PCGreen) (Small center) _ } };
  | (? Overflow p1 ab), (? Overflow s1 cd) with buffer_halve buf => {
    | ? (x, Any rest) with suffix12 ab x => {
      | ? prefix => ? Big (Triple p1 (Triple prefix Hole (B1 cd) PCYellow) s1 PCGreen) (Small rest) _ } }
}.
Next Obligation. Qed.
Next Obligation. Qed.
Next Obligation. Qed.
Next Obligation. Qed.
Next Obligation.  
  rewrite e1; cbn in *.
  hauto db:rlist.
Qed.
Next Obligation.
  rewrite e1.
  flattenp_eq y.
  hauto db:rlist.
Qed.
Next Obligation.
  rewrite e1.
  flattenp_eq y.
  hauto db:rlist.
Qed.
Next Obligation. Qed.
Next Obligation. Qed.
Next Obligation. Qed.
Next Obligation. Qed.

#[local] Obligation Tactic :=
  try first [ done | hauto db:rlist ].

(* Inductive eqT : forall (A B : Type), A = B -> A -> B -> Prop := 
| eqT_refl {A : Type} (a : A) : eqT A A eq_refl a a.
Arguments eqT {A B}.
Arguments eqT_refl {A a}.

Print eq_rect.

Inductive eq_prod {A : Type} : forall (n m : nat), n = m -> prodN A n -> prodN A m -> Prop := 
| prod_refl {n m : nat} {p : prodN A n} {e : n = m} : eq_prod n m e p (eq_rect n (fun n => prodN A n) p m e).
Arguments eq_prod {A n m}.

Lemma plus_n_Sm : forall n m, n + S m = S n + m.
Proof.
  induction n.
  - reflexivity.
  - intro; simpl; f_equal. apply IHn.
Defined. 

Equations prodN_n_Sm' {A} (lvl len : nat) (p : prodN A (len + S lvl)) :
    { p' : prodN A (S len + lvl) | eq_prod (plus_n_Sm len lvl) p p' } := 
prodN_n_Sm' lvl 0 p := ? p;
prodN_n_Sm' lvl (S len) (prodS (p1, p2)) with prodN_n_Sm' lvl len p1 => {
  | ? p1' with prodN_n_Sm' lvl len p2 => {
    | ? p2' := ? prodS (p1', p2') } }.
Next Obligation.
  cbn. intros H * H1 * H2.
  destruct H1.
  destruct H2.
  destruct e; simpl.
  constructor.
Qed.

Equations prodN_n_Sm {A} (lvl len : nat) (p : prodN A (len + S lvl)) : 
    { p' : prodN A (S len + lvl) | eqT (f_equal (fun n => prodN A n) (plus_n_Sm len lvl)) p p' } := 
prodN_n_Sm lvl len p with prodN_n_Sm' lvl len p => {
  | ? p' := ? p' 
}.
Next Obligation.
  cbn. intros * H. destruct H; destruct e. simpl. constructor.
Qed.
Arguments prodN_n_Sm {A lvl len}.

Equations buffer_n_Sm {A lvl len C} (b : buffer A (len + S lvl) C) :
    { b' : buffer A (S len + lvl) C | eqT (f_equal (fun n => buffer A n C) (plus_n_Sm len lvl)) b b' } := 
buffer_n_Sm B0 := ? B0;
buffer_n_Sm (B1 a) with prodN_n_Sm a => { | ? a' := ? (B1 a') };
buffer_n_Sm (B2 a b) with prodN_n_Sm a, prodN_n_Sm b => { | ? a', ? b' := ? (B2 a' b') };
buffer_n_Sm (B3 a b c) with prodN_n_Sm a, prodN_n_Sm b, prodN_n_Sm c => 
    { | ? a', ? b', ? c' := ? (B3 a' b' c') };
buffer_n_Sm (B4 a b c d) with prodN_n_Sm a, prodN_n_Sm b, prodN_n_Sm c, prodN_n_Sm d => 
    { | ? a', ? b', ? c', ? d' := ? (B4 a' b' c' d') };
buffer_n_Sm (B5 a b c d e) with prodN_n_Sm a, prodN_n_Sm b, prodN_n_Sm c, prodN_n_Sm d, prodN_n_Sm e => 
    { | ? a', ? b', ? c', ? d', ? e' := ? (B5 a' b' c' d' e') }.
Next Obligation.
  cbn. intros *. induction len.
  - simpl. constructor.
  - simpl. rewrite eq_trans_map_distr; simpl. rewrite f_equal_compose.
    eapply IHlen.


Equations cdeque_n_Sm {A C} (lvl len : nat) (a : lvl_cdeque A (len + S lvl) C) : 
    { a' : lvl_cdeque A (S len + lvl) C | eqT (f_equal (fun n => lvl_cdeque A n C) (eq_sym (plus_n_Sm len lvl))) a a' } := 
cdeque_n_Sm lvl 0 a := ? a;
cdeque_n_Sm lvl (S len) a := ? a. *)

Set Equations Transparent.

Equations plus_n_Sm : forall n m, n + S m = S (n + m) :=
plus_n_Sm 0 m := eq_refl;
plus_n_Sm (S n) m := f_equal S (plus_n_Sm n m).

(* Equations prodN_assoc {A} n m q : prodN A (n + (m + q)) -> prodN A (n + m + q) :=
prodN_assoc 0 m q p := p;
prodN_assoc (S n) m q (prodS (p1, p2)) := prodS (prodN_assoc n m q p1, prodN_assoc n m q p2).
Arguments prodN_assoc {A n m q}.

Equations buffer_assoc {A n m q C} (b : buffer A (n + (m + q)) C) : 
    { b' : buffer A (n + m + q) C | map prodN_assoc (buffer_seq b) = buffer_seq b' } := 
buffer_assoc B0 := ? B0;
buffer_assoc (B1 a) := ? B1 (prodN_assoc a);
buffer_assoc (B2 a b) := ? B2 (prodN_assoc a) (prodN_assoc b);
buffer_assoc (B3 a b c) := ? B3 (prodN_assoc a) (prodN_assoc b) (prodN_assoc c); 
buffer_assoc (B4 a b c d) := ? B4 (prodN_assoc a) (prodN_assoc b) (prodN_assoc c) (prodN_assoc d); 
buffer_assoc (B5 a b c d e) := ? B5 (prodN_assoc a) (prodN_assoc b) (prodN_assoc c) (prodN_assoc d) (prodN_assoc e).

Lemma map_flattenp_assoc {A n m q} (l : list (prodN A (S n + (m + q)))) :
    map prodN_assoc (flattenp l) = flattenp (map prodN_assoc l).
Proof.
  induction l.
  - reflexivity.
  - dependent destruction a. destruct p as [a b].
    rewrite app_cons_one. rewrite flattenp_app.
    simp flattenp.  
    rewrite !map_app.
    hauto db:rlist.
Qed.

Equations packet_assoc {A n m q len C} (p : lvl_packet A (n + (m + q)) len C) :
    { p' : lvl_packet A (n + m + q) len C | 
        map prodN_assoc (packet_front_seq p) = packet_front_seq p' /\ 
        map prodN_assoc (packet_rear_seq p) = packet_rear_seq p' } := 
packet_assoc Hole := ? Hole;
packet_assoc (Triple buf1 p buf2 PC) with buffer_assoc buf1, packet_assoc (n := S n) p, buffer_assoc buf2 => {
  | ? buf1', ? p', ? buf2' := ? (Triple buf1' p' buf2' PC) 
}.
Next Obligation.
  cbn beta. intros H * Hbuf1 * [Hfp Hrp] * Hbuf2 *.
  split; rewrite map_app;
  [simp packet_front_seq | simp packet_rear_seq];
  rewrite map_flattenp_assoc;
  hauto db:rlist.
Qed. *)

(* Equations cdeque_assoc {A n m q C} (cd : lvl_cdeque A (n + (m + q)) C) :
    { cd' : lvl_cdeque A (n + m + q) C | map prodN_assoc (cdeque_seq cd) = cdeque_seq cd' } :=
cdeque_assoc (Small buf) with buffer_assoc buf => {
  | ? buf' := ? Small buf' };
cdeque_assoc (Big p cd CC) with packet_assoc p, cdeque_assoc cd => {
  | ? p', ? cd' := ? Big p' _ CC 
}.
Next Obligation.
  cbn beta. intros H * [Hfp Hrp] * Hcd CC.
  (* Search "assoc". *)
  rewrite <-(@Nat.add_assoc n m q).
  rewrite Nat.add_assoc.
  assumption.
Qed.
Next Obligation.
  cbn beta. intros H *.
  simp cdeque_assoc_obligations_obligation_2. *)


(* Equations prodN_n_Sm {A : Type} (n m : nat) (p : prodN A (n + S m)) : prodN A (S n + m) := 
prodN_n_Sm 0 m p := p;
prodN_n_Sm (S n) m (prodS (p1, p2)) := prodS (prodN_n_Sm n m p1, prodN_n_Sm n m p2).
Arguments prodN_n_Sm {A n m}.

Equations buffer_n_Sm {A n m C} (b : buffer A (n + S m) C) : 
    { b' : buffer A (S n + m) C | map prodN_n_Sm (buffer_seq b) = buffer_seq b' } := 
buffer_n_Sm B0 := ? B0;
buffer_n_Sm (B1 a) := ? B1 (prodN_n_Sm a);
buffer_n_Sm (B2 a b) := ? B2 (prodN_n_Sm a) (prodN_n_Sm b);
buffer_n_Sm (B3 a b c) := ? B3 (prodN_n_Sm a) (prodN_n_Sm b) (prodN_n_Sm c); 
buffer_n_Sm (B4 a b c d) := ? B4 (prodN_n_Sm a) (prodN_n_Sm b) (prodN_n_Sm c) (prodN_n_Sm d); 
buffer_n_Sm (B5 a b c d e) := ? B5 (prodN_n_Sm a) (prodN_n_Sm b) (prodN_n_Sm c) (prodN_n_Sm d) (prodN_n_Sm e).

Lemma map_flattenp_n_Sm {A n m} (l : list (prodN A (S n + S m))) :
    map prodN_n_Sm (flattenp l) = flattenp (map prodN_n_Sm l).
Proof.
  induction l.
  - reflexivity.
  - dependent destruction a. destruct p as [a b].
    rewrite app_cons_one. rewrite flattenp_app.
    simp flattenp.  
    rewrite !map_app.
    hauto db:rlist.
Qed. *)

(* Equations packet_n_Sm {A n m len C} (p : lvl_packet A (n + S m) len C) :
    { p' : lvl_packet A (S n + m) len C | 
        map prodN_n_Sm (packet_front_seq p) = packet_front_seq p' /\ 
        map prodN_n_Sm (packet_rear_seq p) = packet_rear_seq p' } := 
packet_n_Sm Hole := ? Hole;
packet_n_Sm (Triple buf1 p buf2 PC) with buffer_n_Sm buf1, packet_n_Sm (n := S n) p, buffer_n_Sm buf2 => {
  | ? buf1', ? p', ? buf2' := ? (Triple buf1' p' buf2' PC) 
}.
Next Obligation.
  cbn beta. intros H * Hbuf1 * [Hfp Hrp] * Hbuf2 PC.
  split; rewrite map_app; 
  [simp packet_front_seq | simp packet_rear_seq];
  rewrite map_flattenp_n_Sm;
  hauto db:rlist.
Qed.

Equations cdeque_n_Sm {A n m C} (cd : lvl_cdeque A (n + S m) C) :
    { cd' : lvl_cdeque A (S n + m) C | map prodN_n_Sm (cdeque_seq cd) = cdeque_seq cd' } :=
cdeque_n_Sm (Small buf) with buffer_n_Sm buf => {
  | ? buf' := ? Small buf' };
cdeque_n_Sm (Big p cd CC) with packet_n_Sm p, cdeque_n_Sm cd => {
  | ? p', ? cd' := ? Big p' cd' CC 
}. *)

(* Equations cdeque_map {A n g C} (f : prodN A n -> prodN A (g n)) (cd : lvl_cdeque A n C) :
    { cd' : lvl_cdeque A (g n) C | map f (cdeque cd) = cdeque cd' } := 
cdeque_map f (Small b) with buffer_n_Sm f b => { | b' := ? Small b' };
cdeque_map f (Big p cd CC)  *)

Equations get_color {A lvl C} : lvl_cdeque A lvl C -> color :=
get_color _ := C.

Equations get_length {A lvl len C} : lvl_packet A lvl len C -> nat :=
get_length _ := len.

Equations inv_flattenp {A n} : list (prodN A n) -> list (prodN A (S n)) := 
inv_flattenp [] := [];
inv_flattenp [a] := [];
inv_flattenp (a :: b :: l) := [prodS (a, b)] ++ inv_flattenp l.

Lemma flattenp_id {A n} : forall (l : list (prodN A (S n))), l = inv_flattenp (flattenp l).
Proof.
  induction l.
  - reflexivity.
  - dependent destruction a. destruct p as [a b].
    simp flattenp.
    do 2 rewrite <-app_cons_one. 
    simp inv_flattenp.
    rewrite app_cons_one. f_equal. assumption.
Qed.

(* Inductive even_list (A : Type) : Type :=
| ENil
| ECons (a b : A) (l : even_list A).
Arguments ENil {A}.
Arguments ECons {A}.

Fixpoint even_list_to_list {A : Type} (l : even_list A) : list A :=
  match l with 
  | ENil => []
  | ECons a b l => [a] ++ [b] ++ even_list_to_list l
  end.

Fixpoint list_to_even_list {A : Type} (l : list A) : length l mod 2 = 0 -> 

Lemma teeeeest {A n} : 
    forall (l : list (prodN A n)), 
    (length l) mod 2 = 0 ->
    flattenp (inv_flattenp l) = l.
Proof.
  intros l e. induction l.
  - reflexivity.
  -  *)

Print eq_rect.

Lemma simplify {A n m} (e : n = m) (l : list (prodN A (S n))) (l' : list (prodN A (S m))) : 
    l' = eq_rect (S n) (fun n => list (prodN A n)) l (S m) (f_equal S e) ->
    flattenp l' = eq_rect n (fun n => list (prodN A n)) (flattenp l) m e.
Proof.
  intro H.
  symmetry in H. destruct H.
  rewrite (flattenp_id l).
  rewrite (map_subst_map S (@inv_flattenp A)).
  pose (fun n => compose (@flattenp A n) inv_flattenp) as f.
  assert (forall n l, f n l = flattenp (inv_flattenp l)). { intros. unfold f. reflexivity. }
  rewrite <-H.
  rewrite <-(map_subst f).
  unfold f. unfold compose.
  reflexivity. 
Qed.

Lemma first_step {A n m} (l : list (prodN A (S n + m))) (l' : list (prodN A (n + S m))) : 
    l = eq_rect _ (fun n => list (prodN A n)) l' _ (plus_n_Sm n m) ->
    flattenp_plus_m (flattenp l) = flattenp (flattenp_plus_m l').
Proof.
  intro e.
  induction n.
  - simp flattenp_plus_m. 
    rewrite <-eq_rect_eq in e. destruct e. 
    unfold id. reflexivity.
  - simp flattenp_plus_m.
    apply IHn.
    apply simplify.
    assumption. 
Qed.

Lemma first_step' {A n m} (l : list (prodN A (n + S m))) (l' : list (prodN A (S n + m))) :
    l = eq_rect _ (fun n => list (prodN A n)) l' _ (eq_sym (plus_n_Sm n m)) ->
    flattenp (flattenp_plus_m l) = flattenp_plus_m (flattenp l').
Proof.
  intro e.
  induction n.
  - simp flattenp_plus_m.
    rewrite <-eq_rect_eq in e. destruct e.
    unfold id. reflexivity.
  - simp flattenp_plus_m.
    apply IHn.
    apply simplify.
    simpl in e.
    rewrite <-eq_sym_map_distr.
    assumption.
Qed.

Lemma test {A len lvl C} (cd : lvl_cdeque A (S (S (len + lvl))) C) (cd' : lvl_cdeque A (S (len + S lvl)) C) : 
    cdeque_seq cd = cdeque_seq (eq_rect _ (fun n => lvl_cdeque A n C) cd' _ (f_equal S (plus_n_Sm len lvl))) -> 
    (flattenp_plus_m (flattenp (flattenp (cdeque_seq cd)))) = flattenp (flattenp_plus_m (flattenp (cdeque_seq cd'))).
Proof.
  intro H.
  apply first_step.
  apply simplify.
  symmetry in H. destruct H.
  rewrite (map_subst (fun n => @cdeque_seq A n C)).
  reflexivity.
Qed.

Lemma test' {A len lvl C} (cd : lvl_cdeque A (S (len + S lvl)) C) (cd' : lvl_cdeque A (S (S (len + lvl))) C) :
    cdeque_seq cd = cdeque_seq (eq_rect _ (fun n => lvl_cdeque A n C) cd' _ (f_equal S (eq_sym (plus_n_Sm len lvl)))) ->
    (flattenp (flattenp_plus_m (flattenp (cdeque_seq cd)))) = flattenp_plus_m (flattenp (flattenp (cdeque_seq cd'))).
Proof.
  intro H.
  apply first_step'.
  apply simplify.
  symmetry in H. destruct H.
  rewrite (map_subst (fun n => @cdeque_seq A n C)).
  reflexivity.
Qed.

(* Takes a red cdeque and returns a green one representing the same set. *)

Equations green_of_red {A lvl} (cd : lvl_cdeque A lvl red) :
  { cd' : lvl_cdeque A lvl green | cdeque_seq cd' = cdeque_seq cd } :=
green_of_red (Big (Triple p1 Hole s1 PCRed) (Small buf) CCRed) with make_small p1 buf s1 => {
  | ? cd' := ? cd' };
green_of_red (Big (Triple p1 (Triple p2 child s2 PCYellow) s1 PCRed) cd CCRed)
  with yellow_prefix_concat p1 (Yellowish p2), yellow_suffix_concat (Yellowish s2) s1 => {
  | ? (p1', Any p2'), ? (Any s2', s1') :=
    let C := get_color cd in 
    let len := get_length child in
    let cd' := eq_rect _ (fun n => lvl_cdeque A n C) cd _ (f_equal S (eq_sym (plus_n_Sm len lvl))) in 
    ? Big (Triple p1' Hole s1' PCGreen) (Big (Triple p2' child s2' PCRed) cd' CCRed) CCGreen };
green_of_red (Big (Triple p1 Hole s1 PCRed) (Big (Triple p2 child s2 PCGreen) cd CCGreen) CCRed)
  with green_prefix_concat p1 p2, green_suffix_concat s2 s1 => {
  | ? (p1', Yellowish p2'), ? (Yellowish s2', s1') :=
    let C := get_color cd in 
    let len := get_length child in
    let cd' := eq_rect _ (fun n => lvl_cdeque A n C) cd _ (f_equal S (plus_n_Sm len lvl)) in 
    ? Big (Triple p1' (Triple p2' child s2' PCYellow) s1' PCGreen) cd' CCGreen }.
Next Obligation.
  cbn. intros * Hpref * Hsuff *.
  autorewrite with rlist. 
  aac_rewrite <-Hpref. aac_rewrite <-Hsuff. 
  aac_normalise.
  do 3 apply <-app_inv_head_iff.
  apply app_inv_tail_iff.
  unfold get_color, get_length, compose.
  apply test.
  reflexivity.
Qed.
Next Obligation.
  cbn. intros * Hpref * Hsuff *.
  autorewrite with rlist.
  aac_rewrite <-Hpref. aac_rewrite <-Hsuff.
  aac_normalise.
  do 3 apply <-app_inv_head_iff.
  apply app_inv_tail_iff.
  unfold get_color, get_length, compose.
  apply test'.
  reflexivity.
Qed.

(* Takes a green or red cdeque, and returns a green one representing
   the same set. *)

Equations ensure_green {A lvl C} (ny: not_yellow C) (cd : lvl_cdeque A lvl C) :
  { cd' : lvl_cdeque A lvl green | cdeque_seq cd' = cdeque_seq cd } :=
ensure_green Not_yellow (Small buf) := ? Small buf;
ensure_green Not_yellow (Big x cd CCGreen) := ? Big x cd CCGreen;
ensure_green Not_yellow (Big x cd CCRed) := green_of_red (Big x cd CCRed).

(* Takes a yellow packet, as a prefix buffer, a child packet and a suffix 
   buffer, and a green or red cdeque. Returns a deque starting with this packet 
   and followed by the green version of the input colored deque. *)

Equations make_yellow {A len} {G1 Y1 Y2 G3 Y3 G4 R4}
  (buf1 : buffer A 0 (Mix G1 Y1 NoRed))
  (p : lvl_packet A 1 len (Mix NoGreen Y2 NoRed))
  (buf2 : buffer A 0 (Mix G3 Y3 NoRed))
  (cd : lvl_cdeque A (S len + 0) (Mix G4 NoYellow R4)) :
  { sq : deque A |
    deque_seq sq = map prodN_0 (
               buffer_seq buf1 ++
               flattenp (packet_front_seq p) ++
               flattenp_plus_m (cdeque_seq cd) ++
               flattenp (packet_rear_seq p) ++
               buffer_seq buf2) }
:=
make_yellow p1 child s1 cd with ensure_green Not_yellow cd => {
  | ? cd' => ? T (Big (Triple p1 child s1 PCYellow) cd' CCYellow) }.

(* Takes a red packet, as a prefix buffer, a child packet and a suffix
   buffer, and a green cdeque. Returns the green version of the colored deque 
   made of the red packet followed by the green cdeque. *)

Equations make_red {A len} {C1 Y2 C3}
  (buf1 : buffer A 0 C1)
  (p : lvl_packet A 1 len (Mix NoGreen Y2 NoRed))
  (buf2 : buffer A 0 C3)
  (cd : lvl_cdeque A (S len + 0) green) :
  { sq : deque A |
    deque_seq sq = map prodN_0 (
               buffer_seq buf1 ++
               flattenp (packet_front_seq p) ++
               flattenp_plus_m (cdeque_seq cd) ++
               flattenp (packet_rear_seq p) ++
               buffer_seq buf2) }
:=
make_red p1 child s1 cd with green_of_red (Big (Triple p1 child s1 PCRed) cd CCRed) => {
  | ? cd' => ? T cd' }.

Module S.

(* Pushes an element on a deque. *)

Equations push {A: Type} (x : A) (sq : deque A) :
  { sq' : deque A | deque_seq sq' = [x] ++ deque_seq sq }
:=
push x (T (Small buf)) with buffer_push (prodZ x) buf => {
  | ? buf' => ? T buf' };
push x (T (Big (Triple p1 child s1 PCGreen) dq CCGreen)) with green_push (prodZ x) p1 => {
  | ? buf' with make_yellow buf' child s1 dq => {
    | ? sq' => ? sq' } };
push x (T (Big (Triple p1 child s1 PCYellow) dq CCYellow))
  with yellow_push (prodZ x) (Yellowish p1) => {
  | ? (Any p1') with make_red p1' child s1 dq => {
    | ? sq' => ? sq' } }.

(* Injects an element on a deque. *)

Equations inject {A: Type} (sq : deque A) (x : A) :
  { sq' : deque A | deque_seq sq' = deque_seq sq ++ [x] }
:=
inject (T (Small buf)) x with buffer_inject buf (prodZ x) => {
  | ? buf' => ? T buf' };
inject (T (Big (Triple p1 child s1 PCGreen) cd CCGreen)) x with green_inject s1 (prodZ x) => {
  | ? buf' with make_yellow p1 child buf' cd => {
    | ? sq' => ? sq' } };
inject (T (Big (Triple p1 child s1 PCYellow) cd CCYellow)) x
  with yellow_inject (Yellowish s1) (prodZ x) => {
  | ? (Any s1') with make_red p1 child s1' cd => {
    | ? sq' => ? sq' } }.

(* Pops an element from a deque. *)

Equations pop {A: Type} (sq : deque A) :
  { o : option (A * deque A) |
    deque_seq sq = match o with
               | None => []
               | Some (x, sq') => [x] ++ deque_seq sq'
               end } :=
pop (T (Small buf)) with buffer_pop buf => {
  pop _ (? None) := ? None;
  pop _ (? Some (prodZ x, Any buf')) := ? Some (x, T (Small buf'))
};
pop (T (Big (Triple p1 child s1 PCGreen) cd CCGreen)) with green_pop p1 => {
  | ? (prodZ x, Yellowish p1') with make_yellow p1' child s1 cd => {
    | ? sq' => ? Some (x, sq') } };
pop (T (Big (Triple p1 child s1 PCYellow) cd CCYellow)) with yellow_pop (Yellowish p1) => {
  | ? (prodZ x, Any p1') with make_red p1' child s1 cd => {
    | ? sq' => ? Some (x, sq') } }.

(* Ejects an element from a deque. *)

Equations eject {A : Type} (sq : deque A) :
  { o : option (deque A * A) |
    deque_seq sq = match o with
               | None => []
               | Some (sq', x) => deque_seq sq' ++ [x]
               end } :=
eject (T (Small buf)) with buffer_eject buf => {
  eject _ (? None) := ? None;
  eject _ (? Some (Any buf', prodZ x)) := ? Some (T (Small buf'), x)
};
eject (T (Big (Triple p1 child s1 PCGreen) cd CCGreen)) with green_eject s1 => {
  | ? (Yellowish s1', prodZ x) with make_yellow p1 child s1' cd => {
    | ? sq' => ? Some (sq', x) } };
eject (T (Big (Triple p1 child s1 PCYellow) cd CCYellow)) with yellow_eject (Yellowish s1) => {
  | ? (Any s1', prodZ x) with make_red p1 child s1' cd => {
    | ? sq' => ? Some (sq', x) } }.

End S.