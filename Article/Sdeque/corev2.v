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
  | prodS {n : nat} : prodN A n -> prodN A n -> prodN A (S n).
Arguments prodZ {A}.
Arguments prodS {A n}.

(* In the following types, an integer parameter is introduced : the [lvl] of
   the type. The level contains information on the type of elements stored in
   the structure encoded. As elements stored in our different structure are
   iterated pairs of a type A, the level is simply the number of times we
   iterated the product on A.

   For example, a buffer of level 0 will contain elements of A, a buffer of
   level 1 will contain elements of A * A, a buffer of level 2 will contain
   elements of (A * A) * (A * A), and so on ... *)

(* A type for leveled buffers. *)

Inductive buffer (A : Type) (lvl : nat) : color -> Type :=
  | B0 : buffer A lvl red
  | B1 : prodN A lvl -> buffer A lvl yellow
  | B2 : prodN A lvl -> prodN A lvl -> buffer A lvl green
  | B3 : prodN A lvl -> prodN A lvl -> prodN A lvl -> buffer A lvl green
  | B4 : prodN A lvl -> prodN A lvl ->
         prodN A lvl -> prodN A lvl -> buffer A lvl yellow
  | B5 : prodN A lvl -> prodN A lvl -> prodN A lvl ->
         prodN A lvl -> prodN A lvl -> buffer A lvl red.
Arguments B0 {A lvl}.
Arguments B1 {A lvl}.
Arguments B2 {A lvl}.
Arguments B3 {A lvl}.
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

(* A type for leveled packet. *)

Inductive packet (A : Type) (hlvl : nat) : nat -> color -> Type :=
  | Hole : packet A hlvl hlvl uncolored
  | PGreen {tlvl : nat} {Y : yellow_hue} :
    buffer A hlvl green ->
    packet A (S hlvl) tlvl (Mix NoGreen Y NoRed) ->
    buffer A hlvl green ->
    packet A hlvl tlvl green
  | PYellow {tlvl : nat} {GP YP Y GS YS} :
    buffer A hlvl (Mix GP YP NoRed) ->
    packet A (S hlvl) tlvl (Mix NoGreen Y NoRed) ->
    buffer A hlvl (Mix GS YS NoRed) ->
    packet A hlvl tlvl yellow
  | PRed {tlvl : nat} {CP Y CS} :
    buffer A hlvl CP ->
    packet A (S hlvl) tlvl (Mix NoGreen Y NoRed) ->
    buffer A hlvl CS ->
    packet A hlvl tlvl red.
Arguments Hole {A hlvl}.
Arguments PGreen {A hlvl tlvl Y}.
Arguments PYellow {A hlvl tlvl GP YP Y GS YS}.
Arguments PRed {A hlvl tlvl CP Y CS}.

(* A type for leveled colored deque. *)

Inductive chain (A : Type) (lvl : nat) : color -> Type :=
  | Ending {C : color} : buffer A lvl C -> chain A lvl green
  | CGreen {tlvl : nat} {G : green_hue} {R : red_hue} :
    packet A lvl tlvl green ->
    chain A tlvl (Mix G NoYellow R) ->
    chain A lvl green
  | CYellow {tlvl : nat} :
    packet A lvl tlvl yellow ->
    chain A tlvl green ->
    chain A lvl yellow
  | CRed {tlvl : nat} :
    packet A lvl tlvl red ->
    chain A tlvl green ->
    chain A lvl red.
Arguments Ending {A lvl C}.
Arguments CGreen {A lvl tlvl G R}.
Arguments CYellow {A lvl tlvl}.
Arguments CRed {A lvl tlvl}.

(* The leveled decompose type. *)

Inductive decompose (A : Type) (lvl : nat) : Type :=
| Underflow : option (prodN A lvl) -> decompose A lvl
| Ok : buffer A lvl green -> decompose A lvl
| Overflow : buffer A lvl green -> prodN A (S lvl) -> decompose A lvl.

Arguments Underflow {_ _}.
Arguments Ok {_ _}.
Arguments Overflow {_ _}.

(* The leveled sandwich type. *)

Inductive sandwich (A : Type) (lvl : nat) : Type :=
| Alone : option (prodN A lvl) -> sandwich A lvl
| Sandwich {C} : prodN A lvl -> buffer A lvl C -> prodN A lvl -> sandwich A lvl.
Arguments Alone {A lvl}.
Arguments Sandwich {A lvl C}.

(* A type for deque. *)

Inductive deque (A : Type) : Type :=
  T : forall (G : green_hue) (Y : yellow_hue),
      chain A 0 (Mix G Y NoRed) ->
      deque A.
Arguments T {A G Y}.

(* Models *)

Set Equations Transparent.

Opaque app.
Definition singleton {A : Type} (x : A) : list A := [x].
Opaque singleton.

(* A list of tactics to be used when trying to resolve obligations generated by
   Equations. *)

#[export] Hint Rewrite <-app_assoc : rlist.
#[export] Hint Rewrite <-app_comm_cons : rlist.
#[export] Hint Rewrite app_nil_r : rlist.

#[local] Obligation Tactic :=
  try first [ done | cbn; hauto db:rlist ].

(* Returns the sequence contained in a product. *)

Equations prodN_seq {A} (n : nat) : prodN A n -> list A :=
prodN_seq 0 (prodZ a) := [a];
prodN_seq (S n) (prodS p1 p2) := prodN_seq n p1 ++ prodN_seq n p2.
Arguments prodN_seq {A n}.

(* Returns the sequence contained in an option. *)

Equations option_seq {A lvl} : option (prodN A lvl) -> list A :=
option_seq None := [];
option_seq (Some x) := prodN_seq x.

(* Returns the sequence contained in a buffer. *)

Equations buffer_seq {A lvl C} : buffer A lvl C -> list A :=
buffer_seq B0 := [];
buffer_seq (B1 a) := prodN_seq a;
buffer_seq (B2 a b) := prodN_seq a ++ prodN_seq b;
buffer_seq (B3 a b c) := prodN_seq a ++ prodN_seq b ++ prodN_seq c;
buffer_seq (B4 a b c d) :=
  prodN_seq a ++ prodN_seq b ++ prodN_seq c ++ prodN_seq d;
buffer_seq (B5 a b c d e) :=
  prodN_seq a ++ prodN_seq b ++ prodN_seq c ++ prodN_seq d ++ prodN_seq e.

(* Returns the sequence contained in a yellow buffer. *)

Equations yellow_buffer_seq {A lvl} : yellow_buffer A lvl -> list A :=
yellow_buffer_seq (Yellowish buf) := buffer_seq buf.

(* Returns the sequence contained in any buffer. *)

Equations any_buffer_seq {A lvl} : any_buffer A lvl -> list A :=
any_buffer_seq (Any buf) := buffer_seq buf.

(* Returns the sequence of elements stored in prefix buffers along a
   packet. *)

Equations packet_front_seq {A lvl len C} : packet A lvl len C -> list A :=
packet_front_seq Hole := [];
packet_front_seq (PGreen buf1 p _) := buffer_seq buf1 ++ packet_front_seq p;
packet_front_seq (PYellow buf1 p _) := buffer_seq buf1 ++ packet_front_seq p;
packet_front_seq (PRed buf1 p _) := buffer_seq buf1 ++ packet_front_seq p.

(* Returns the sequence of elements stored in suffix buffers along a
   packet. *)

Equations packet_rear_seq {A lvl len C} : packet A lvl len C -> list A :=
packet_rear_seq Hole := [];
packet_rear_seq (PGreen _ p buf2) := packet_rear_seq p ++ buffer_seq buf2;
packet_rear_seq (PYellow _ p buf2) := packet_rear_seq p ++ buffer_seq buf2;
packet_rear_seq (PRed _ p buf2) := packet_rear_seq p ++ buffer_seq buf2.

(* Returns the sequence contained in a leveled colored deque. *)

Equations chain_seq {A lvl C} : chain A lvl C -> list A :=
chain_seq (Ending buf) := buffer_seq buf;
chain_seq (CGreen p cd) :=
  packet_front_seq p ++ chain_seq cd ++ packet_rear_seq p;
chain_seq (CYellow p cd) :=
  packet_front_seq p ++ chain_seq cd ++ packet_rear_seq p;
chain_seq (CRed p cd) :=
  packet_front_seq p ++ chain_seq cd ++ packet_rear_seq p.

(* Returns the sequence of non-excess elements of an object of type decompose. *)

Equations decompose_main_seq {A lvl} (dec : decompose A lvl) : list A :=
decompose_main_seq (Underflow opt) := option_seq opt;
decompose_main_seq (Ok b) := buffer_seq b;
decompose_main_seq (Overflow b _) := buffer_seq b.

(* Returns the sequence of excess elements of an object of type decompose. *)

Equations decompose_rest_seq {A lvl} (dec : decompose A lvl) : list A :=
decompose_rest_seq (Underflow _) := [];
decompose_rest_seq (Ok _) := [];
decompose_rest_seq (Overflow _ p) := prodN_seq p.

(* Returns the sequence of elements of an object of type sandwich. *)

Equations sandwich_seq {A lvl} (sw : sandwich A lvl) : list A :=
sandwich_seq (Alone opt) := option_seq opt;
sandwich_seq (Sandwich x b y) := prodN_seq x ++ buffer_seq b ++ prodN_seq y.

(* Returns the sequence contained in a deque. *)

Equations deque_seq {A} : deque A -> list A :=
deque_seq (T dq) := chain_seq dq.

Unset Equations Transparent.

Notation "? x" := (@exist _ _ x _) (at level 100).

(* Elements *)

(* The empty colored deque. *)

Equations empty_chain {A lvl} :
  { cd : chain A lvl green | chain_seq cd = [] } :=
empty_chain := ? Ending B0.

(* The empty deque. *)

Equations empty {A} : { d : deque A | deque_seq d = [] } :=
empty with empty_chain => { | ? cd := ? T cd }.

(* Functions *)

(* A new tactic [destruct_prod] is introduced. It destructs all elements of
   higher level into elements of lower levels. *)

Local Ltac destruct_prod :=
  repeat
  match goal with
  | a : prodN _ 0 |- _ => dependent destruction a
  | ab : prodN _ (S _) |- _ => dependent destruction ab
  | p : _ * _ |- _ => destruct p
  end;
  cbn in *.

#[local] Obligation Tactic :=
  try first [ done | cbn; hauto db:rlist ].

(* Pushing on a green buffer. *)

Equations green_push {A lvl} (x : prodN A lvl) (b : buffer A lvl green) :
  { b' : yellow_buffer A lvl |
    yellow_buffer_seq b' = prodN_seq x ++ buffer_seq b } :=
green_push x (B2 a b) := ? Yellowish (B3 x a b);
green_push x (B3 a b c) := ? Yellowish (B4 x a b c).

(* Injecting on a green buffer. *)

Equations green_inject {A lvl} (b : buffer A lvl green) (x : prodN A lvl) :
  { b' : yellow_buffer A lvl |
    yellow_buffer_seq b' = buffer_seq b ++ prodN_seq x } :=
green_inject (B2 a b) x := ? Yellowish (B3 a b x);
green_inject (B3 a b c) x := ? Yellowish (B4 a b c x).

(* Poping from a green buffer. *)

Equations green_pop {A lvl} (b : buffer A lvl green) :
  { '(x, b') : prodN A lvl * yellow_buffer A lvl | buffer_seq b = prodN_seq x ++ yellow_buffer_seq b' } :=
green_pop (B2 a b) => ? (a, (Yellowish (B1 b)));
green_pop (B3 a b c) => ? (a, (Yellowish (B2 b c))).

(* Ejecting from a green buffer. *)

Equations green_eject {A lvl} (b : buffer A lvl green) :
  { '(b', x) : yellow_buffer A lvl * prodN A lvl | buffer_seq b = yellow_buffer_seq b' ++ prodN_seq x } :=
green_eject (B2 a b) => ? ((Yellowish (B1 a)), b);
green_eject (B3 a b c) => ? ((Yellowish (B2 a b)), c).

(* Pushing on a yellow buffer. *)

#[derive(eliminator=no)]
Equations yellow_push {A lvl} (x : prodN A lvl) (b : yellow_buffer A lvl) :
  { b' : any_buffer A lvl | any_buffer_seq b' = prodN_seq x ++ yellow_buffer_seq b } :=
yellow_push x (Yellowish buf) with buf => {
  | B1 a => ? Any (B2 x a);
  | B2 a b => ? Any (B3 x a b);
  | B3 a b c => ? Any (B4 x a b c);
  | B4 a b c d => ? Any (B5 x a b c d)
}.

(* Injecting on a yellow buffer. *)

#[derive(eliminator=no)]
Equations yellow_inject {A lvl} (b : yellow_buffer A lvl) (x : prodN A lvl) :
  { b' : any_buffer A lvl | any_buffer_seq b' = yellow_buffer_seq b ++ prodN_seq x } :=
yellow_inject (Yellowish buf) x with buf := {
  | B1 a => ? Any (B2 a x);
  | B2 a b => ? Any (B3 a b x);
  | B3 a b c => ? Any (B4 a b c x);
  | B4 a b c d => ? Any (B5 a b c d x)
}.

(* Poping from a yellow buffer. *)

#[derive(eliminator=no)]
Equations yellow_pop {A lvl} (b : yellow_buffer A lvl) :
  { '(x, b') : prodN A lvl * any_buffer A lvl | yellow_buffer_seq b = prodN_seq x ++ any_buffer_seq b' } :=
yellow_pop (Yellowish buf) with buf => {
  | B1 a => ? (a, Any B0);
  | B2 a b => ? (a, Any (B1 b));
  | B3 a b c => ? (a, Any (B2 b c));
  | B4 a b c d => ? (a, Any (B3 b c d))
}.

(* Ejecting from a yellow buffer. *)

#[derive(eliminator=no)]
Equations yellow_eject {A lvl} (b : yellow_buffer A lvl) :
  { '(b', x) : any_buffer A lvl * prodN A lvl | yellow_buffer_seq b = any_buffer_seq b' ++ prodN_seq x } :=
yellow_eject (Yellowish buf) with buf => {
  | B1 a => ? (Any B0, a);
  | B2 a b => ? (Any (B1 a), b);
  | B3 a b c => ? (Any (B2 a b), c);
  | B4 a b c d => ? (Any (B3 a b c), d)
}.

(* Pushing on a buffer. *)

Equations buffer_push {A lvl C} (x : prodN A lvl) (b : buffer A lvl C) :
  { cd : chain A lvl green | chain_seq cd = prodN_seq x ++ buffer_seq b } :=
buffer_push x B0 := ? Ending (B1 x);
buffer_push x (B1 a) := ? Ending (B2 x a);
buffer_push x (B2 a b) := ? Ending (B3 x a b);
buffer_push x (B3 a b c) := ? Ending (B4 x a b c);
buffer_push x (B4 a b c d) := ? Ending (B5 x a b c d);
buffer_push x (B5 a b c d e) :=
  ? CGreen (PGreen (B3 x a b) Hole (B3 c d e)) (Ending B0).

(* Injecting on a buffer. *)

Equations buffer_inject {A lvl C} (b : buffer A lvl C) (x : prodN A lvl) :
  { cd : chain A lvl green | chain_seq cd = buffer_seq b ++ prodN_seq x } :=
buffer_inject B0 x := ? Ending (B1 x);
buffer_inject (B1 a) x := ? Ending (B2 a x);
buffer_inject (B2 a b) x := ? Ending (B3 a b x);
buffer_inject (B3 a b c) x := ? Ending (B4 a b c x);
buffer_inject (B4 a b c d) x := ? Ending (B5 a b c d x);
buffer_inject (B5 a b c d e) x :=
    ? CGreen (PGreen (B3 a b c) Hole (B3 d e x))(Ending B0).

(* Poping from a buffer. *)

Equations buffer_pop {A lvl C} (b : buffer A lvl C) :
  { o : option (prodN A lvl * any_buffer A lvl) |
    buffer_seq b =
    match o with
    | None => []
    | Some (x, b') => prodN_seq x ++ any_buffer_seq b'
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
    | Some (b', x) => any_buffer_seq b' ++ prodN_seq x
    end } :=
buffer_eject (B5 a b c d e) := ? Some (Any (B4 a b c d), e);
buffer_eject B0 := ? None;
buffer_eject buf with yellow_eject (Yellowish buf) => { | ? o := ? Some o }.

(* Pushes then ejects. *)

Equations prefix_rot {A lvl C} (x : prodN A lvl) (b : buffer A lvl C) :
  { '(b', y) : buffer A lvl C * prodN A lvl | prodN_seq x ++ buffer_seq b = buffer_seq b' ++ prodN_seq y } :=
prefix_rot x B0 := ? (B0, x);
prefix_rot x (B1 a) := ? (B1 x, a);
prefix_rot x (B2 a b) := ? (B2 x a, b);
prefix_rot x (B3 a b c) := ? (B3 x a b, c);
prefix_rot x (B4 a b c d) := ? (B4 x a b c, d);
prefix_rot x (B5 a b c d e) := ? (B5 x a b c d, e).

(* Injects then pops. *)

Equations suffix_rot {A lvl C} (b : buffer A lvl C) (y : prodN A lvl) :
  { '(x, b') : prodN A lvl * buffer A lvl C | buffer_seq b ++ prodN_seq y = prodN_seq x ++ buffer_seq b' } :=
suffix_rot B0 x := ? (x, B0);
suffix_rot (B1 a) x := ? (a, B1 x);
suffix_rot (B2 a b) x := ? (a, B2 b x);
suffix_rot (B3 a b c) x := ? (a, B3 b c x);
suffix_rot (B4 a b c d) x := ? (a, B4 b c d x);
suffix_rot (B5 a b c d e) x := ? (a, B5 b c d e x).

(* Create a green buffer by injecting a pair onto an option. *)

Equations prefix23 {A lvl} (o : option (prodN A lvl)) (p: prodN A (S lvl)) :
  { b : buffer A lvl green | buffer_seq b = option_seq o ++ prodN_seq p } :=
prefix23 None (prodS b c) := ? B2 b c;
prefix23 (Some a) (prodS b c) := ? B3 a b c.

(* Create a green buffer by poping a pair onto an option. *)

Equations suffix23 {A lvl} (p : prodN A (S lvl)) (o : option (prodN A lvl)) :
  { b : buffer A lvl green | buffer_seq b = prodN_seq p ++ option_seq o } :=
suffix23 (prodS a b) None := ? B2 a b;
suffix23 (prodS a b) (Some c) := ? B3 a b c.

(* Create a yellow (or green) buffer by pushing an element onto an option. *)

Equations suffix12 {A lvl} (x : prodN A lvl) (o : option (prodN A lvl)) :
  { b : yellow_buffer A lvl |
    yellow_buffer_seq b = prodN_seq x ++ option_seq o } :=
suffix12 x None := ? Yellowish (B1 x);
suffix12 x (Some y) := ? Yellowish (B2 x y).

(* Returns the decomposed version of a buffer. Here, it is a prefix
   decomposition: when the buffer is overflowed, elements at the end are
   removed. *)

Equations prefix_decompose {A lvl C} (b : buffer A lvl C) :
  { dec : decompose A lvl | buffer_seq b = decompose_main_seq dec ++ decompose_rest_seq dec } :=
prefix_decompose B0 := ? Underflow None;
prefix_decompose (B1 x) := ? Underflow (Some x);
prefix_decompose (B2 a b) := ? Ok (B2 a b);
prefix_decompose (B3 a b c) := ? Ok (B3 a b c);
prefix_decompose (B4 a b c d) := ? Overflow (B2 a b) (prodS c d);
prefix_decompose (B5 a b c d e) := ? Overflow (B3 a b c) (prodS d e).

(* Returns the decomposed version of a buffer. Here, it is a suffix
   decomposition: when the buffer is overflowed, elements at the beginning are
   removed. *)

Equations suffix_decompose {A lvl C} (b : buffer A lvl C) :
  { dec : decompose A lvl | buffer_seq b = decompose_rest_seq dec ++ decompose_main_seq dec } :=
suffix_decompose B0 := ? Underflow None;
suffix_decompose (B1 x) := ? Underflow (Some x);
suffix_decompose (B2 a b) := ? Ok (B2 a b);
suffix_decompose (B3 a b c) := ? Ok (B3 a b c);
suffix_decompose (B4 a b c d) := ? Overflow (B2 c d) (prodS a b);
suffix_decompose (B5 a b c d e) := ? Overflow (B3 c d e) (prodS a b).

(* Returns the sandwich representation of a buffer. *)

Equations buffer_unsandwich {A lvl C} (b : buffer A lvl C) :
  { sw : sandwich A lvl | buffer_seq b = sandwich_seq sw } :=
buffer_unsandwich B0 := ? Alone None;
buffer_unsandwich (B1 a) := ? Alone (Some a);
buffer_unsandwich (B2 a b) := ? Sandwich a B0 b;
buffer_unsandwich (B3 a b c) := ? Sandwich a (B1 b) c;
buffer_unsandwich (B4 a b c d) := ? Sandwich a (B2 b c) d;
buffer_unsandwich (B5 a b c d e) := ? Sandwich a (B3 b c d) e.

(* In the following, when talking about structures, we will write n-struct for
   a structure of level n. *)

(* Translates a n-buffer to a (n+1)-buffer. An additional option type is
   returned to handle cases where the buffer contains an odd number of elements. *)

Equations buffer_halve {A lvl C} (b : buffer A lvl C) :
  { '(o, b') : option (prodN A lvl) * any_buffer A (S lvl) |
    buffer_seq b = option_seq o ++ any_buffer_seq b' } :=
buffer_halve B0 := ? (None, Any B0);
buffer_halve (B1 a) := ? (Some a, Any B0);
buffer_halve (B2 a b) := ? (None, Any (B1 (prodS a b)));
buffer_halve (B3 a b c) := ? (Some a, Any (B1 (prodS b c)));
buffer_halve (B4 a b c d) := ? (None, Any (B2 (prodS a b) (prodS c d)));
buffer_halve (B5 a b c d e) := ? (Some a, Any (B2 (prodS b c) (prodS d e))).

(* Takes any n-buffer and a green (n+1)-buffer, and rearranges elements
   contained in the two buffers to return a green n-buffer and a yellow
   (n+1)-buffer. The order of elements is preserved. *)

Equations green_prefix_concat {A lvl C}
  (buf1 : buffer A lvl C)
  (buf2 : buffer A (S lvl) green) :
  { '(buf1', buf2') : buffer A lvl green * yellow_buffer A (S lvl) |
    buffer_seq buf1 ++ buffer_seq buf2 =
    buffer_seq buf1' ++ yellow_buffer_seq buf2' } :=
green_prefix_concat buf1 buf2 with prefix_decompose buf1 => {
  | (? Ok buf) => ? (buf, Yellowish buf2);
  | (? Underflow opt) with green_pop buf2 => {
    | (? (ab, buf)) =>
        let '(? prefix) := prefix23 opt ab in
        ? (prefix, buf) };
  | (? Overflow buf ab) =>
    let '(? suffix) := green_push ab buf2 in
    ? (buf, suffix)
}.

(* Takes a green (n+1)-buffer and any n-buffer, and rearranges elements
   contained in the two buffers to return a yellow (n+1)-buffer and a green
   n-buffer. The order of elements is preserved. *)

Equations green_suffix_concat {A lvl C}
  (buf1 : buffer A (S lvl) green)
  (buf2 : buffer A lvl C) :
  { '(buf1', buf2') : yellow_buffer A (S lvl) * buffer A lvl green |
    buffer_seq buf1 ++ buffer_seq buf2 =
    yellow_buffer_seq buf1' ++ buffer_seq buf2' } :=
green_suffix_concat buf1 buf2 with suffix_decompose buf2 => {
  | ? Ok buf => ? (Yellowish buf1, buf);
  | ? Underflow opt with green_eject buf1 => {
    | ? (buf, ab) =>
        let '(? suffix) := suffix23 ab opt in
        ? (buf, suffix) };
  | ? Overflow buf ab =>
    let '(? prefix) := green_inject buf1 ab in
    ? (prefix, buf)
}.

(* Takes any n-buffer and a yellow (n+1)-buffer, and rearranges elements
   contained in the two buffers to return a green n-buffer and any (n+1)-buffer.
   The order of elements is preserved. *)

Equations yellow_prefix_concat {A lvl C}
  (buf1 : buffer A lvl C)
  (buf2 : yellow_buffer A (S lvl)) :
  { '(buf1', buf2') : buffer A lvl green * any_buffer A (S lvl) |
    buffer_seq buf1 ++ yellow_buffer_seq buf2 =
    buffer_seq buf1' ++ any_buffer_seq buf2' } :=
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

(* Takes a yellow (n+1)-buffer and any n-buffer, and rearranges elements
   contained in the two buffers to return any (n+1)-buffer and a green n-buffer.
   The order of elements is preserved. *)

Equations yellow_suffix_concat {A lvl C}
  (buf1 : yellow_buffer A (S lvl))
  (buf2 : buffer A lvl C) :
  { '(buf1', buf2') : any_buffer A (S lvl) * buffer A lvl green |
    yellow_buffer_seq buf1 ++ buffer_seq buf2 =
    any_buffer_seq buf1' ++ buffer_seq buf2' } :=
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

(* Creates a green colored deque from three options, two of level n and one of
   level n+1. *)

Equations cdeque_of_opt3 {A lvl} (o1 : option (prodN A lvl)) (o2 : option (prodN A (S lvl))) (o3 : option (prodN A lvl)) :
  { cd : chain A lvl green |
    chain_seq cd = option_seq o1 ++ option_seq o2 ++ option_seq o3 } :=
cdeque_of_opt3 None None None := ? Ending B0;
cdeque_of_opt3 (Some a) None None := ? Ending (B1 a);
cdeque_of_opt3 None None (Some a) := ? Ending (B1 a);
cdeque_of_opt3 (Some a) None (Some b) := ? Ending (B2 a b);
cdeque_of_opt3 None (Some (prodS a b)) None := ? Ending (B2 a b);
cdeque_of_opt3 (Some a) (Some (prodS b c)) None := ? Ending (B3 a b c);
cdeque_of_opt3 None (Some (prodS a b)) (Some c) := ? Ending (B3 a b c);
cdeque_of_opt3 (Some a) (Some (prodS b c)) (Some d) := ? Ending (B4 a b c d).

#[local] Obligation Tactic :=
  cbn; intros; destruct_prod; try (unfold id); try hauto db:rlist.

(* Takes a prefix buffer, a following buffer (when the next level is composed
   of only one buffer), and a suffix buffer. It allows to rearrange all
   elements contained in those buffers into a green cdeque. *)

Equations make_small {A lvl C1 C2 C3}
  (b1 : buffer A lvl C1)
  (b2 : buffer A (S lvl) C2)
  (b3 : buffer A lvl C3) :
  { cd : chain A lvl green |
    chain_seq cd = buffer_seq b1 ++ buffer_seq b2 ++ buffer_seq b3 } :=
make_small prefix1 buf suffix1 with (prefix_decompose prefix1), (suffix_decompose suffix1) => {
  | (? Underflow p1), (? Underflow s1) with buffer_unsandwich buf => {
    | ? Sandwich ab rest cd with prefix23 p1 ab, suffix23 cd s1 => {
      | ? prefix, ? suffix :=
        ? CGreen (PGreen prefix Hole suffix) (Ending rest) };
    | ? Alone opt with cdeque_of_opt3 p1 opt s1 => { | ? cd := ? cd } }
  | (? Underflow opt), (? Ok s1) with buffer_pop buf => {
    | ? None with opt => {
      | None := ? Ending s1;
      | Some x with buffer_push x s1 => { | ? cd := ? cd } };
    | ? Some (cd, Any rest) with prefix23 opt cd => {
      | ? prefix := ? CGreen (PGreen prefix Hole s1) (Ending rest) } };
  | (? Underflow opt), (? Overflow s1 ab) with suffix_rot buf ab => {
    | ? (cd, center) with prefix23 opt cd => {
      | ? prefix => ? CGreen (PGreen prefix Hole s1) (Ending center) } };
  | (? Ok p1), (? Underflow opt) with buffer_eject buf => {
    | ? None with opt => {
      | None := ? Ending p1;
      | Some x with buffer_inject p1 x => { | ? cd := ? cd } };
    | ? Some (Any rest, cd) with suffix23 cd opt => {
      | ? suffix := ? CGreen (PGreen p1 Hole suffix) (Ending rest) } };
  | (? Ok p1), (? Ok s1) :=
    ? CGreen (PGreen p1 Hole s1) (Ending buf);
  | (? Ok p1), (? Overflow s1 ab) with buffer_inject buf ab => {
    | ? rest => ? CGreen (PGreen p1 Hole s1) rest };
  | (? Overflow p1 ab), (? Underflow opt) with prefix_rot ab buf => {
    | ? (center, cd) with suffix23 cd opt => {
      | ? suffix => ? CGreen (PGreen p1 Hole suffix) (Ending center) } };
  | (? Overflow p1 ab), (? Ok s1) with buffer_push ab buf => {
    | ? rest => ? CGreen (PGreen p1 Hole s1) rest };
  | (? Overflow p1 ab), (? Overflow s1 cd) with buffer_halve buf => {
    | ? (x, Any rest) with suffix12 ab x => {
      | ? Yellowish prefix =>
        ? CGreen (PGreen p1 (PYellow prefix Hole (B1 cd)) s1) (Ending rest) } }
}.
Next Obligation.
  rewrite e1.
  aac_rewrite <-y.
  hauto db:rlist.
Qed.
Next Obligation.
  rewrite e1.
  aac_rewrite <-y.
  hauto db:rlist.
Qed.

#[local] Obligation Tactic :=
  try first [ done | hauto db:rlist |
  (* Introduce all the hypothesis. *)
  cbn; intros * Hpref * Hsuff *;
  autorewrite with rlist;
  (* Rewrite the beginning and the end of the sequence equality to match. *)
  aac_rewrite <-Hpref; aac_rewrite <-Hsuff;
  aac_normalise;
  (* Remove the beginning and the end of the sequence equality. *)
  do 3 apply <-app_inv_head_iff;
  apply app_inv_tail_iff;
  reflexivity ].

(* Takes a red cdeque and returns a green one representing the same set. *)

Equations green_of_red {A lvl} (cd : chain A lvl red) :
  { cd' : chain A lvl green | chain_seq cd' = chain_seq cd } :=
green_of_red (CRed (PRed p1 Hole s1) (Ending buf))
  with make_small p1 buf s1 => { | ? cd' := ? cd' };
green_of_red (CRed (PRed p1 (PYellow p2 child s2) s1) cd)
  with yellow_prefix_concat p1 (Yellowish p2) => {
    | ? (p1', Any p2') with yellow_suffix_concat (Yellowish s2) s1 => {
      | ? (Any s2', s1') :=
        ? CGreen (PGreen p1' Hole s1') (CRed (PRed p2' child s2') cd) } };
green_of_red (CRed (PRed p1 Hole s1) (CGreen (PGreen p2 child s2) cd))
  with green_prefix_concat p1 p2, green_suffix_concat s2 s1 => {
  | ? (p1', Yellowish p2'), ? (Yellowish s2', s1') :=
    ? CGreen (PGreen p1' (PYellow p2' child s2') s1') cd }.
Next Obligation. Qed.
Next Obligation. Qed.

#[local] Obligation Tactic :=
  try first [ done | hauto db:rlist ].

(* Takes a green or red cdeque, and returns a green one representing
   the same set. *)

Equations ensure_green {A lvl G R} (cd : chain A lvl (Mix G NoYellow R)) :
  { cd' : chain A lvl green | chain_seq cd' = chain_seq cd } :=
ensure_green (Ending buf) := ? Ending buf;
ensure_green (CGreen x cd) := ? CGreen x cd;
ensure_green (CRed x cd) := green_of_red (CRed x cd).

(* Takes a yellow packet, as a prefix buffer, a child packet and a suffix
   buffer, and a green or red cdeque. Returns a deque starting with this packet
   and followed by the green version of the input colored deque. *)

Equations make_yellow {A tlvl} {G1 Y1 Y2 G3 Y3 G4 R4}
  (buf1 : buffer A 0 (Mix G1 Y1 NoRed))
  (p : packet A 1 tlvl (Mix NoGreen Y2 NoRed))
  (buf2 : buffer A 0 (Mix G3 Y3 NoRed))
  (cd : chain A tlvl (Mix G4 NoYellow R4)) :
  { sq : deque A |
    deque_seq sq =
               buffer_seq buf1 ++
               packet_front_seq p ++
               chain_seq cd ++
               packet_rear_seq p ++
               buffer_seq buf2 }
:=
make_yellow p1 child s1 cd with ensure_green cd => {
  | ? cd' => ? T (CYellow (PYellow p1 child s1) cd') }.

(* Takes a red packet, as a prefix buffer, a child packet and a suffix
   buffer, and a green cdeque. Returns the green version of the colored deque
   made of the red packet followed by the green cdeque. *)

Equations make_red {A tlvl} {C1 Y2 C3}
  (buf1 : buffer A 0 C1)
  (p : packet A 1 tlvl (Mix NoGreen Y2 NoRed))
  (buf2 : buffer A 0 C3)
  (cd : chain A tlvl green) :
  { sq : deque A |
    deque_seq sq =
               buffer_seq buf1 ++
               packet_front_seq p ++
               chain_seq cd ++
               packet_rear_seq p ++
               buffer_seq buf2 }
:=
make_red p1 child s1 cd with green_of_red (CRed (PRed p1 child s1) cd) => {
  | ? cd' => ? T cd' }.

(* Pushes an element on a deque. *)

Equations push {A: Type} (x : A) (sq : deque A) :
  { sq' : deque A | deque_seq sq' = [x] ++ deque_seq sq }
:=
push x (T (Ending buf)) with buffer_push (prodZ x) buf => {
  | ? buf' => ? T buf' };
push x (T (CGreen (PGreen p1 child s1) dq))
  with green_push (prodZ x) p1 => {
    | ? Yellowish buf' with make_yellow buf' child s1 dq => {
      | ? sq' => ? sq' } };
push x (T (CYellow (PYellow p1 child s1) dq))
  with yellow_push (prodZ x) (Yellowish p1) => {
  | ? (Any p1') with make_red p1' child s1 dq => {
    | ? sq' => ? sq' } }.

(* Injects an element on a deque. *)

Equations inject {A: Type} (sq : deque A) (x : A) :
  { sq' : deque A | deque_seq sq' = deque_seq sq ++ [x] }
:=
inject (T (Ending buf)) x with buffer_inject buf (prodZ x) => {
  | ? buf' => ? T buf' };
inject (T (CGreen (PGreen p1 child s1) cd)) x
  with green_inject s1 (prodZ x) => {
    | ? Yellowish buf' with make_yellow p1 child buf' cd => {
      | ? sq' => ? sq' } };
inject (T (CYellow (PYellow p1 child s1) cd)) x
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
pop (T (Ending buf)) with buffer_pop buf => {
  pop _ (? None) := ? None;
  pop _ (? Some (prodZ x, Any buf')) := ? Some (x, T (Ending buf'))
};
pop (T (CGreen (PGreen p1 child s1) cd)) with green_pop p1 => {
  | ? (prodZ x, Yellowish p1') with make_yellow p1' child s1 cd => {
    | ? sq' => ? Some (x, sq') } };
pop (T (CYellow (PYellow p1 child s1) cd))
  with yellow_pop (Yellowish p1) => {
    | ? (prodZ x, Any p1') with make_red p1' child s1 cd => {
      | ? sq' => ? Some (x, sq') } }.

(* Ejects an element from a deque. *)

Equations eject {A : Type} (sq : deque A) :
  { o : option (deque A * A) |
    deque_seq sq = match o with
               | None => []
               | Some (sq', x) => deque_seq sq' ++ [x]
               end } :=
eject (T (Ending buf)) with buffer_eject buf => {
  eject _ (? None) := ? None;
  eject _ (? Some (Any buf', prodZ x)) := ? Some (T (Ending buf'), x)
};
eject (T (CGreen (PGreen p1 child s1) cd)) with green_eject s1 => {
  | ? (Yellowish s1', prodZ x) with make_yellow p1 child s1' cd => {
    | ? sq' => ? Some (sq', x) } };
eject (T (CYellow (PYellow p1 child s1) cd))
  with yellow_eject (Yellowish s1) => {
    | ? (Any s1', prodZ x) with make_red p1 child s1' cd => {
      | ? sq' => ? Some (sq', x) } }.