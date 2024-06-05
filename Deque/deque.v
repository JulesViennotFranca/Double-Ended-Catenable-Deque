From Coq Require Import ssreflect.
From Coq Require Import Program List ZArith Lia.
Import ListNotations.
From Equations Require Import Equations.
From Hammer Require Import Tactics.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Deque Require Import buffer.

(* Types *)

Inductive preferred_child : Type :=
  | Preferred : bool -> bool -> preferred_child.

Inductive kind : Type := Only | Left | Right.

(* Here, [green_hue], [yellow_hue], [orange_hue] and [red_hue] will be utilized 
   to generate the colors essential for our program. They function as boolean 
   variables, indicating whether or not a specific hue is present in our color. *)

Inductive green_hue  : Type := SomeGreen  | NoGreen.
Inductive yellow_hue : Type := SomeYellow | NoYellow.
Inductive orange_hue : Type := SomeOrange | NoOrange.
Inductive red_hue    : Type := SomeRed    | NoRed.

(* Colors are generated through the constructor [Mix], which accepts amount 
   of each hue as arguments. *)

Inductive color : Type :=
  | Mix : green_hue -> yellow_hue -> orange_hue -> red_hue -> color.

(* In order for [Equations] to work on hues and colors, instances of 
   [NoConfusion] are added to these types. *)

Derive NoConfusion for kind.
Derive NoConfusion for green_hue.
Derive NoConfusion for yellow_hue.
Derive NoConfusion for orange_hue.
Derive NoConfusion for red_hue.
Derive NoConfusion for color.

(* Some basic colors that we'll need. *)

Notation green := (Mix SomeGreen NoYellow NoOrange NoRed).
Notation yellow := (Mix NoGreen SomeYellow NoOrange NoRed).
Notation yellorange := (Mix NoGreen SomeYellow SomeOrange NoRed).
Notation orange := (Mix NoGreen NoYellow SomeOrange NoRed).
Notation red := (Mix NoGreen NoYellow NoOrange SomeRed).

(* Types for general prefix and suffix, they are simply aliases for buffer.t. *)

Definition prefix' := buffer.t.
Definition suffix' := buffer.t.

Inductive small_triple_size : nat -> nat -> kind -> Type :=
  | POnly {q : nat} : small_triple_size (S q) 0 Only
  | PLeft {q : nat} : small_triple_size (5 + q) 2 Left
  | PRight {q : nat} : small_triple_size 2 (5 + q) Right.

Inductive big_triple_size : nat -> nat -> nat -> kind -> Type :=
  | BOnly {p qp qs : nat} : big_triple_size p (p + qp) (p + qs) Only
  | BLeft {p q : nat} : big_triple_size p (p + q) 2 Left
  | BRight {p q : nat} : big_triple_size p 2 (p + q) Right.

Inductive stored_triple (A : Type) : nat -> Type :=
  | ST_ground : A -> stored_triple A 0
  | ST_small {lvl q : nat} : 
      prefix' (stored_triple A lvl) (3 + q) -> 
      stored_triple A (S lvl)
  | ST_triple {lvl qp qs : nat} {C : color} :
      prefix' (stored_triple A lvl) (3 + qp) -> 
      cdeque A (S lvl) C -> 
      suffix' (stored_triple A lvl) (3 + qs) -> 
      stored_triple A (S lvl)

with triple (A : Type) : nat -> nat -> bool -> kind -> kind -> color -> Type :=
  | Hole {lvl : nat} {K : kind} : 
      triple A lvl 0 true K K yellorange
  | Small {lvl qp qs : nat} {K : kind} : 
      prefix' (stored_triple A lvl) qp -> 
      suffix' (stored_triple A lvl) qs ->
      small_triple_size qp qs K ->
      triple A lvl 0 false K K green
  | Green {lvl qp qs : nat} {K : kind} {G R} :
      prefix' (stored_triple A lvl) qp ->
      cdeque A (S lvl) (Mix G NoYellow NoOrange R) ->
      suffix' (stored_triple A lvl) qs ->
      big_triple_size 8 qp qs K ->
      triple A lvl 0 false K K green
  | Yellow {lvl len qp qs : nat} {K1 K2 : kind} :
      prefix' (stored_triple A lvl) qp ->
      packet A (S lvl) len (Preferred true false) K2 ->
      suffix' (stored_triple A lvl) qs ->
      big_triple_size 7 qp qs K1 ->
      triple A lvl (S len) false K1 K2 yellow
  | Orange {lvl len qp qs : nat} {K1 K2 : kind} :
      prefix' (stored_triple A lvl) qp ->
      packet A (S lvl) len (Preferred false true) K2 ->
      suffix' (stored_triple A lvl) qs ->
      big_triple_size 6 qp qs K1 ->
      triple A lvl (S len) false K1 K2 orange
  | Red {lvl qp qs : nat} {K : kind} :
      prefix' (stored_triple A lvl) qp ->
      cdeque A (S lvl) green ->
      suffix' (stored_triple A lvl) qs ->
      big_triple_size 5 qp qs K ->
      triple A lvl 0 false K K red

with packet (A : Type) : nat -> nat -> preferred_child -> kind -> Type :=
  | Only_child {lvl len : nat} {is_hole : bool} {K : kind} {Y O} {left right : bool} :
      triple A lvl len is_hole Only K (Mix NoGreen Y O NoRed) ->
      packet A lvl len (Preferred left right) K
  | Left_child {lvl len : nat} {is_hole : bool} {K : kind} {Y O C} :
      triple A lvl len is_hole Left K (Mix NoGreen Y O NoRed) ->
      path A lvl Right C ->
      packet A lvl len (Preferred true false) K
  | Right_child {lvl len : nat} {is_hole : bool} {K : kind} {Y O} :
      path A lvl Left green ->
      triple A lvl len is_hole Right K (Mix NoGreen Y O NoRed) ->
      packet A lvl len (Preferred false true) K

with path (A : Type) : nat -> kind -> color -> Type := 
  | Children {lvl len nlvl : nat} {is_hole : bool} {K1 K2 : kind} {G Y O R} :
      triple A lvl len is_hole K1 K2 (Mix NoGreen Y O NoRed) ->
      triple A nlvl 0 false K2 K2 (Mix G NoYellow NoOrange R) ->
      nlvl = len + lvl ->
      path A lvl K1 (Mix G NoYellow NoOrange R)

with cdeque (A : Type) : nat -> color -> Type :=
  | Empty {lvl : nat} : cdeque A lvl green 
  | Only_path {lvl : nat} {G R} :
      path A lvl Only (Mix G NoYellow NoOrange R) ->
      cdeque A lvl (Mix G NoYellow NoOrange R)
  | Pair_green {lvl : nat} :
      path A lvl Left green ->
      path A lvl Right green ->
      cdeque A lvl green
  | Pair_red {lvl : nat} {Cl Cr : color} :
      path A lvl Left Cl ->
      path A lvl Right Cr ->
      cdeque A lvl red.

Arguments ST_ground {A}.
Arguments ST_small {A lvl q}.
Arguments ST_triple {A lvl qp qs C}.

Arguments Hole {A lvl K}.
Arguments Small {A lvl qp qs K}.
Arguments Green {A lvl qp qs K G R}.
Arguments Yellow {A lvl len qp qs K1 K2}.
Arguments Orange {A lvl len qp qs K1 K2}.
Arguments Red {A lvl qp qs K}.

Arguments Only_child {A lvl len is_hole K Y O left right}.
Arguments Left_child {A lvl len is_hole K Y O C}.
Arguments Right_child {A lvl len is_hole K Y O}.

Arguments Children {A lvl len nlvl is_hole K1 K2 G Y O R}.

Arguments Empty {A lvl}.
Arguments Only_path {A lvl G R}.
Arguments Pair_green {A lvl}.
Arguments Pair_red {A lvl Cl Cr}.

Definition prefix (A : Type) (lvl : nat) := prefix' (stored_triple A lvl).
Definition suffix (A : Type) (lvl : nat) := suffix' (stored_triple A lvl).

Definition only_triple (A : Type) (lvl len : nat) (is_hole : bool) := 
  triple A lvl len is_hole Only.
Definition left_triple (A : Type) (lvl len : nat) (is_hole : bool) := 
  triple A lvl len is_hole Left.
Definition right_triple (A : Type) (lvl len : nat) (is_hole : bool) := 
  triple A lvl len is_hole Right.

Inductive sdeque (A : Type) (lvl : nat) : Type :=
  Sd : forall (C : color), cdeque A lvl C -> sdeque A lvl.
Arguments Sd {A lvl C}.

Inductive deque (A : Type) : Type :=
  T : cdeque A 0 green -> deque A.
Arguments T {A}.

(* Models *)

Set Equations Transparent.

Parameter stored_triple_seq : 
  forall {A lvl}, stored_triple A lvl -> list A.

Equations prefix_seq {A lvl q} : prefix A lvl q -> list A :=
prefix_seq p := concat (map stored_triple_seq (buffer.seq p)).

Equations suffix_seq {A lvl q} : suffix A lvl q -> list A :=
suffix_seq s := concat (map stored_triple_seq (buffer.seq s)).

Parameter triple_front_seq :
  forall {A lvl len is_hole K1 K2 C}, 
  triple A lvl len is_hole K1 K2 C -> list A.

Parameter triple_rear_seq :
  forall {A lvl len is_hole K1 K2 C}, 
  triple A lvl len is_hole K1 K2 C -> list A.

Equations triple_seq {A lvl len is_hole K1 K2 C} : 
  triple A lvl len is_hole K1 K2 C -> list A :=
triple_seq t := triple_front_seq t ++ triple_rear_seq t.

Equations path_seq {A lvl K C} : path A lvl K C -> list A :=
path_seq (Children nchild achild _) := 
  triple_front_seq nchild ++ triple_seq achild ++ triple_rear_seq nchild.

Equations cdeque_seq {A lvl C} : cdeque A lvl C -> list A :=
cdeque_seq Empty := [];
cdeque_seq (Only_path p) := path_seq p;
cdeque_seq (Pair_green p1 p2) := path_seq p1 ++ path_seq p2;
cdeque_seq (Pair_red p1 p2) := path_seq p1 ++ path_seq p2.

Equations packet_front_seq {A lvl len pc K} : packet A lvl len pc K -> list A :=
packet_front_seq (Only_child child) := triple_front_seq child;
packet_front_seq (Left_child child _) := triple_front_seq child;
packet_front_seq (Right_child path child) := path_seq path ++ triple_front_seq child.

Equations packet_rear_seq {A lvl len pc K} : packet A lvl len pc K -> list A :=
packet_rear_seq (Only_child child) := triple_rear_seq child;
packet_rear_seq (Left_child child path) := triple_rear_seq child ++ path_seq path;
packet_rear_seq (Right_child _ child) := triple_rear_seq child.

Equations deque_seq {A} : deque A -> list A :=
deque_seq (T cd) := cdeque_seq cd.

Unset Equations Transparent.

Axiom stored_triple_small : forall [A lvl q], forall 
  (p : prefix A lvl (3 + q)),
  stored_triple_seq (ST_small p) = prefix_seq p.
  
Axiom stored_triple_triple : forall [A lvl qp qs C], forall 
  (p : prefix A lvl (3 + qp)) 
  (cd : cdeque A (S lvl) C) 
  (s : suffix A lvl (3 + qs)),
  stored_triple_seq (ST_triple p cd s) =
    prefix_seq p ++ cdeque_seq cd ++ suffix_seq s.

Axiom triple_front_hole : forall (A : Type) (lvl : nat) (K : kind), 
  triple_front_seq (A := A) (lvl := lvl) (K1 := K) Hole = [].

Axiom triple_rear_hole : forall (A : Type) (lvl : nat) (K : kind), 
  triple_rear_seq (A := A) (lvl := lvl) (K1 := K) Hole = [].

Axiom triple_front_small : forall [A lvl qp qs K], forall
  (p : prefix A lvl qp)
  (s : suffix A lvl qs)
  (ss : small_triple_size qp qs K),
  triple_front_seq (Small p s ss) = prefix_seq p.

Axiom triple_rear_small : forall [A lvl qp qs K], forall 
  (p : prefix A lvl qp)
  (s : suffix A lvl qs)
  (ss : small_triple_size qp qs K),
  triple_rear_seq (Small p s ss) = suffix_seq s.

Axiom triple_front_green : forall [A lvl qp qs K G R], forall
  (p : prefix A lvl qp)
  (cd : cdeque A (S lvl) (Mix G NoYellow NoOrange R))
  (s : suffix A lvl qs)
  (bs : big_triple_size 8 qp qs K),
  triple_front_seq (Green p cd s bs) = prefix_seq p ++ cdeque_seq cd.

Axiom triple_rear_green : forall [A lvl qp qs K G R], forall
  (p : prefix A lvl qp)
  (cd : cdeque A (S lvl) (Mix G NoYellow NoOrange R))
  (s : suffix A lvl qs)
  (bs : big_triple_size 8 qp qs K),
  triple_rear_seq (Green p cd s bs) = suffix_seq s.

Axiom triple_front_yellow : forall [A lvl len qp qs K1 K2], forall
  (p : prefix A lvl qp)
  (pkt : packet A (S lvl) len (Preferred true false) K2)
  (s : suffix A lvl qs)
  (bs : big_triple_size 7 qp qs K1),
  triple_front_seq (Yellow p pkt s bs) =
    prefix_seq p ++ packet_front_seq pkt.

Axiom triple_rear_yellow : forall [A lvl len qp qs K1 K2], forall
  (p : prefix A lvl qp)
  (pkt : packet A (S lvl) len (Preferred true false) K2)
  (s : suffix A lvl qs)
  (bs : big_triple_size 7 qp qs K1),
  triple_rear_seq (Yellow p pkt s bs) =
    packet_rear_seq pkt ++ suffix_seq s.

Axiom triple_front_orange : forall [A lvl len qp qs K1 K2], forall
  (p : prefix A lvl qp)
  (pkt : packet A (S lvl) len (Preferred false true) K2)
  (s : suffix A lvl qs)
  (bs : big_triple_size 6 qp qs K1),
  triple_front_seq (Orange p pkt s bs) =
    prefix_seq p ++ packet_front_seq pkt.

Axiom triple_rear_orange : forall [A lvl len qp qs K1 K2], forall
  (p : prefix A lvl qp)
  (pkt : packet A (S lvl) len (Preferred false true) K2)
  (s : suffix A lvl qs)
  (bs : big_triple_size 6 qp qs K1),
  triple_rear_seq (Orange p pkt s bs) =
    packet_rear_seq pkt ++ suffix_seq s.

Axiom triple_front_red : forall [A lvl qp qs K], forall
  (p : prefix A lvl qp)
  (cd : cdeque A (S lvl) green)
  (s : suffix A lvl qs)
  (bs : big_triple_size 5 qp qs K),
  triple_front_seq (Red p cd s bs) = prefix_seq p ++ cdeque_seq cd.

Axiom triple_rear_red : forall [A lvl qp qs K], forall
  (p : prefix A lvl qp)
  (cd : cdeque A (S lvl) green)
  (s : suffix A lvl qs)
  (bs : big_triple_size 5 qp qs K),
  triple_rear_seq (Red p cd s bs) = suffix_seq s.

(* The list application is made opaque. *)

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

#[export] Hint Rewrite stored_triple_small : rlist.
#[export] Hint Rewrite stored_triple_triple : rlist.
#[export] Hint Rewrite triple_front_hole : rlist.
#[export] Hint Rewrite triple_rear_hole : rlist.
#[export] Hint Rewrite triple_front_small : rlist.
#[export] Hint Rewrite triple_rear_small : rlist.
#[export] Hint Rewrite triple_front_green : rlist.
#[export] Hint Rewrite triple_rear_green : rlist.
#[export] Hint Rewrite triple_front_yellow : rlist.
#[export] Hint Rewrite triple_rear_yellow : rlist.
#[export] Hint Rewrite triple_front_orange : rlist.
#[export] Hint Rewrite triple_rear_orange : rlist.
#[export] Hint Rewrite triple_front_red : rlist.
#[export] Hint Rewrite triple_rear_red : rlist.

(* Lemmas *)

Lemma empty_prefix [A lvl] (p : prefix A lvl 0) : prefix_seq p = [].
Proof.
  unfold prefix_seq; unfold prefix, prefix' in p.
  pose buffer.empty_buffer as H; rewrite H.
  reflexivity.
Qed.

Lemma empty_suffix [A lvl] (s : suffix A lvl 0) : suffix_seq s = [].
Proof. 
  unfold suffix_seq; unfold suffix, suffix' in s. 
  pose buffer.empty_buffer as H; rewrite H.
  reflexivity.
Qed.

#[export] Hint Rewrite empty_buffer : rlist.

#[local] Obligation Tactic :=
  try first [ done | cbn; hauto db:rlist ].

Notation "? x" := (@exist _ _ x _) (at level 100).

(* Elements *)

Equations empty {A} : { d : deque A | deque_seq d = [] } :=
empty := ? T Empty.

(* Functions *)

Equations push_only_triple {A lvl len K C}
  (x : stored_triple A lvl) 
  (t : only_triple A lvl len false K C) :
  { t' : only_triple A lvl len false K C | 
    triple_seq t' = stored_triple_seq x ++ triple_seq t } :=
push_only_triple x (Small p s POnly) with buffer.push x p => {
  | ? p' := ? Small p' s POnly };
push_only_triple x (Green p cd s BOnly) with buffer.push x p => {
  | ? p' := ? Green p' cd s BOnly };
push_only_triple x (Yellow p cd s BOnly) with buffer.push x p => {
  | ? p' := ? Yellow p' cd s BOnly };
push_only_triple x (Orange p cd s BOnly) with buffer.push x p => {
  | ? p' := ? Orange p' cd s BOnly };
push_only_triple x (Red p cd s BOnly) with buffer.push x p => {
  | ? p' := ? Red p' cd s BOnly }.
Next Obligation.
  cbn; intros * Hbuf *; simp triple_seq.
  autorewrite with rlist; simp prefix_seq; hauto db:rlist.
Qed.
Next Obligation.
  cbn; intros * Hbuf *; simp triple_seq.
  autorewrite with rlist; simp prefix_seq; hauto db:rlist.
Qed.
Next Obligation.
  cbn; intros * Hbuf *; simp triple_seq.
  autorewrite with rlist; simp prefix_seq; hauto db:rlist.
Qed.
Next Obligation.
  cbn; intros * Hbuf *; simp triple_seq.
  autorewrite with rlist; simp prefix_seq; hauto db:rlist.
Qed.
Next Obligation.
  cbn; intros * Hbuf *; simp triple_seq.
  autorewrite with rlist; simp prefix_seq; hauto db:rlist.
Qed.

Equations inject_only_triple {A lvl len K C}
  (t : only_triple A lvl len false K C)
  (x : stored_triple A lvl) :
  { t' : only_triple A lvl len false K C | 
    triple_seq t' = triple_seq t ++ stored_triple_seq x } :=
inject_only_triple (Small p s POnly) x with buffer.inject p x => {
  | ? p' := ? Small p' s POnly };
inject_only_triple (Green p cd s BOnly) x with buffer.inject s x => {
  | ? s' := ? Green p cd s' BOnly };
inject_only_triple (Yellow p cd s BOnly) x with buffer.inject s x => {
  | ? s' := ? Yellow p cd s' BOnly };
inject_only_triple (Orange p cd s BOnly) x with buffer.inject s x => {
  | ? s' := ? Orange p cd s' BOnly };
inject_only_triple (Red p cd s BOnly) x with buffer.inject s x => {
  | ? s' := ? Red p cd s' BOnly }.
Next Obligation.
  cbn; intros * Hbuf *; simp triple_seq.
  autorewrite with rlist; simp prefix_seq; hauto db:rlist.
Qed.
Next Obligation.
  cbn; intros * Hbuf *; simp triple_seq.
  autorewrite with rlist; simp prefix_seq; hauto db:rlist.
Qed.
Next Obligation.
  cbn; intros * Hbuf *; simp triple_seq.
  autorewrite with rlist; simp prefix_seq; hauto db:rlist.
Qed.
Next Obligation.
  cbn; intros * Hbuf *; simp triple_seq.
  autorewrite with rlist; simp prefix_seq; hauto db:rlist.
Qed.
Next Obligation.
  cbn; intros * Hbuf *; simp triple_seq.
  autorewrite with rlist; simp prefix_seq; hauto db:rlist.
Qed.

Equations push_only_path {A lvl C} 
  (x : stored_triple A lvl) 
  (p : path A lvl Only C) :
  { p' : path A lvl Only C | path_seq p' = stored_triple_seq x ++ path_seq p } :=
push_only_path x (Children Hole adoptive eq_refl) with push_only_triple x adoptive => {
  | ? adoptive' := ? Children Hole adoptive' eq_refl };
push_only_path x (Children natural adoptive eq_refl) with push_only_triple x natural => {
  | ? natural' := ? Children natural' adoptive eq_refl }.
Next Obligation.
  cbn; intros * Hpnat *; simp triple_seq in *; autorewrite with rlist in *. 


let push_only_path
: type a c. a -> (a, c, only) path -> (a, c, only) path
= fun x (Path (only, kont)) ->
  match is_hole only, only with
  | Is_hole, HOLE -> Path (only, push_only_triple x kont)
  | Not_hole, _   -> Path (push_only_triple x only, kont)