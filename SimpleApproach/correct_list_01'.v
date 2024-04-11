From Coq Require Import ssreflect.
From Coq Require Import List.
Import ListNotations.
From Equations Require Import Equations.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.
From Hammer Require Import Tactics.

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

(* The lemma [app_cons_one] is trivial but it is mandatory as ++ is later made
   opaque. *)

Lemma app_cons_one [A : Type] (a : A) (l : list A) : a :: l = [a] ++ l.
Proof.
  reflexivity.
Qed.

Opaque app.
Definition singleton {A : Type} (x : A) : list A := [x].
Opaque singleton.

(* A [power] function on types, with the product as iterated function. *)

Fixpoint power (A : Type) (n : nat) : Type := 
  match n with 
  | 0 => A 
  | S n => power (A * A) n
  end.

(* The type [packet] denotes lists of ones preceded by a head. Structurally, 
   it encompasses the empty list, [Hole], as well as lists of the format 011...1, 
   111...1, and 211...1, with their respective heads determined by the 
   corresponding constructor.

   Here, 0, 1 and 2 correspond to the list of elements contained at this 'bit'.
   And at each 'bit', the 'size' of elements contained doubles. For example, if
   we starts with elements of type A, the rest of the packet starts with 
   elements of type (A * A). The type [In] and the natural number [length] 
   derive from this behavior, [In] being the type of elements at the beginning, 
   and [length] serving at counting how many times the size of elements doubles.
   At the list's end, elements will have size power In length.

   A color is linked to a packet, providing insights into the head. An uncolored 
   list is empty, a green one begins with 0, a yellow one with 1, and a red one 
   with 2.

   Then, to express that 0, 1, and 2 are solely followed by 1s or nothing, we 
   leverage information provided by colors. If the constructor parameter is 
   yellow, it implies 1s are following; if it is uncolored, nothing follows, 
   thereby concluding the list.

   To ensure the parameter is either yellow or uncolored, we employ an implicit 
   variable [YellowAmount] of type [yellow_hue]. This variable may be either 
   [SomeYellow] or [NoYellow], resulting in either yellow or uncolored outcomes. *)

Definition yellow_or_uncolored : yellow_hue -> color := 
  fun YellowAmount => Mix NoGreen YellowAmount NoRed.

Inductive packet : forall (In : Type) (length : nat), color -> Type :=
  | Hole {A} : packet A 0 uncolored
  | Zero {A n} : forall {YellowAmount}, 
                  packet (A * A) n (yellow_or_uncolored YellowAmount) ->
                   packet A (S n) green
  | One {A n} : forall {YellowAmount}, 
                 A ->
                  packet (A * A) n (yellow_or_uncolored YellowAmount) ->
                   packet A (S n) yellow
  | Two {A n} : forall {YellowAmount}, 
                 A ->
                  A -> 
                   packet (A * A) n (yellow_or_uncolored YellowAmount) ->
                    packet A (S n) red.

(* The function [flatten] transform a list of pairs into a list of single 
   elements, preserving their order. *)

Fixpoint flatten {A : Type} (l : list (A * A)) : list A :=
  match l with 
  | [] => []
  | (a1, a2) :: l => [a1] ++ [a2] ++ (flatten l)
  end.

(* The lemma [flatten_app] ensure the distributivity of flatten over ++. *)

Lemma flatten_app [A : Type] (l1 l2 : list (A * A)) : 
    flatten (l1 ++ l2) = flatten l1 ++ flatten l2.
Proof.
  induction l1 as [ | (a, b) l1].
  - eauto.
  - rewrite <- app_comm_cons.
    simpl.
    rewrite IHl1.
    aac_reflexivity.
Qed.

(* To help automatize proofs, we design a list of useful tactics. *)

#[export] Hint Rewrite <-app_comm_cons : rlist.
#[export] Hint Rewrite <-app_cons_one : rlist.
#[export] Hint Rewrite flatten_app : rlist.

#[local] Obligation Tactic :=
  try first [ done | hauto db:rlist ].

(* The function [packet_value] gives the list stored in a packet. *)

Fixpoint packet_value {A : Type} {n : nat} {c : color} (p : packet A n c) : 
    list A := 
  match p with 
  | Hole => []
  | Zero ones => flatten (packet_value ones)
  | One a ones => [a] ++ flatten (packet_value ones)
  | Two a b ones => [a] ++ [b] ++ flatten (packet_value ones)
  end.

(* The type [colored_list] denotes lists represented in redundant binary form, 
   embellished with colors representing the ease of adding elements to the list.

   In a green colored list, adding one element can be done effortlessly. In a 
   yellow one, it requires some rearrangements, while in a red one, it isn't 
   possible to add an element in constant time.

   Formally, a colored list is simply a recursive list of packet, terminated 
   by [Null]. However, we have to make sure the type of the rest of the colored
   list is the same as the one at the exit of the first packet. The integer [n] 
   introduced in the color constructor ensure that. This maintains the behavior
   of packets where the size of elements contained from a bit to the next 
   doubles.
   
   For example, as a redundant representation of 10 can be 012, the list 
   [1; 2; 3; 4; 5; 6; 7; 8; 9; 10] in redundant form is 
   [; [(1, 2); [((3, 4), (5, 6)); ((7, 8), (9, 10))]]]. 
   And as a colored list, it would give us a list of 2 packets:
   [; [(1, 2); []]] ++ [((3, 4), (5, 6)); ((7, 8), (9, 10)); []] ++ Null.

   A green colored list is one that commences with a green packet, and likewise 
   for yellow or red ones.

   However, we impose different conditions on the tail of a colored list 
   (understood as the tail in the sense of a colored list as a list of packet). 
   For a red colored list, we require the tail to be green, which is 
   straightforward.

   However, for green and yellow colored lists, the color of the tail is more 
   nuanced. We don't want it to be yellow (= starting with 1s). To address this, 
   we utilize implicit variables [GreenAmount] and [RedAmount] of corresponding 
   hues. This yields four potential colors, but as we only declare green, yellow, 
   and red colored lists, [Equations] will discard the two impossible colors, 
   leaving us with a green or red tail. *)

Definition not_yellow : green_hue -> red_hue -> color := 
  fun GreenAmount RedAmount => Mix GreenAmount NoYellow RedAmount.

Inductive next : color -> color -> Prop := 
  | FromGreen {GreenAmount RedAmount} : next green (not_yellow GreenAmount RedAmount) 
  | FromYellow {GreenAmount RedAmount} : next yellow (not_yellow GreenAmount RedAmount)  
  | FromRed : next red green.

Inductive colored_list : Type -> color -> Type :=
  | Null {A} : colored_list A green
  | Cons {A n} : forall {c1 c2 : color}, 
                  packet A n c1 ->
                   colored_list (power A n) c2 -> 
                    next c1 c2 -> 
                     colored_list A c1.
Arguments Cons {A n c1 c2} p clist {next}. 

(* The function [flattenN] is simply a generalization of [flatten], to apply it 
   n times, where n is the number of times the size of element is doubled. *)

Equations flattenN {A : Type} (n : nat) : list (power A n) -> list A :=
flattenN 0 l := l;
flattenN (S n) l := 
    let l' := flattenN n l in 
    flatten l'.
Transparent flattenN.
Arguments flattenN {A n} l. 

(* The function [colored_list_value] returns the list represented by a colored
   list.

   Since a colored list is essentially several consecutive packets, we initially
   calculate the list [l1] represented by the head. Then, by induction, we can 
   compute the list [l2] represented by the tail. Finally, thanks to relation
   on types, we know that [l1] has type [list A], and [l2] has type 
   [list (power A n)], for some n. The function flattenN will be able to derive
   this n from the context, and transform [l2] in a list of elements of type A.
   We just have to merge the two list and we have our final list.

   Applying our algorithm manually on a list of 10 elements:
   - Null -> [];
   - [((3, 4), (5, 6)); ((7, 8), (9, 10)); []] ++ Null ->
        ([((3, 4), (5, 6))] ++ [((7, 8), (9, 10))] ++ []) ++ flattenN [] 
        = [((3, 4), (5, 6)); ((7, 8), (9, 10))];
   - [; [(1, 2); []]] ++ [((3, 4), (5, 6)); ((7, 8), (9, 10)); []] ++ Null ->
        (flatten [(1, 2)]) ++ flattenN [((3, 4), (5, 6)); ((7, 8), (9, 10))]
        = [1; 2] ++ [3; 4; 5; 6; 7; 8; 9; 10]
        = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]. *)

Fixpoint colored_list_value {A : Type} {c : color} (clist : colored_list A c) : 
    list A :=
  match clist with 
  | Null => []
  | Cons p clist => 
      let l1 := packet_value p in 
      let l2 := colored_list_value clist in 
      l1 ++ flattenN l2
  end.

Notation "? x" := (@exist _ _ x _) (at level 100).

(* The function [ensure_green] takes a green or red colored list and returns 
   a green one representing the same list. *)

Equations ensure_green {A : Type} {GreenAmount RedAmount} 
    (clist : colored_list A (Mix GreenAmount NoYellow RedAmount)) :
        { glist : colored_list A green | 
            colored_list_value glist = colored_list_value clist } :=
ensure_green Null := ? Null;
ensure_green (Cons (Zero ones) clist) := ? Cons (Zero ones) clist;
ensure_green (Cons (Two a b Hole) Null) := ? Cons (Zero (One (a, b) Hole)) Null;
ensure_green (Cons (Two a b Hole) (Cons (Zero ones) clist)) := 
    ? Cons (Zero (One (a, b) ones)) clist;
ensure_green (Cons (Two a b (One (c, d) ones)) clist) := 
    ? Cons (Zero Hole) (Cons (Two (a, b) (c, d) ones) clist).

(* Lastly, the type [blist] will denote lists represented in redundant binary 
   form where the addition of one element in constant time is possible.

   We employ the same method as before to exclusively select green and yellow 
   colored lists. *)

Definition not_red : green_hue -> yellow_hue -> color := 
  fun GreenAmount YellowAmount => Mix GreenAmount YellowAmount NoRed.

Inductive blist : Type -> Type :=
  | T {A} : forall {GreenAmount YellowAmount}, 
         colored_list A (not_red GreenAmount YellowAmount) -> 
          blist A.

(* The function [blist_value] gives the list represented by a blist. *)

Definition blist_value {A : Type} (bl : blist A) : list A :=
  match bl with 
  | T clist => colored_list_value clist 
  end.

(* The function [bcons] simply adds an element to a list. *)

Equations bcons {A : Type} (a : A) (l : blist A) : 
    { bl : blist A | blist_value bl = [a] ++ blist_value l } :=
bcons a (T Null) := ? T (Cons (One a Hole) Null);
bcons a (T (Cons (Zero ones) clist)) := ? T (Cons (One a ones) clist);
bcons a (T (Cons (One b ones) (next := FromYellow) clist)) := 
    let '(? gclist) := ensure_green clist in 
    let '(? glist) := ensure_green (Cons (Two a b ones) gclist) in 
    ? T glist.
Next Obligation.
  intros.
  destruct n0; exact FromYellow. 
Qed.

Print bcons.
  