From Coq Require Import ZArith Lia.
From Equations Require Import Equations.

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

(* The type [packet] denotes lists of ones preceded by a head. Structurally, 
   it encompasses the empty list, [Hole], as well as lists of the format 011...1, 
   111...1, and 211...1, with their respective heads determined by the 
   corresponding constructor.

   A color is linked to a packet, providing insights into the head. An uncolored 
   list is empty, a green one begins with 0, a yellow one with 1, and a red one 
   with 2.

   Here, to express that 0, 1, and 2 are solely followed by 1s or nothing, we 
   leverage information provided by colors. If the constructor parameter is 
   yellow, it implies 1s are following; if it is uncolored, nothing follows, 
   thereby concluding the list.

   To ensure the parameter is either yellow or uncolored, we employ an implicit 
   variable [YellowAmount] of type [yellow_hue]. This variable may be either 
   [SomeYellow] or [NoYellow], resulting in either yellow or uncolored outcomes. *)

Inductive packet : color -> Type :=
  | Hole : packet uncolored
  | Zero : forall {YellowAmount}, 
            packet (Mix NoGreen YellowAmount NoRed) ->
             packet green
  | One : forall {YellowAmount}, 
           packet (Mix NoGreen YellowAmount NoRed) ->
            packet yellow
  | Two : forall {YellowAmount}, 
           packet (Mix NoGreen YellowAmount NoRed) ->
            packet red.

(* The function [packet_length] simply returns the number of bits in a packet. *)

Fixpoint packet_length {color} (packet : packet color) : nat :=
  match packet with 
  | Hole => 0
  | Zero ones | One ones | Two ones => 1 + packet_length ones 
  end.

(* The type [colored_nbr] denotes integers represented in redundant binary form, 
   embellished with colors representing the ease of incrementing the integer.

   In a green colored number, adding 1 can be done effortlessly. In a yellow 
   one, adding 1 requires some rearrangements, while in a red one, adding 1 
   isn't possible in constant time.

   Formally, a colored number is simply a recursive list of packet, terminated 
   by [Null]. For instance, the redundant representation of 1870 as 01112100111 
   (with the least significant bit on the left) would be stored as follows: 
   0111 (21 (0 (0 (111 Null)))).

   A green colored number is one that commences with a green packet, and likewise 
   for yellow or red ones.

   However, we impose different conditions on the tail of a colored number 
   (understood as the tail in the sense of a colored number as a list of packet). 
   For a red colored number, we require the tail to be green, which is 
   straightforward.

   However, for green and yellow colored numbers, the color of the tail is more 
   nuanced. We don't want it to be yellow (= starting with 1s). To address this, 
   we utilize implicit variables [GreenAmount] and [RedAmount] of corresponding 
   hues. This yields four potential colors, but as we only declare green, yellow, 
   and red colored numbers, [Equations] will discard the two impossible colors, 
   leaving us with a green or red tail. *)

Inductive colored_nbr : color -> Type :=
  | Null : colored_nbr green
  | Green : forall {GreenAmount RedAmount}, 
             packet green -> 
              colored_nbr (Mix GreenAmount NoYellow RedAmount) -> 
               colored_nbr green
  | Yellow : forall {GreenAmount RedAmount}, 
              packet yellow -> 
               colored_nbr (Mix GreenAmount NoYellow RedAmount) -> 
                colored_nbr yellow 
  | Red : packet red -> 
           colored_nbr green -> 
            colored_nbr red.

(* The function [colored_nbr_length] simply returns the number of bits in a 
   colored number. *)

Fixpoint colored_nbr_length {color} (cnbr : colored_nbr color) : nat :=
  match cnbr with 
  | Null => 0 
  | Green ho cnbr | Yellow ho cnbr | Red ho cnbr => 
      packet_length ho + colored_nbr_length cnbr 
  end.

(* The function [colored_nbr_value] determines the integer represented by a 
   colored number.

   To compute this number, the colored number is traversed sequentially, and
   the quantity corresponding to the bit is added. In order to go through the
   colored number bit by bit, its first packet is decrease until it contains 
   only one element. Then, the computation is passed through the tail of the 
   colored number.

   For instance, if 376 is represented as 2110112, transforming it into colored 
   number form, we obtain 211 (0111 (2 Null)). Let's manually apply our algorithm 
   to this colored number:
                Null -> 0;
              2 Null -> 2 + 2 * 0;
           1 (2 Null) -> 1 + 2 * 2 = 5;
          11 (2 Null) -> 1 + 2 * 5 = 11;
         111 (2 Null) -> 1 + 2 * 11 = 23;
        0111 (2 Null) -> 0 + 2 * 23 = 46;
     1 (0111 (2 Null)) -> 1 + 2 * 46 = 93;
    11 (0111 (2 Null)) -> 1 + 2 * 93 = 187;
   211 (0111 (2 Null)) -> 2 + 2 * 187 = 376. 
   
   As it is a recursive function, a decreasing value to ensure termination is 
   needed. The length of the colored number is the ideal candidate for this. 

   /!\ The validation by Coq may take a while /!\ *)

Set Equations Transparent.

Equations colored_nbr_value {color} (cnbr : colored_nbr color) : nat 
                                    by wf (colored_nbr_length cnbr) := 
colored_nbr_value Null := 0;
colored_nbr_value (Green (Zero Hole) cnbr) := 0 + 2 * colored_nbr_value cnbr;
colored_nbr_value (Green (Zero ones) cnbr) := 0 + 2 * colored_nbr_value (Yellow ones cnbr);
colored_nbr_value (Yellow (One Hole) cnbr) := 1 + 2 * colored_nbr_value cnbr;
colored_nbr_value (Yellow (One ones) cnbr) := 1 + 2 * colored_nbr_value (Yellow ones cnbr);
colored_nbr_value (Red (Two Hole) cnbr)    := 2 + 2 * colored_nbr_value cnbr;
colored_nbr_value (Red (Two ones) cnbr)    := 2 + 2 * colored_nbr_value (Yellow ones cnbr).

Notation "? x" := (@exist _ _ x _) (at level 100).

Require Import Coq.Program.Equality.

(* The function [ensure_green] takes a green or red colored number and returns 
   a green one representing the same integer. *)

Equations ensure_green {GreenAmount RedAmount} 
    (cnbr : colored_nbr (Mix GreenAmount NoYellow RedAmount)) :
        { gnbr : colored_nbr green | 
            colored_nbr_value gnbr = colored_nbr_value cnbr } :=
ensure_green Null := ? Null;
ensure_green (Green zero cnbr) := ? Green zero cnbr;
(* 2 -> 01 *)
ensure_green (Red (Two Hole) Null) := ? Green (Zero (One Hole)) Null;
(* 20... -> 01... *)
ensure_green (Red (Two Hole) (Green (Zero ones) cnbr)) := 
    ? Green (Zero (One ones)) cnbr;
(* 21... -> 02... *)
ensure_green (Red (Two (One ones)) cnbr) := 
    ? Green (Zero Hole) (Red (Two ones) cnbr).
Next Obligation.
  dependent destruction ones; simp colored_nbr_value; lia.
Qed.
Next Obligation.
  dependent destruction ones; simp colored_nbr_value; lia.
Qed.

Search ensure_green.
Print ensure_green_equation_5.
About ensure_green.

(* Lastly, the type [nbr] will denote integers represented in redundant binary 
   form where the addition of 1 in constant time is possible.

   We employ the same method as before to exclusively select green and yellow 
   colored numbers. *)

Inductive nbr : Type :=
  | T : forall {GreenAmount YellowAmount}, 
         colored_nbr (Mix GreenAmount YellowAmount NoRed) -> 
          nbr.

(* The function [nbr_value] gives the integer represented by a nbr. *)

Definition nbr_value (n : nbr) : nat := 
  let '(T t) := n in colored_nbr_value t.

Require Import Coq.Program.Equality.

(* The function [succ] simply increments a number by 1. *)

Equations succ (n : nbr) : { m : nbr | nbr_value m = S (nbr_value n) } :=
succ (T Null) := ? T (Yellow (One Hole) Null);
succ (T (Green (Zero ones) cnbr)) := ? T (Yellow (One ones) cnbr);
succ (T (Yellow (One ones) cnbr)) := _.
Next Obligation.
  dependent destruction ones; simp colored_nbr_value; lia.
Qed.
Next Obligation.
  remember (ensure_green cnbr) as gnbr1 eqn: Heq1; destruct gnbr1 as [gnbr1 H1].
  remember (ensure_green (Red (Two ones) gnbr1)) as gnbr2 eqn: Heq2; destruct gnbr2 as [gnbr2 H2].
  exists (T gnbr2); simpl.
  dependent destruction ones.
  - rewrite H2; simp colored_nbr_value; rewrite H1; lia.
  - rewrite ensure_green_equation_5 in Heq2; apply (f_equal (fun '(? x) => x)) in Heq2.
    rewrite Heq2. simp colored_nbr_value.
    dependent destruction cnbr.
    + simp ensure_green in Heq1; apply (f_equal (fun '(? x) => x)) in Heq1.
      rewrite Heq1; dependent destruction ones
