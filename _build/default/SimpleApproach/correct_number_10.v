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

(* For a type [N], an instance of [NatRep N] means that [N] can represent 
   natural numbers. This type class only contains one function, [value], that 
   returns the integer represented by an element of type [N]. *)

Class NatRep (N : Type) := {
  value : N -> nat
}.

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

(* The function [packet_value] gives the integer represented by a packet. *)

Fixpoint packet_value {color} (p : packet color) : nat :=
  match p with 
  | Hole => 0
  | Zero ones => 0 + 2 * packet_value ones 
  | One ones  => 1 + 2 * packet_value ones 
  | Two ones  => 2 + 2 * packet_value ones
  end.

(* Packets can represent integers, therefor we can add an instance of 
   NatRep for packets. *)

Instance PacketRep {color} : NatRep (packet color) := {|
  value := packet_value
|}.

(* The function [thickness] determines the power of 2 associated with the bit 
   following the last '1' in a headed list of ones. For a headed list of ones, 
   denoted as [ho], thickness ho is equal to 2 ** (1 + length ho). 
   
   For example, 
      thickness Hole := 1;
      thickness (Zero Hole) := 2;
      thickness (Zero (One Hole)) := 4;
      thickness (Two (One Hole)) := 4;
      thickness (One (One (One (One Hole)))) := 16. 
      
   It is used when computing the integer represented by several headed lists of
   ones in a row (= a colored number). *)

Fixpoint thickness {color} (p : packet color) : nat :=
  match p with
  | Hole => 1
  | Zero ones | One ones | Two ones => 2 * thickness ones 
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

(* The function [colored_nbr_value] determines the integer represented by a 
   colored number.

   Since a colored number is essentially several consecutive packets, we initially
   calculate the integer represented by the tail. Then, utilizing [thickness] 
   on the head, we ascertain by how many bits we should shift the integer 
   represented by the tail. By summing the integer represented by the head and 
   the one represented by the tail, we obtain the integer represented by the 
   entire colored number.

   For instance, if 376 is represented as 2110112, transforming it into colored 
   number form, we obtain 211 (0111 (2 Null)). Let's manually apply our algorithm 
   to this colored number:
                Null -> 0;
              2 Null : packet_value 2 := 2,
                       thickness 2 := 2
                     -> 2 + 2 * 0 = 2;
        0111 (2 Null) : packet_value 0111 := 14,
                       thickness 0111 := 16,
                     -> 14 + 16 * 2 = 46;
   211 (0111 (2 Null)) : packet_value 211 := 8,
                         thickness 211 := 8,
                     -> 8 + 8 * 46 = 376. *)

Fixpoint colored_nbr_value {color} (cnbr : colored_nbr color) : nat :=
  match cnbr with 
  | Null => 0 
  | Green ho tl | Yellow ho tl | Red ho tl => 
    let n1 := value ho in 
    let pow1 := thickness ho in 
    let n2 := colored_nbr_value tl in
    n1 + pow1 * n2 
  end.

(* Colored numbers can represent integers, an instance of NatRep is
   created for them. *)

Instance ColoredNbrRep {color} : NatRep (colored_nbr color) := {|
  value := colored_nbr_value
|}.

(* The function [ensure_green] takes a green or red colored number and returns 
   a green one representing the same integer. *)

Equations ensure_green {GreenAmount RedAmount} 
    (cnbr : colored_nbr (Mix GreenAmount NoYellow RedAmount)) :
        colored_nbr green :=
ensure_green Null := Null;
ensure_green (Green zero cnbr) := Green zero cnbr;
(* 2 -> 01 *)
ensure_green (Red (Two Hole) Null) := Green (Zero (One Hole)) Null;
(* 20... -> 01... *)
ensure_green (Red (Two Hole) (Green (Zero ones) cnbr)) := 
    Green (Zero (One ones)) cnbr;
(* 21... -> 02... *)
ensure_green (Red (Two (One ones)) cnbr) := 
    Green (Zero Hole) (Red (Two ones) cnbr).

(* The lemma [valid_ensure_green] ensures that the integer represented by a 
   colored number remains unchanged after the transformation performed by 
   [ensure_green]. *)

Lemma valid_ensure_green {GreenAmount RedAmount} 
    (cnbr : colored_nbr (Mix GreenAmount NoYellow RedAmount)) : 
        value (ensure_green cnbr) = value cnbr.
Proof.
  eapply ensure_green_elim; eauto; simpl; lia.
Qed.

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
  let '(T t) := n in value t.

(* The goal of [nbr] is to represent integers, we obviously add an instance of 
   NatRep for nbr. *)

Instance NbrRep : NatRep nbr := {|
  value := nbr_value
|}.

(* The function [succ] simply increments a number by 1. *)

Equations succ (n : nbr) : nbr :=
succ (T Null) := T (Yellow (One Hole) Null);
succ (T (Green (Zero ones) cnbr)) := T (Yellow (One ones) cnbr);
succ (T (Yellow (One ones) cnbr)) := 
    T (ensure_green (Red (Two ones) (ensure_green cnbr))).

(* The lemma [valid_succ] ensures that for 'n' being a [nbr], the integer 
   represented by (succ n) is indeed the integer represented by 'n' 
   incremented by 1. *)

Lemma valid_succ (n : nbr) : value (succ n) = S (value n).
Proof.
  eapply succ_elim; eauto; intros GreenAmount RedAmount YellowAmount ? ?.
  simpl.
  (* Not the most beautiful proof, but I had troubles unifying the value
     function of ColoredNbrRep and colored_nbr_value, which are the same. *)
  assert (forall {G R} (cnbr' : colored_nbr (Mix G NoYellow R)), 
      colored_nbr_value (ensure_green cnbr') = colored_nbr_value cnbr').
  { intros; apply valid_ensure_green. }
  rewrite H.
  simpl. do 2 f_equal.
  rewrite H.
  lia.
Qed.