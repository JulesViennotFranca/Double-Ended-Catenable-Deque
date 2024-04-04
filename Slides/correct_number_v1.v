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

(* The type [headed_ones] denotes lists of ones preceded by a head. Structurally, 
   it encompasses the empty list, [Hole], as well as lists of the format 011...1, 
   111...1, and 211...1, with their respective heads determined by the 
   corresponding constructor.

   A color is linked to headed lists of ones, providing insights into the head. 
   An uncolored list is empty, a green one begins with 0, a yellow one with 1, 
   and a red one with 2.

   Here, to express that 0, 1, and 2 are solely followed by 1s or nothing, we 
   leverage information provided by colors. If the constructor parameter is 
   yellow, it implies 1s are following; if it is uncolored, nothing follows, 
   thereby concluding the list.

   To ensure the parameter is either yellow or uncolored, we employ an implicit 
   variable [YellowAmount] of type [yellow_hue]. This variable may be either 
   [SomeYellow] or [NoYellow], resulting in either yellow or uncolored outcomes. *)

Inductive headed_ones : color -> Type :=
  | Hole : headed_ones uncolored
  | Zero : forall {YellowAmount}, 
            headed_ones (Mix NoGreen YellowAmount NoRed) ->
             headed_ones green
  | One : forall {YellowAmount}, 
           headed_ones (Mix NoGreen YellowAmount NoRed) ->
            headed_ones yellow
  | Two : forall {YellowAmount}, 
           headed_ones (Mix NoGreen YellowAmount NoRed) ->
            headed_ones red.

(* The function [headed_ones_to_nat] gives the integer represented by a headed
   list of ones. *)

Fixpoint headed_ones_to_nat {color} (headed_ones : headed_ones color) : nat :=
  match headed_ones with 
  | Hole => 0
  | Zero ones => 0 + 2 * headed_ones_to_nat ones 
  | One ones  => 1 + 2 * headed_ones_to_nat ones 
  | Two ones  => 2 + 2 * headed_ones_to_nat ones
  end.

(* The function [headed_ones_to_pow] determines the power of 2 associated with
   the bit following the last '1' in a headed list of ones. For a headed list 
   of ones, denoted as [ho], headed_ones_to_pow ho is equal to 
   2 ** (1 + length ho). 
   
   For example, 
      headed_ones_to_pow Hole := 1;
      headed_ones_to_pow (Zero Hole) := 2;
      headed_ones_to_pow (Zero (One Hole)) := 4;
      headed_ones_to_pow (Two (One Hole)) := 4;
      headed_ones_to_pow (One (One (One (One Hole)))) := 16. 
      
   It is used when computing the integer represented by several headed lists of
   ones in a row (= a colored number). *)

Fixpoint headed_ones_to_pow {color} (headed_ones : headed_ones color) : nat :=
  match headed_ones with
  | Hole => 1
  | Zero ones | One ones | Two ones => 2 * headed_ones_to_pow ones 
  end.

(* The type [colored_nbr] denotes integers represented in skewed binary form, 
   embellished with colors representing the ease of incrementing the integer.

   In a green colored number, adding 1 can be done effortlessly. In a yellow 
   one, adding 1 requires some rearrangements, while in a red one, adding 1 
   isn't possible in constant time.

   Formally, a colored number is simply a recursive list of headed_ones, 
   terminated by [Null]. For instance, the skewed representation of 1870 as 
   01112100111 (with the least significant bit on the left) would be stored as 
   follows: 0111 (21 (0 (0 (111 Null)))).

   A green colored number is one that commences with a green headed_ones, and 
   likewise for yellow or red ones.

   However, we impose different conditions on the tail of a colored number 
   (understood as the tail in the sense of a colored number as a list of 
   headed_ones). For a red colored number, we require the tail to be green, 
   which is straightforward.

   However, for green and yellow colored numbers, the color of the tail is more 
   nuanced. We don't want it to be yellow (= starting with 1s). To address this, 
   we utilize implicit variables [GreenAmount] and [RedAmount] of corresponding 
   hues. This yields four potential colors, but as we only declare green, yellow, 
   and red colored numbers, [Equations] will discard the two impossible colors, 
   leaving us with a green or red tail. *)

Inductive colored_nbr : color -> Type :=
  | Null : colored_nbr green
  | Green : forall {GreenAmount RedAmount}, 
             headed_ones green -> 
              colored_nbr (Mix GreenAmount NoYellow RedAmount) -> 
               colored_nbr green
  | Yellow : forall {GreenAmount RedAmount}, 
              headed_ones yellow -> 
               colored_nbr (Mix GreenAmount NoYellow RedAmount) -> 
                colored_nbr yellow 
  | Red : headed_ones red -> 
           colored_nbr green -> 
            colored_nbr red.

(* The function [colored_nbr_to_nat] determines the integer represented by a 
   colored number.

   Since a colored number is essentially several consecutive headed lists of 
   ones, we initially calculate the integer represented by the tail. Then, 
   utilizing [headed_ones_to_pow] on the head, we ascertain by how many bits we 
   should shift the integer represented by the tail. By summing the integer 
   represented by the head and the one represented by the tail, we obtain the 
   integer represented by the entire colored number.

   For instance, if 376 is represented as 2110112, transforming it into colored 
   number form, we obtain 211 (0111 (2 Null)). Let's manually apply our algorithm 
   to this colored number:
   - Null -> 0;
   - 2 : headed_ones_to_nat 2 := 2,
         headed_ones_to_pow 2 := 2
          -> 2 + 2 * 0 = 2;
   - 0111 : headed_ones_to_nat 0111 := 14,
            headed_ones_to_pow 0111 := 16,
          -> 14 + 16 * 2 = 46;
   - 211 : headed_ones_to_nat 211 := 8,
           headed_ones_to_nat 211 := 8,
          -> 8 + 8 * 46 = 376. *)

Fixpoint colored_nbr_to_nat {color} (cnbr : colored_nbr color) : nat :=
  match cnbr with 
  | Null => 0 
  | Green ho tl | Yellow ho tl | Red ho tl => 
    let n1 := headed_ones_to_nat ho in 
    let pow1 := headed_ones_to_pow ho in 
    let n2 := colored_nbr_to_nat tl in
    n1 + pow1 * n2 
  end.

Notation "? x" := (@exist _ _ x _) (at level 100).

(* The function [ensure_green] takes a green or red colored number and returns 
   a green one representing the same integer. *)

Equations ensure_green {GreenAmount RedAmount} 
    (cnbr : colored_nbr (Mix GreenAmount NoYellow RedAmount)) :
        { gnbr : colored_nbr green | colored_nbr_to_nat gnbr = colored_nbr_to_nat cnbr } :=
ensure_green Null := ? Null;
ensure_green (Green zero cnbr) := ? Green zero cnbr;
(* 2 -> 01 *)
ensure_green (Red (Two Hole) Null) := ? Green (Zero (One Hole)) Null;
(* 20... -> 01... *)
ensure_green (Red (Two Hole) (Green (Zero ones) cnbr)) := ? Green (Zero (One ones)) cnbr;
(* 21... -> 02... *)
ensure_green (Red (Two (One ones)) cnbr) := ? Green (Zero Hole) (Red (Two ones) cnbr).
Next Obligation.
  simpl; lia.
Qed.
Next Obligation.
  simpl; lia.
Qed.

(* Lastly, the type [nbr] will denote integers represented in skewed binary 
   form where the addition of 1 in constant time is possible.

   We employ the same method as before to exclusively select green and yellow 
   colored numbers. *)

Inductive nbr : Type :=
  | T : forall {GreenAmount YellowAmount}, 
         colored_nbr (Mix GreenAmount YellowAmount NoRed) -> 
          nbr.

(* The function [nbr_to_nat] gives the integer represented by a nbr. *)

Definition nbr_to_nat (n : nbr) : nat := 
  let '(T t) := n in colored_nbr_to_nat t.

(* The function [succ] simply increments a number by 1. *)

Equations succ (n : nbr) : { m : nbr | nbr_to_nat m = S (nbr_to_nat n) } :=
succ (T Null) := ? T (Yellow (One Hole) Null);
succ (T (Green (Zero ones) cnbr)) := ? T (Yellow (One ones) cnbr);
succ (T (Yellow (One ones) cnbr)) := 
    let '(exist _ gnbr _) := ensure_green cnbr in 
    let '(exist _ gnbr _) := ensure_green (Red (Two ones) gnbr) in 
    ? T gnbr.