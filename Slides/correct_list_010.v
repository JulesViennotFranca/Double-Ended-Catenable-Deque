From Coq Require Import List ZArith Lia.
Import ListNotations.
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

Opaque app.
Definition singleton {A} (x : A) : list A := [x].
Opaque singleton.

(* The type [packet] denotes lists of ones preceded by a head. Structurally, 
   it encompasses the empty list, [Hole], as well as lists of the format 011...1, 
   111...1, and 211...1, with their respective heads determined by the 
   corresponding constructor.

   Here, 0, 1 and 2 correspond to the list of elements contained at this 'bit'.
   And at each 'bit', the 'size' of elements contained doubles. For example, if
   we starts with elements of type A, the rest of the packet starts with 
   elements of type (A * A). Type [In] and [Out] derive from this behavior, [In]
   being the type of elements at the beginning, and [Out] being the type of 
   elements at the list's end. 

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

Inductive packet : forall (In Out : Type), color -> Type :=
  | Hole {A} : packet A A uncolored
  | Zero {A B} : forall {YellowAmount}, 
                  packet (A * A) B (Mix NoGreen YellowAmount NoRed) ->
                   packet A B green
  | One {A B} : forall {YellowAmount}, 
                 A ->
                  packet (A * A) B (Mix NoGreen YellowAmount NoRed) ->
                   packet A B yellow
  | Two {A B} : forall {YellowAmount}, 
                 A ->
                  A -> 
                   packet (A * A) B (Mix NoGreen YellowAmount NoRed) ->
                    packet A B red.

(* The function [packet_length] simply returns the number of bits in a packet. *)

Fixpoint packet_length {A B color} (packet : packet A B color) : nat := 
  match packet with 
  | Hole => 0
  | Zero ones | One _ ones | Two _ _ ones => 1 + packet_length ones
  end.

(* The type [colored_list] denotes lists represented in redundant binary form, 
   embellished with colors representing the ease of adding elements to the list.

   In a green colored list, adding one element can be done effortlessly. In a 
   yellow one, it requires some rearrangements, while in a red one, it isn't 
   possible to add an element in constant time.

   Formally, a colored list is simply a recursive list of packet, terminated 
   by [Null]. However, we have to make sure the type of the rest of the colored
   list is the same as the one at the exit of the first packet. The type [B] 
   introduced in the color constructor ensure that. This maintains the behavior
   of packets where the size of elements contained from a bit to the next 
   doubles.
   
   For example, as a redundant representation of 10 can be 012, the list 
   [1; 2; 3; 4; 5; 6; 7; 8; 9; 10] in redundant form is 
   [; [(1, 2); [((3, 4), (5, 6)); ((7, 8), (9, 10))]]]. 
   And as a colored list, it would give us a list of 2 packets:
   [; [(1, 2)]] ++ [((3, 4), (5, 6)); ((7, 8), (9, 10)); []] ++ Null.

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

Inductive colored_list : Type -> color -> Type :=
  | Null {A} : colored_list A green
  | Green {A B} : forall {GreenAmount RedAmount}, 
                   packet A B green -> 
                    colored_list B (Mix GreenAmount NoYellow RedAmount) -> 
                     colored_list A green
  | Yellow {A B} : forall {GreenAmount RedAmount}, 
                    packet A B yellow -> 
                     colored_list B (Mix GreenAmount NoYellow RedAmount) -> 
                      colored_list A yellow 
  | Red {A B} : packet A B red -> 
                 colored_list B green -> 
                  colored_list A red.

(* The function [colored_list_length] simply returns the number of bits in a 
   colored list. *)

Fixpoint colored_list_length {A color} (clist : colored_list A color) : nat := 
  match clist with 
  | Null => 0
  | Green ho clist | Yellow ho clist | Red ho clist => 
      packet_length ho + colored_list_length clist
  end.

(* The function [flatten] transform a list of pairs into a list of single 
   elements, preserving their order. *)

Fixpoint flatten {A} (l : list (A * A)) : list A :=
  match l with 
  | [] => []
  | cons (a1, a2) l => [a1] ++ [a2] ++ (flatten l)
  end.

(* The function [colored_list_value] returns the list represented by a colored 
   list.

   To compute this list, the colored list is traversed sequentially, and the 
   elements stored at each bit are added. In order to go through the colored 
   list bit by bit, its first packet is decrease until it contains only one last
   bit. Then, the computation is passed through the tail of the colored list.

   If the first element of a colored list is of type A, applying 
   colored_list_value on it returns a list of elements of type A. As we've seen,
   the size of elements contained in a colored number doubles from a bit to the 
   next. So flatten is called at each stage to ensure the right typing for our 
   output list.

   Applying our algorithm manually on a list of 10 elements:
   - Null -> [];
   - [((3, 4), (5, 6)); ((7, 8), (9, 10)); []] ++ Null ->
        [((3, 4), (5, 6))] ++ [((7, 8), (9, 10))] ++ [] 
        = [((3, 4), (5, 6)); ((7, 8), (9, 10))];
   - [(1, 2)] ++ [((3, 4), (5, 6)); ((7, 8), (9, 10)); []] ++ Null ->
        [(1, 2)] ++ [(3, 4); (5, 6); (7, 8); (9, 10)]
        = [(1, 2); (3, 4); (5, 6); (7, 8); (9, 10)];
   - [; [(1, 2)]] ++ [((3, 4), (5, 6)); ((7, 8), (9, 10)); []] ++ Null ->
        [1; 2; 3; 4; 5; 6; 7; 8; 9; 10].
   
   As it is a recursive function, a decreasing value to ensure termination is 
   needed. The length (in bits) of the colored list is the ideal candidate for 
   this. 

   /!\ The validation by Coq may take a while /!\ *)

Equations colored_list_value {A color} (clist : colored_list A color) : list A 
                                            by wf (colored_list_length clist) := 
colored_list_value Null := [];
colored_list_value (Green (Zero Hole) clist) := 
    flatten (colored_list_value clist);
colored_list_value (Green (Zero ones) clist) := 
    flatten (colored_list_value (Yellow ones clist));
colored_list_value (Yellow (One a Hole) clist) := 
    [a] ++ flatten (colored_list_value clist);
colored_list_value (Yellow (One a ones) clist) := 
    [a] ++ flatten (colored_list_value (Yellow ones clist));
colored_list_value (Red (Two a b Hole) clist) := 
    [a] ++ [b] ++ flatten (colored_list_value clist);
colored_list_value (Red (Two a b ones) clist) := 
    [a] ++ [b] ++ flatten (colored_list_value (Yellow ones clist)).

Notation "? x" := (@exist _ _ x _) (at level 100).

Require Import Coq.Program.Equality.

(* The function [ensure_green] takes a green or red colored list and returns 
   a green one representing the same list. *)

Equations ensure_green {A GreenAmount RedAmount} 
    (clist : colored_list A (Mix GreenAmount NoYellow RedAmount)) :
        { glist : colored_list A green | 
            colored_list_value glist = colored_list_value clist } :=
ensure_green Null := ? Null;
ensure_green (Green zero clist) := ? Green zero clist;
ensure_green (Red (Two a b Hole) Null) := ? Green (Zero (One (a, b) Hole)) Null;
ensure_green (Red (Two a b Hole) (Green (Zero ones) clist)) := 
    ? Green (Zero (One (a, b) ones)) clist;
ensure_green (Red (Two a b (One (c, d) ones)) clist) := 
    ? Green (Zero Hole) (Red (Two (a, b) (c, d) ones) clist).
Next Obligation.
  simp colored_list_value.
  dependent destruction ones; simp colored_list_value; reflexivity.
Qed.
Next Obligation.
  simp colored_list_value.
  dependent destruction ones; simp colored_list_value; reflexivity.
Qed.

(* Lastly, the type [blist] will denote lists represented in redundant binary 
   form where the addition of one element in constant time is possible.

   We employ the same method as before to exclusively select green and yellow 
   colored lists. *)

Inductive blist : Type -> Type :=
  | T {A} : forall {GreenAmount YellowAmount}, 
         colored_list A (Mix GreenAmount YellowAmount NoRed) -> 
          blist A.

(* The function [blist_value] gives the list represented by a blist. *)

Definition blist_value {A} (bl : blist A) : list A :=
  match bl with 
  | T clist => colored_list_value clist 
  end.

(* The function [bcons] simply adds an element to a list. *)

Equations bcons {A} (a : A) (l : blist A) : 
    { bl : blist A | blist_value bl = [a] ++ blist_value l } :=
bcons a (T Null) := ? T (Yellow (One a Hole) Null);
bcons a (T (Green (Zero ones) clist)) := ? T (Yellow (One a ones) clist);
bcons a (T (Yellow (One b ones) clist)) := 
    let '(? gclist) := ensure_green clist in 
    let '(? glist) := ensure_green (Red (Two a b ones) gclist) in 
    ? T glist.
Next Obligation.
  dependent destruction ones; simp colored_list_value; reflexivity.
Qed.
Next Obligation.
  
