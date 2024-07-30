From Deque Require Import buffer.

(*  When a yellow or an orange triple has two children, a preferred child must 
    be specified. This is done using the [preferred_child] type that function 
    as a flag on packets (that are defined later). *)

Inductive preferred_child : Type :=
  | Preferred_left
  | Preferred_right.

(*  In the following, only, left and right triples are grouped under one type
    [triple]. To differentiate between the three kinds of triples, a new type 
    [kind] is introduced and used as a flag on the more general [triple] type. *)

Inductive kind : Type := Only | Left | Right.

(*  Here, [green_hue], [yellow_hue], [orange_hue] and [red_hue] will be utilized 
    to generate the colors essential for our program. They function as boolean 
    variables, indicating whether or not a specific hue is present in our color. *)

Inductive green_hue  : Type := SomeGreen  | NoGreen.
Inductive yellow_hue : Type := SomeYellow | NoYellow.
Inductive orange_hue : Type := SomeOrange | NoOrange.
Inductive red_hue    : Type := SomeRed    | NoRed.

(*  Colors are generated through the constructor [Mix], which accepts amount 
    of each hue as arguments. *)

Inductive color : Type :=
  | Mix : green_hue -> yellow_hue -> orange_hue -> red_hue -> color.

(*  In order for [Equations] to work on preferred children, hues and colors, 
    instances of [NoConfusion] are added to these types. *)

Derive NoConfusion for preferred_child.
Derive NoConfusion for kind.
Derive NoConfusion for green_hue.
Derive NoConfusion for yellow_hue.
Derive NoConfusion for orange_hue.
Derive NoConfusion for red_hue.
Derive NoConfusion for color.

(*  Some basic colors that we'll need. *)

Notation green      := (Mix SomeGreen  NoYellow   NoOrange   NoRed).
Notation yellow     := (Mix  NoGreen  SomeYellow  NoOrange   NoRed).
Notation yellorange := (Mix  NoGreen  SomeYellow SomeOrange  NoRed).
Notation orange     := (Mix  NoGreen   NoYellow  SomeOrange  NoRed).
Notation red        := (Mix  NoGreen   NoYellow   NoOrange  SomeRed).

(*  Types for general prefix and suffix, they are simply aliases for buffer.t. *)

Definition prefix' := buffer.t.
Definition suffix' := buffer.t.

(*  When the child of a triple is empty, different constrains apply on the 
    prefix and suffix sizes according to the kind (only, left or right) of the
    triple.  
    
    The type [small_triple_sizes] represents those constrains. There is a 
    constructor for each specific kind, which indicates what rules the sizes 
    must follow.
    
    For example, [small_triple_sizes Only qp qs] means that there exists a 
    natural number q such that qp = S q and qs = 0. *)

Inductive small_triple_sizes : kind -> nat -> nat -> Type :=
  | Only_small_sizes  {q : nat} : small_triple_sizes Only   (S q)     0
  | Left_small_sizes  {q : nat} : small_triple_sizes Left  (5 + q)    2
  | Right_small_sizes {q : nat} : small_triple_sizes Right    2    (5 + q).

(*  Similarly, when the child of a triple is not empty, new constrains apply on
    the prefix and suffix sizes according to the kind of the triple. 

    The type [big_triple_sizes] represents those constrains. It functions as 
    [small_triple_sizes], but we add a parameter, an offset that appears in 
    sizes constrains.

    For example, [big_triple_sizes offset Left qp qs] means that there exists a
    natural number q such that qp = offset + q and qs = 2. *)

Inductive big_triple_sizes (o : nat) : kind -> nat -> nat -> Type :=
  | Only_big_sizes {qp qs : nat} : big_triple_sizes o Only  (o + qp) (o + qs)
  | Left_big_sizes     {q : nat} : big_triple_sizes o Left  (o + q)     2
  | Right_big_sizes    {q : nat} : big_triple_sizes o Right    2     (o + q).
Arguments Only_big_sizes  {o qp qs}.
Arguments Left_big_sizes  {o q}.
Arguments Right_big_sizes {o q}.

(*  The mutually recursive definition of stored triples, other triples, packets,
    paths, non empty colored deques and colored deques. We call them structures 
    as they serve to store elements. 
    
    All those structures are parametrized with a base type [A]. It is the type 
    of elements that a structure holds. It means that a [struct A ...] can be 
    translated to a [list A]. 

    To put it simply, elements contained in our differents structure are 
    triples over triples over triples ... over the base type. We would like 

    To satisfy Rocq's positivity condition on types, we need to add a level 
    parameter to all of our types.  *)

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

(*  A triple represents only, left and right triples. *)

with triple (A : Type) : nat -> nat -> bool -> kind -> kind -> color -> Type :=
  | Hole {lvl : nat} {K : kind} : 
      triple A lvl 0 true K K yellorange
  | Small {lvl qp qs : nat} {K : kind} : 
      prefix' (stored_triple A lvl) qp -> 
      suffix' (stored_triple A lvl) qs ->
      small_triple_sizes K qp qs ->
      triple A lvl 0 false K K green
  | Green {lvl qp qs : nat} {K : kind} {G R} :
      prefix' (stored_triple A lvl) qp ->
      non_empty_cdeque A (S lvl) (Mix G NoYellow NoOrange R) ->
      suffix' (stored_triple A lvl) qs ->
      big_triple_sizes 8 K qp qs ->
      triple A lvl 0 false K K green
  | Yellow {lvl len qp qs : nat} {K1 K2 : kind} :
      prefix' (stored_triple A lvl) qp ->
      packet A (S lvl) len Preferred_left K2 ->
      suffix' (stored_triple A lvl) qs ->
      big_triple_sizes 7 K1 qp qs ->
      triple A lvl (S len) false K1 K2 yellow
  | Orange {lvl len qp qs : nat} {K1 K2 : kind} :
      prefix' (stored_triple A lvl) qp ->
      packet A (S lvl) len Preferred_right K2 ->
      suffix' (stored_triple A lvl) qs ->
      big_triple_sizes 6 K1 qp qs ->
      triple A lvl (S len) false K1 K2 orange
  | Red {lvl qp qs : nat} {K : kind} :
      prefix' (stored_triple A lvl) qp ->
      non_empty_cdeque A (S lvl) green ->
      suffix' (stored_triple A lvl) qs ->
      big_triple_sizes 5 K qp qs ->
      triple A lvl 0 false K K red

(*  A packet helps us choose the right triple to continue with when we follow a
    preferred chain. *)

with packet (A : Type) : nat -> nat -> preferred_child -> kind -> Type :=
  | Only_child {lvl len : nat} {is_hole : bool} {K : kind} {Y O} {pref : preferred_child} :
      triple A lvl len is_hole Only K (Mix NoGreen Y O NoRed) ->
      packet A lvl len pref K
  | Left_child {lvl len : nat} {is_hole : bool} {K : kind} {Y O C} :
      triple A lvl len is_hole Left K (Mix NoGreen Y O NoRed) ->
      path A lvl Right C ->
      packet A lvl len Preferred_left K
  | Right_child {lvl len : nat} {is_hole : bool} {K : kind} {Y O} :
      path A lvl Left green ->
      triple A lvl len is_hole Right K (Mix NoGreen Y O NoRed) ->
      packet A lvl len Preferred_right K

with path (A : Type) : nat -> kind -> color -> Type := 
  | Children {lvl len nlvl : nat} {is_hole : bool} {K1 K2 : kind} {G Y O R} :
      triple A lvl len is_hole K1 K2 (Mix NoGreen Y O NoRed) ->
      triple A nlvl 0 false K2 K2 (Mix G NoYellow NoOrange R) ->
      nlvl = len + lvl ->
      path A lvl K1 (Mix G NoYellow NoOrange R)

with non_empty_cdeque (A : Type) : nat -> color -> Type :=
  | Only_path {lvl : nat} {G R} :
      path A lvl Only (Mix G NoYellow NoOrange R) ->
      non_empty_cdeque A lvl (Mix G NoYellow NoOrange R)
  | Pair_green {lvl : nat} :
      path A lvl Left green ->
      path A lvl Right green ->
      non_empty_cdeque A lvl green
  | Pair_red {lvl : nat} {Cl Cr : color} :
      path A lvl Left Cl ->
      path A lvl Right Cr ->
      non_empty_cdeque A lvl red

with cdeque (A : Type) : nat -> color -> Type :=
  | Empty {lvl : nat} : cdeque A lvl green
  | NonEmpty {lvl G R} : 
      non_empty_cdeque A lvl (Mix G NoYellow NoOrange R) ->
      cdeque A lvl (Mix G NoYellow NoOrange R).

Arguments ST_ground {A}.
Arguments ST_small {A lvl q}.
Arguments ST_triple {A lvl qp qs C}.

Arguments Hole {A lvl K}.
Arguments Small {A lvl qp qs K}.
Arguments Green {A lvl qp qs K G R}.
Arguments Yellow {A lvl len qp qs K1 K2}.
Arguments Orange {A lvl len qp qs K1 K2}.
Arguments Red {A lvl qp qs K}.

Arguments Only_child {A lvl len is_hole K Y O pref}.
Arguments Left_child {A lvl len is_hole K Y O C}.
Arguments Right_child {A lvl len is_hole K Y O}.

Arguments Children {A lvl len nlvl is_hole K1 K2 G Y O R}.

Arguments Only_path {A lvl G R}.
Arguments Pair_green {A lvl}.
Arguments Pair_red {A lvl Cl Cr}.

Arguments Empty {A lvl}.
Arguments NonEmpty {A lvl G R}.

Definition prefix (A : Type) (lvl : nat) := prefix' (stored_triple A lvl).
Definition suffix (A : Type) (lvl : nat) := suffix' (stored_triple A lvl).

Definition only_triple (A : Type) (lvl len : nat) (is_hole : bool) := 
  triple A lvl len is_hole Only.
Definition left_triple (A : Type) (lvl len : nat) (is_hole : bool) := 
  triple A lvl len is_hole Left.
Definition right_triple (A : Type) (lvl len : nat) (is_hole : bool) := 
  triple A lvl len is_hole Right.

Inductive pref_left (A : Type) (lvl : nat) : Type :=
  | Pref_left {len nlvl K G R} : 
      packet A lvl len Preferred_left K ->
      triple A nlvl 0 false K K (Mix G NoYellow NoOrange R) ->
      nlvl = len + lvl ->
      pref_left A lvl.
Arguments Pref_left {A lvl len nlvl K G R}.

Inductive pref_right (A : Type) (lvl : nat) : Type :=
  | Pref_right {len nlvl K G R} :
      packet A lvl len Preferred_right K ->
      triple A nlvl 0 false K K (Mix G NoYellow NoOrange R) ->
      nlvl = len + lvl ->
      pref_right A lvl.
Arguments Pref_right {A lvl len nlvl K G R}.

Definition buffer_12 (A : Type) (lvl : nat) : Type := stored_triple A lvl * vector (stored_triple A lvl) 1.

Inductive path_attempt (A : Type) (lvl : nat) : kind -> color -> Type :=
  | ZeroSix {K : kind} {C : color} : 
      vector (stored_triple A lvl) 6 -> path_attempt A lvl K C
  | Ok {K : kind} {C : color} : 
      path A lvl K C -> path_attempt A lvl K C
  | Any {K : kind} {C : color} :
      path A lvl K C -> path_attempt A lvl K red.
Arguments ZeroSix {A lvl K C}.
Arguments Ok {A lvl K C}.
Arguments Any {A lvl K C}.

Inductive path_uncolored (A : Type) (lvl : nat) (K : kind) : Type :=
  | Six : stored_triple A lvl -> stored_triple A lvl -> stored_triple A lvl ->
          stored_triple A lvl -> stored_triple A lvl -> stored_triple A lvl ->
          path_uncolored A lvl K
  | AnyColor {C : color} : path A lvl K C -> path_uncolored A lvl K.
Arguments Six {A lvl K}.
Arguments AnyColor {A lvl K C}.

Inductive sdeque (A : Type) (lvl : nat) : Type :=
  Sd : forall (C : color), cdeque A lvl C -> sdeque A lvl.
Arguments Sd {A lvl C}.

Inductive unstored (A : Type) (lvl : nat) : Type :=
  | Unstored {q : nat} : 
      prefix A lvl (3 + q) -> sdeque A (S lvl) -> unstored A lvl.
Arguments Unstored {A lvl q}.

Inductive sandwich (A : Type) (lvl : nat) : Type :=
  | Alone : stored_triple A lvl -> sandwich A lvl
  | Sandwich : 
      stored_triple A lvl -> sdeque A lvl -> stored_triple A lvl ->
      sandwich A lvl.
Arguments Alone {A lvl}.
Arguments Sandwich {A lvl}.

Inductive unstored_sandwich (A : Type) (lvl : nat) : Type :=
  | Unstored_alone {q : nat} :
      prefix A lvl (3 + q) -> unstored_sandwich A lvl
  | Unstored_sandwich {qp qs : nat} :
      prefix A lvl (3 + qp) -> 
      sdeque A (S lvl) ->
      suffix A lvl (3 + qs) ->
      unstored_sandwich A lvl.
Arguments Unstored_alone {A lvl q}.
Arguments Unstored_sandwich {A lvl qp qs}.

Inductive deque (A : Type) : Type :=
  T : cdeque A 0 green -> deque A.
Arguments T {A}.