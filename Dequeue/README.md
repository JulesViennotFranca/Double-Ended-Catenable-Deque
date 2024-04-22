# Double-Ended Queue

Abreviated to deque, said to be over the set A if it stores elements from A.

## Structure description

### Goal

The purpose of this structure is to support push and pop (at the front of the list) and inject and eject (at the end of the list) in pushtant time.

Hence the name 'double-ended' queue.

### Buffers

To begin with, we present the building blocks of our structure, *buffers*. They are simply lists that can hold up to five elements.

In our structure, we will encounter two types of *buffers*, *prefixes* and *suffixes*.

### Deque

A *deque* d over a set A is composed of a prefix, a child and a suffix. The prefix and suffix of d, written prefix(d) and suffix(d), are simply prefix and suffix *buffers*, containing elements from A.

The child of d, written child(d) is another *deque* over the set A * A, possibly empty. So we have a recursive definition for *deques*. We introduce the notation child(i, d) for the i-th non-empty child of the *deque* d (child(0, d) = d and child(1, d) = child(d)).

Here, we represent the first two children of a deque over the set A:

![deque_representation](/Annex/deque1.png)

### Coloration

As for the simple approach, we decorate our structures with colors.

For *buffers*, coloration comes directly from the number of elements it contains. A *buffer* containing 2 or 3 elements is green, one containing 1 or 4 elements is yellow and one with 0 or 5 elements is red. Practically, the color of a *buffer* stands for how much elements we can add **and** remove from it: for green it's 2, for yellow 1 and for red 0.

Then, given the order red < yellow < green, the color of a *deque* is the minimum of its prefix and suffix colors. If the child of a *deque* and one of its buffer is empty, the color of the *deque* will then be the one of its non-empty buffer.

### Regularity

Given colors for each *deque*, we can look at the colors of the sequence child(0, d), child(1, d), child(2, d), ...

First, we call d *semiregular* if between any two red *deques* in the descendant sequence, there is a green *deque* (ignoring yellow ones).

Notice how if d is *semiregular*, for all i, child(i, d) is *semiregular*.

We call d *regular* if d is *semiregular* and if the first non-yellow *deque* is green.

Notice that if d is *semiregular* and red, then child(d) is *regular*.

### Link with our simple approach

Our strategy is to maintain regularity for the top-level *deque*. As in our simple approach, an operation may change the color of the top-level *deque*, and this may also change its regularity.

To restore the regularity, we have to change to green the topmost non-yellow descendant *deque*, similarly to how we changed a red number or list to green.

As we want to avoid checking all descendant until we find the red one, we will use *packets*, the same way we did in the simpler approach. A *packet* being either empty or a stack of *deques* with only the first one possibly non-yellow. A *deque* will then be a stack of such *packets*:

![deque_packet](/Annex/deque_packet.png)

### Operations

- *push* and *pop*: done on the top-level prefix, if the top-level prefix is empty and the child *deque* too, it is done on the top-level suffix.
- *inject* and *eject*: symmetric case.

During this process, the top-level can change from green to yellow, or from yellow to red, thus making the *deque* semiregular.

### Regularisation

To restore a semiregular *deque* d, we start by introducing some notations. If i is the topmost red level, let P(i), P(i+1), S(i+1), S(i) denote prefixes and suffixes at level i and i+1. We call elements of P(i+1) and S(i+1) pairs as they are pairs of elements of P(i) and S(i).

Note that as level i+1 can't be red (semiregularity), if P(i+1) or S(i+1) is empty, so is the *deque* at level i+2.

Next, one of the three cases apply:

- *Two-Buffer Case*: |P(i+1)| + |S(i+1)| ≥ 2. We can make P(i+1) and S(i+1) yellow. So it is possible for us to move around a pair from level i to level i+1. We can make P(i) and S(i) green.
- *One-Buffer Case*: |P(i+1)| + |S(i+1)| ≤ 1, and |P(i)| ≥ 2 or |S(i)| ≥ 2. If there is one pair at level i+1, there are enough elements to make P(i) and S(i) green, and pass excess elements at level i+1. If level i+1 is empty, in order for level i to be red, it must have enough elements to make P(i) and S(i) green, possibly creating a level i+1 for excess elements.
- *No-Buffer Case*: |P(i+1)| + |S(i+1)| ≤ 1, and |P(i)| ≤ 1, and |S(i)| ≤ 1. We have 1 pair at level i+1, and 0 or 1 element at level i. That adds up to 2 or 3 elements in total, we move all them to P(i) and discard level i+1.

## Explanations of Arthur Wendling's code

### Code for buffers

He starts by defining a type for *buffers*:

```ml
type ('a, 'color) buffer =
  | B0 :                           ('a, [`red   ]) buffer
  | B1 : 'a                     -> ('a, [`yellow]) buffer
  | B2 : 'a * 'a                -> ('a, [< `green | `yellow]) buffer
  | B3 : 'a * 'a * 'a           -> ('a, [< `green | `yellow]) buffer
  | B4 : 'a * 'a * 'a * 'a      -> ('a, [`yellow]) buffer
  | B5 : 'a * 'a * 'a * 'a * 'a -> ('a, [`red   ]) buffer
```

Notice that, contrary to Kaplan and Tarjan's paper, *buffer* containing 2 or 3 elements can also be considered yellow. It will simplify the typing of later functions.

He also defines special types for yellow and green *buffers* ...

```ml
type 'a yellow_buffer =
  Yellowish : ('a, [< `green | `yellow]) buffer -> 'a yellow_buffer
```

... and *buffers* of any color.

```ml
type 'a any_buffer =
  Any : ('a, [< `green | `yellow | `red ]) buffer -> 'a any_buffer
```

### Code for deque

First, he defines a type for *packet*:

```ml
type ('a, 'b, 'color) packet =
  (* The empty packet. *)
  | HOLE : ('a, 'a, [`hole]) packet

  (* Packet starting with one. *)
  | Yellow : ('a, [< `green | `yellow]) buffer
           * ('a * 'a, 'b, [< `yellow | `hole]) packet
           * ('a, [< `green | `yellow]) buffer
          -> ('a, 'b, [`yellow]) packet

  (* Packet starting with green. *)
  | Green : ('a, [`green]) buffer
          * ('a * 'a, 'b, [< `yellow | `hole]) packet
          * ('a, [`green]) buffer
         -> ('a, 'b, [`green]) packet

  (* Packet starting with red. *)
  | Red : ('a, [< `green | `yellow | `red]) buffer
        * ('a * 'a, 'b, [< `yellow | `hole]) packet
        * ('a, [< `green | `yellow | `red]) buffer
       -> ('a, 'b, [`red]) packet
```

Then, a type for *deque*, decorated with colors:

```ml
type ('a, 'color) cdeque =
  (* Deque made of only one buffer. *)
  | Small : ('a, _) buffer -> ('a, [`green]) cdeque

  (* Deque starting with a green packet. *)
  | G : ('a, 'b, [`green ]) packet
      * ('b, [< `green | `red]) cdeque
     -> ('a, [`green ]) cdeque

  (* Deque starting with a yellow packet. It must be followed by a green packet 
     in order to be regular. *)
  | Y : ('a, 'b, [`yellow]) packet
      * ('b, [`green]) cdeque
     -> ('a, [`yellow]) cdeque

  (* Deque starting with a red packet. It must be followed by a green packet in
     order to be semiregular. *)
  | R : ('a, 'b, [`red]) packet
      * ('b, [`green]) cdeque
     -> ('a, [`red]) cdeque
```

Finally, a type for regular *deque*:

```ml
type 'a deque = T : ('a, [< `green | `yellow]) cdeque -> 'a deque
```

### Code for operations

To better understand the code architecture for operations, here is a graph representing dependencies between different functions found in the code:

![AW_code_architecture](/Annex/deque_code_architecture.png)

First, we can see the desired operations *push*, *inject*, *pop* and *eject* directly on *deques*:

```ml
val push : 'a -> 'a deque -> 'a deque
val inject : 'a deque -> 'a -> 'a deque
val pop_unsafe : 'a deque -> 'a * 'a deque
val eject_unsafe : 'a deque -> 'a deque * 'a
```

Here, the `unsafe` keyword means that an error is raised when trying to *pop* or *eject* from an empty *deque*.

Similarly, the same operations on *buffers* exists:

```ml
val buffer_push : 'a -> ('a, 'c) buffer -> ('a, [ `green ]) cdeque
val buffer_inject : ('a, 'c) buffer -> 'a -> ('a, [ `green ]) cdeque
val buffer_pop_unsafe : ('a, 'c) buffer -> 'a * 'a any_buffer
val buffer_pop : ('a, 'c) buffer -> ('a * 'a any_buffer) option
val buffer_eject_unsafe : ('a, 'c) buffer -> 'a any_buffer * 'a
val buffer_eject : ('a, 'c) buffer -> ('a any_buffer * 'a) option
```

Notice that `buffer_push` and `buffer_inject` directly returns a green *deque*.

Then, the same operations on green and yellow *buffers* are written:

```ml
val green_push : 'a -> ('a, [ `green ]) buffer -> 'a yellow_buffer
val green_inject : ('a, [ `green ]) buffer -> 'a -> 'a yellow_buffer
val green_pop : ('a, [ `green ]) buffer -> 'a * 'a yellow_buffer
val green_eject : ('a, [ `green ]) buffer -> 'a yellow_buffer * 'a

val yellow_push : 'a -> 'a yellow_buffer -> 'a any_buffer
val yellow_inject : 'a yellow_buffer -> 'a -> 'a any_buffer
val yellow_pop : 'a yellow_buffer -> 'a * 'a any_buffer
val yellow_eject : 'a yellow_buffer -> 'a any_buffer * 'a
```

Some auxiliary and specific functions are needed:

```ml
(* Elements rotations in buffers. *)
val prefix_rot : 'a -> ('a, 'c) buffer -> ('a, 'c) buffer * 'a (* Push then eject. *)
val suffix_rot : ('a, 'c) buffer -> 'a -> 'a * ('a, 'c) buffer (* Inject then pop. *)

(* Merging elements and options into buffers. *)
val prefix23 : 'a option -> 'a * 'a -> ('a, [< `green | `yellow ]) buffer
val suffix23 : 'a * 'a -> 'a option -> ('a, [< `green | `yellow ]) buffer
val suffix12 : 'a -> 'a option -> ('a, [ `yellow ]) buffer

(* Decomposition with respect to a green buffer. *)
type 'a decompose =
  | Underflow : 'a option -> 'a decompose
  | Ok : ('a, [ `green ]) buffer -> 'a decompose
  | Overflow : ('a, [ `green ]) buffer * ('a * 'a) -> 'a decompose
val prefix_decompose : ('a, 'c) buffer -> 'a decompose (* Excess elements are removed at the end. *)
val suffix_decompose : ('a, 'c) buffer -> 'a decompose (* Excess elements are removed at the beginning. *)

(* Sandwich representation of buffers. *)
type 'a sandwich =
  | Alone : 'a option -> 'a sandwich
  | Sandwich : 'a * ('a, 'b) buffer * 'a -> 'a sandwich
val buffer_unsandwich : ('a, 'c) buffer -> 'a sandwich

(* Going from a buffer to a lower level buffer. *)
val buffer_halve : ('a, 'c) buffer -> 'a option * ('a * 'a) any_buffer
```

Then, the `concat` functions are used when the *buffers* of one level are made green using the *buffers* at the next level. The `prefix` keyword means that this is done on prefix *buffers*, respectively the `suffix` keyword means that this is done on suffix *buffers*. The function starting with `green` are called when the lower level is green, the `yellow` ones are called when the lower level is yellow.

```ml
val green_prefix_concat :
  ('a, 'c) buffer ->
  ('a * 'a, [ `green ]) buffer ->
  ('a, [ `green ]) buffer * ('a * 'a) yellow_buffer

val green_suffix_concat :
  ('a * 'a, [ `green ]) buffer ->
  ('a, 'c) buffer -> 
  ('a * 'a) yellow_buffer * ('a, [ `green ]) buffer

val yellow_prefix_concat :
  ('a, 'b) buffer ->
  ('a * 'a) yellow_buffer -> 
  ('a, [ `green ]) buffer * ('a * 'a) any_buffer

val yellow_suffix_concat :
  ('a * 'a) yellow_buffer ->
  ('a, 'b) buffer -> 
  ('a * 'a) any_buffer * ('a, [ `green ]) buffer
```

Arthur Wendling designs special function `make_small` when the red *cdeque* is at the end. The lower level is then composed of only one *buffer*. The arguments of `make_small` are the prefix *buffer*, the unique *buffer* of the lower level and the suffix *buffer*. This function returns a green *cdeque* containing the same set of elements in the same order.

```ml
val make_small :
  ('a, 'b) buffer ->
  ('a * 'a, 'c) buffer -> 
  ('a, 'd) buffer -> 
  ('a, [ `green ]) cdeque
```

Then,he writes a function `green_of_red` to transform a red *cdeque* into a green one representing the same set in the same order. If the red *cdeque* is at the end, he uses `make_small`, if it is followed by a yellow level, he uses `yellow_prefix_concat` and `yellow_suffix_concat`, and if it is followed by a green level, he uses `green_prefix_concat` and `green_suffix_concat`.

He adds a simple wrap of `green_of_red`, `ensure_green`, to work on non-yellow *cdeque*.

```ml
val green_of_red : ('a, [ `red ]) cdeque -> ('a, [ `green ]) cdeque

type _ not_yellow = Not_yellow : [< `green | `red ] not_yellow
val ensure_green :
  'c not_yellow -> 
  ('a, 'c) cdeque -> 
  ('a, [ `green ]) cdeque
```

Finally, the `yellow` and `red` functions transforms respectively a yellow or a red *cdeque* into a *deque*. They are based on `green_of_red` and `ensure_green`. They will be used to ensure regularity when adding or removing elements with *push*, *inject*, *pop* and *eject*.

```ml
val yellow :
  ('a, [< `green | `yellow ]) buffer ->
  ('a * 'a, 'b, [< `hole | `yellow ]) packet ->
  ('a, [< `green | `yellow ]) buffer ->
  ('b, [< `green | `red ]) cdeque -> 
  'a deque

val red :
  ('a, [< `green | `red | `yellow ]) buffer ->
  ('a * 'a, 'b, [< `hole | `yellow ]) packet ->
  ('a, [< `green | `red | `yellow ]) buffer ->
  ('b, [ `green ]) cdeque -> 
  'a deque
```

### The final structure

To complete his structure, he constructs a final type for storing *deque* with their length:

```ml
type 'a t = { length : int ; s : 'a deque }
```

If the length is negative, it means the *t* is to be read backward. This enables Arthur Wendling to write a reverse function in constant time. Obviously, getting the length of a *t* is done in constant time.

```ml
let rev t = { t with length = - t.length }

let length t = abs t.length
```

To finish, he designs the functions *push*, *inject*, *pop* and *eject* for *ts*.

```ml
val push : 'a -> 'a t -> 'a t
val inject : 'a t -> 'a -> 'a t
val pop : 'a t -> ('a * 'a t) option
val eject : 'a t -> ('a t * 'a) option
```

The code is described in detail in [AWcode.ml](/Deque/AWcode.ml).

## Explanation of Armaël Guéneau's proof

The structure of Armaël Guéneau's proof is very similar to the code of Arthur Wendling.

### Types definition

He starts by defining all the types needed, with an additional type `phantom` representing colors:

```coq
Inductive phantom : Type := ...

Inductive buffer : Type -> phantom -> Type := ...
Inductive yellow_buffer (A: Type) : Type := ...
Inductive any_buffer (A: Type) : Type := ...

Inductive packet : Type -> Type -> phantom -> phantom -> Type := ...

Inductive cdeque : Type -> phantom -> Type := ...

Inductive decompose (A : Type) : Type := ...

Inductive sandwich (A : Type) : Type := ...

Inductive deque : Type -> Type := ...
```

### Models definition

Then, he writes functions translating the different structures to the list they represent:

```coq
Equations option_seq {A} : option A -> list A := ...

Equations buffer_seq {A C} : buffer A C -> list A := ...
Equations yellow_buffer_seq {A} : yellow_buffer A -> list A := ...
Equations any_buffer_seq {A} : any_buffer A -> list A := ...

Equations packet_front_seq {A B C K} : packet A B C K -> list A := ...
Equations packet_rear_seq {A B C K} : packet A B C K -> list A := ...
Equations packet_hole_flatten {A B C K} : packet A B C K -> list B -> list A := ...

Equations cdeque_seq {A C} : cdeque A C -> list A := ...

Equations decompose_main_seq {A : Type} (dec : decompose A) : list A := ...
Equations decompose_rest_seq {A : Type} (dec : decompose A) : list A := ...

Equations sandwich_seq {A : Type} (sw : sandwich A) : list A := ...

Equations deque_seq {A} : deque A -> list A := ...
```

Those functions will be used when proving we have the expected behaviors for the different functions of Arthur Wendling's code.

### Functions definition

This part is really similar to the original code: the same functions are defined, along with a proof that they are correct using dependant types.

For example, here are the types of functions corresponding to *push*, *inject*, *pop* and *eject*:

```coq
Equations push {A: Type} (x : A) (sq : deque A) :
  { sq' : deque A | deque_seq sq' = x :: deque_seq sq }
:= ...

Equations inject {A: Type} (sq : deque A) (x : A) :
  { sq' : deque A | deque_seq sq' = deque_seq sq ++ [x] }
:= ...

Equations pop {A: Type} (sq : deque A) :
  { o : option (A * deque A) |
    deque_seq sq = match o with
               | None => []
               | Some (x, sq') => x :: deque_seq sq'
               end } := ...

Equations eject {A : Type} (sq : deque A) :
  { o : option (deque A * A) |
    deque_seq sq = match o with
               | None => []
               | Some (sq', x) => deque_seq sq' ++ [x]
               end } := ...
```

Notice that here, safe version of `pop` and `eject` are directly implemented for *deque*.

### Final structure definition

As in Arthur's code, Armaël defines *t*, adding a field ensuring the `seq_length` field is indeed the length of the sequence represented by the *deque* `seq`.

```coq
Record t (A: Type) : Type := {
  deq_length : Z;
  seq : deque A;
  length_inv : Z.abs_nat deq_length = length (deque_seq seq);
}.
```

Similarly, a model function is written:

```coq
Equations t_seq {A} : t A -> list A := ...
```

Then, as in the original code, there is a `is_empty`, a `length`, a `rev` and a `is_rev` function:

```coq
Equations is_empty {A} (sq : t A) :
  { b : bool | b = true <-> t_seq sq = [] } := ...

Equations length {A} (sq : t A) :
  { n : Z | n = Z.of_nat (List.length (t_seq sq)) } := ...

Equations rev {A} (sq : t A) : 
  { sq' : t A | t_seq sq' = rev (t_seq sq) } := ...

Definition is_rev {A} (sq : t A) : bool := ...
```

Finally, *push*, *inject*, *pop* and *eject* functions are defined for *ts*. They require a bit more work to prove than the previous ones:

```coq
Equations push {A} (x : A) (sq : t A) :
  { sq' : t A | t_seq sq' = x :: t_seq sq } := ...

Equations inject {A} (sq : t A) (x : A) :
  { sq' : t A | t_seq sq' = t_seq sq ++ [x] } := ...

Equations pop {A} (sq : t A) :
  { o : option (A * t A) |
    t_seq sq = match o with
               | None => []
               | Some (x, sq') => x :: t_seq sq'
               end } := ...

Equations eject {A} (sq : t A) :
  { o : option (t A * A) |
    t_seq sq = match o with
               | None => []
               | Some (sq', x) => t_seq sq' ++ [x]
               end } := ...
```
