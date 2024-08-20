# A first approach to our structure

## Introduction

The `Slides` folder contains the first step to understand the whole structure. It describes a way to efficiently store number and list in binary form in order to add 1 or a new element in constant time.

All practical information will be described later.

Furthermore, coq proofs are provided to ensure correctness of such a structure. It is recommanded to first look at the numbers proofs, then the lists ones as they mimic them. Numbers proofs should be looked in this order:

```c
               correct_number_00.v
                 /             \
                /               \
   correct_number_10.v      correct_number_01.v
   correct_number_10'.v
```

- `correct_number_00.v`: Initially, implementations of `ensure_green` and `succ` are provided, followed by the proof of lemmas to ensure their correctness.
- `correct_number_10.v`: A type class called `NatRep` is introduced, which represents structures containing integers. It includes a function called value that retrieves the integer stored in the structure. Consequently, this trait can be extended to `packet`, `colored_nbr`, and `nbr`.
- `correct_number_10'.v`: Similar to the previous proof, but instead of a single type class encompassing all integer-storing structures, we now have two. We retain `NatRep` and introduce `DecoratedNatRep`, a type class for structures representing integers decorated with additional types. This distinction proves useful for types like `packet` or `colored_nbr`, which include extra arguments such as color. It assists Coq in selecting the correct instances during proofs.
- `correct_number_01.v`: Rather than defining `ensure_green` and `succ` separately and then proving their correctness, these two processes are merged. The resulting output is accompanied by a proof of correctness using the dependent type sig.
- `correct_list_01'.v`: Special work on trying to get rid of redundant information for `colored_list`. The idea is to have a single constructor instead of `Green`, `Yellow` and `Red` ones, and adding a relation between colors to ensure the right color patterns in this single constructor.

Thus, we can identify the following behaviors desired for our final code: either implementing functions and then proving their correctness or directly declaring them with a proof of correctness ; deciding whether to use a type class to describe structures or not.

## Explanations of Arthur Wendling's slides

### Preliminaries : numbers representation

#### Binary representation

There is a recursivity problem when adding 1, in the worst case, it costs O(logn):

```ml
let rec succ = function
  | Null -> One Null
  | Zero t -> One t 
  | One  t -> Zero (succ t)

1 + 11111111110 ...
  = 00000000001 ...
```

#### Redundant binary representation

```ml
type t =
  | Null
  | Zero of t
  | One  of t
  | Two  of t
```

We must add an invariant to the representation otherwise we still have the same problem when adding 1 :

```ml
1 + 22222222221 ...
  = 11111111112 ...
```

#### 2 colored redundant binary representation

To this end, we decorate the type with 2 color, green and red. Green meaning we can add 1, and red the opposite.

```ml
type 'color t = 
  | Null : [`green] t 
  | Zero : _ t -> [`green] t
  | One  : 'color t -> 'color t
  | Two  : [`green] t -> [`red] t
```

We define a function to get the green representation of a number.

```ml
let rec ensure_green : type c. c t -> [`green] t = function
  | Null -> Null
  | Zero t -> Zero t
  | One t -> One (ensure_green t)
  (* 2     => 01    *)
  | Two Null -> Zero (One Null)      
  (* 20... => 01... *)
  | Two (Zero t) -> Zero (One t)     
  (* 21... => 02... *)
  | Two (One t) -> Zero (Two t)      
```

Now a function for adding 1.

```ml
let succ : [`green] t -> [`green] t = function
  | Null -> One Null
  (* Not constant cost *)
  | Zero t -> One (ensure_green t)   
  (* Constant cost *)
  | One t -> ensure_green (Two t)    
```

We do not have yet a O(1) cost when adding 1, there are still some cases when we must go through lists of ones:

```ml
1 + 01111111120 ...
  = 11111111101 ...
```

#### 3 colored redundant binary representation

The idea for this improvement is that we want to access and modify the end of the list of ones in constant time. To this end, a number will now be represented recursively as a pair of a list of ones and another number:

```ml
type ones = 
  | HOLE
  | One of ones

type 'color t =
  | Null : [`green] t
  | Zero : ones * [< `green | `red] t -> [`green] t
  | One  : ones * [< `green | `red] t -> [`yellow] t
  | Two  : ones * [< `green]        t -> [`red] t

type nat = T : [< `green | `yellow] t -> nat
```

Colors can be seen as how crowded the representation is. Green correspond to non-crowded, we can add 1 freely. Yellow is semi-crowded, we can add 1 but we will have some work to do to not be fully crowded. Finally, red is fully crowded, we cannot add 1.

Functions `ensure_green` and `succ` are now in constant time:

```ml
type _ not_yellow = Not_Yellow : [< `green | `red] not_yellow

let ensure_green : type c. c not_yellow -> c t -> [`green] t 
= fun Not_Yellow -> function
  | Null -> Null
  | Zero (ones, t) -> Zero (ones, t)
  (* 2     -> 01    *)
  | Two (HOLE, Null) -> Zero (One HOLE, Null)
  (* 20... -> 01... *)
  | Two (HOLE, Zero (ones, t)) -> Zero (One ones, t)
  (* 21... -> 02... *)
  | Two (One ones, t) -> Zero (HOLE, Two (ones, t))

let succ : nat -> nat = function
  | T Null -> T (One (HOLE, Null))
  | T (Zero (ones, t)) -> T (One (ones, t))
  | T (One (ones, t)) -> 
      T (ensure_green Not_Yellow 
          (Two (ones, ensure_green Not_Yellow t)))
```

### List representation

#### List binary representation

```ml
type 'a t =
  | Nil
  | Zero of      ('a * 'a) t
  | One  of 'a * ('a * 'a) t
```

#### List 3 colored redundant binary representation

```ml
type ('in_, 'out) ones =
  | HOLE :                            ('a, 'a) ones
  | One  : 'a * ('a * 'a, 'b) ones -> ('a, 'b) ones
```

Type decoration `'in_` and `'out` represent the 'depth' of the list of ones at its beginning and its end. In practice, `'in_` will be of the form 'a to the power of n (...((a, a), (a, a)), ...), and `'out` 'a to the power of n + m.

```ml
type ('a, 'color) t =
  | Null : ('a, [`green]) t
  | Zero : ('a * 'a, 'b) ones
         * ('b, [< `green | `red]) t
         -> ('a, [`green]) t
  | One  : 'a * ('a * 'a, 'b) ones
         * ('b, [< `green | `red]) t
         -> ('a, [`yellow]) t
  | Two  : 'a * 'a * ('a * 'a, 'b) ones
         * ('b, [`green]) t
         -> ('a, [`red]) t

type 'a list = T : ('a, [< `green | `yellow]) t -> 'a list
```

We add corresponding type decorations so the depth remains coherent throughout our structure.

We modify `ensure_green` and `succ` to match the list structure:

```ml
let ensure_green : type a c. c not_yellow -> (a, c) t -> (a, [`green]) t
= fun Not_yellow -> function
  | Null -> Null
  | Zero (ones, t) -> Zero (ones, t)
  (* 2     -> 01    *)
  | Two (a, b, HOLE, Null) ->
      Zero (One ((a, b), HOLE), Null)
  (* 20... -> 01... *)
  | Two (a, b, HOLE, Zero (ones, t)) ->
      Zero (One ((a, b), ones), t)
  (* 21... -> 02... *)
  | Two (a, b, One ((c, d), ones), t) ->
      Zero (HOLE, Two ((a, b), (c, d), ones, t))

let cons a = function
  | T Null -> T (One (a, HOLE, Null))
  | T (Zero (ones, t)) -> T (One (a, ones, t))
  | T (One (b, ones, t)) ->
      T (ensure_green Not_yellow
           (Two (a, b, ones, ensure_green Not_yellow t)))
```

### Final representation

#### For numbers

In the last representation, a number was either `Null` (=0), either a pair of a list of ones and another number. The first 'bit' of the number was given by the constructors `Zero`, `One` and `Two`, which also gave the crowdedness of the representation of the said number.

For example, $0112110112$ is seen as $0(11, 2(11, 0(11, 2(,Null))))$, but it could also be seen as $011( 211 (011 (2 (Null))))$, which is cleaner and has more of a recursive list shape.

```ml
type 'color s =
  | HOLE : [`hole] s
  | Zero : [< `yellow | `hole] s -> [`green] s
  | One  : [< `yellow | `hole] s -> [`yellow] s
  | Two  : [< `yellow | `hole] s -> [`red] s
```

Thus, a type `s` is created to represent parts of the number representation of the form $\emptyset$, $01...1$, $1..1$ and $21...1$. `Zero`, `One`and `Two` constructors are still decorated with the crowdedness associated to the part they represents.

```ml
type 'color t =
  | Null : [`green] t
  | G : [`green ] s * [< `green | `red] t -> [`green] t
  | Y : [`yellow] s * [< `green | `red] t -> [`yellow] t
  | R : [`red   ] s * [`green]          t -> [`red] t

type r = T : [< `green | `yellow] t -> r
```

We can now let go of the name `Zero`, `One` and `Two` in the type `t` constructors, and only use the crowdedness terms `G`, `Y` and `R`. Indeed, crowdedness and first digit of the representation match perfectly.

Type `r` representing numbers is the same as before, containing green and yellow representation.

We can now adapt our functions `ensure_green` and `succ` to this new definition:

```ml
let ensure_green : type c. c not_yellow -> c t -> [`green] t
= fun Not_yellow -> function
  | Null -> Null
  | G (zero, t) -> G (zero, t)
  (* 2     -> 01    *)
  | R (Two HOLE, Null) -> G (Zero (One HOLE), Null)
  (* 20... -> 01... *)
  | R (Two HOLE, G (Zero ones, t)) -> G (Zero (One ones), t)
  (* 21... -> 02... *)
  | R (Two (One ones), t) -> G (Zero HOLE, R (Two ones, t))

let succ : r -> r = function
  | T Null -> T (Y (One HOLE, Null))
  | T (G (Zero ones, t)) -> T (Y (One ones, t))
  | T (Y (One ones, t)) ->
      T (ensure_green Not_yellow
          (R (Two ones, ensure_green Not_yellow t)))
```

#### For lists

The same transformations can be done for lists:

```ml
type ('in_, 'out, 'color) s =
  | HOLE : ('a, 'a, [`hole]) s
  | Zero : ('a * 'a, 'b, [< `yellow | `hole]) s
         -> ('a, 'b, [`green]) s
  | One  : 'a * ('a * 'a, 'b, [< `yellow | `hole]) s
         -> ('a, 'b, [`yellow]) s
  | Two  : 'a * 'a * ('a * 'a, 'b, [< `yellow | `hole]) s
         -> ('a, 'b, [`red]) s

type ('a, 'color) t =
  | Null : ('a, [`green]) t
  | G : ('a, 'b, [`green ]) s * ('b, [< `green | `red]) t
      -> ('a, [`green]) t
  | Y : ('a, 'b, [`yellow]) s * ('b, [< `green | `red]) t
      -> ('a, [`yellow]) t
  | R : ('a, 'b, [`red   ]) s * ('b, [`green]         ) t
      -> ('a, [`red]) t

type 'a r = T : ('a, [< `green | `yellow]) t -> 'a r

let ensure_green : type a c. c not_yellow -> (a, c) t -> (a, [`green]) t
= fun Not_yellow -> function
  | Null -> Null
  | G (zero, t) -> G (zero, t)
  (* 2     -> 01    *)
  | R (Two (a, b, HOLE), Null) -> G (Zero (One ((a, b), HOLE)), Null)
  (* 20... -> 01... *)
  | R (Two (a, b, HOLE), G (Zero ones, t)) -> G (Zero (One ((a, b), ones)), t)
  (* 21... -> 02... *)
  | R (Two (a, b, One ((c, d), ones)), t) -> G (Zero HOLE, R (Two ((a, b), (c, d), ones), t))

let cons a = function
  | T Null -> T (Y (One (a, HOLE), Null))
  | T (G (Zero ones, t)) -> T (Y (One (a, ones), t))
  | T (Y (One (b, ones), t)) ->
      T (ensure_green Not_yellow
          (R (Two (a, b, ones), ensure_green Not_Yellow t)))
```
