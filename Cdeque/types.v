From Cdeque Require Import buffer.

From Color Require Import color.
Import GYOR.

Inductive pkind : Type := Single | Pair.
Inductive kind : Type := Only | Left | Right.
Inductive ending : Type := Is_end | Not_end.

Derive NoConfusion for pkind.
Derive NoConfusion for kind.
Derive NoConfusion for ending.

(* Types for general prefix and suffix, they are simply aliases for buffer.t. *)

Definition prefix' := buffer.t.
Definition suffix' := buffer.t.

Inductive coloring : nat -> nat -> color -> Type :=
  | G {qp qs : nat} : coloring (3 + qp) (3 + qs) green
  | Y {qp qs : nat} : coloring (2 + qp) (2 + qs) yellow
  | O {qp qs : nat} : coloring (1 + qp) (1 + qs) orange
  | R {qp qs : nat} : coloring (0 + qp) (0 + qs) red.

Inductive storage' (A : Type) : kind -> ending -> color -> Type :=
  | Only_end {q  : nat} : prefix' A (S q) -> storage' A Only Is_end green
  | Left_end {qp : nat} :
    prefix' A (5 + qp) -> suffix' A 2 -> storage' A Left Is_end green
  | Right_end {qs : nat} :
    prefix' A 2 -> suffix' A (5 + qs) -> storage' A Right Is_end green
  | Only_st {qp qs : nat} {C : color} :
    coloring qp qs C -> prefix' A (5 + qp) -> suffix' A (5 + qs) -> storage' A Only Not_end C
  | Left_st {qp qs : nat} {C : color} :
    coloring qp qs C -> prefix' A (5 + qp) -> suffix' A 2 -> storage' A Left Not_end C
  | Right_st {qp qs : nat} {C : color} :
    coloring qp qs C -> prefix' A 2 -> suffix' A (5 + qs) -> storage' A Right Not_end C.
Arguments Only_end {A q}.
Arguments Left_end {A qp}.
Arguments Right_end {A qs}.
Arguments Only_st {A qp qs C}.
Arguments Left_st {A qp qs C}.
Arguments Right_st {A qp qs C}.

Inductive chain_regularity : color -> color -> color -> Type :=
 | Green_chain {Cl Cr : color} : chain_regularity green Cl Cr
 | Red_chain : chain_regularity red green green.

Inductive stored_triple (A : Type) : nat -> Type :=
  | Ground : A -> stored_triple A 0
  | Small {lvl q : nat} :
    suffix' (stored_triple A lvl) (3 + q) ->
    stored_triple A (S lvl)
  | Big {lvl qp qs : nat} {pk : pkind} {e : ending} {Cl Cr : color} :
    prefix' (stored_triple A lvl) (3 + qp) ->
    chain A (S lvl) pk Only e Cl Cr ->
    suffix' (stored_triple A lvl) (3 + qs) ->
    stored_triple A (S lvl)

with body (A : Type) : nat -> nat -> kind -> kind -> Type :=
  | Hole {lvl : nat} {k : kind} : body A lvl lvl k k
  | Only_yellow {hlvl tlvl : nat} {hk tk : kind} :
    storage' (stored_triple A hlvl) hk Not_end yellow ->
    body A (S hlvl) tlvl Only tk ->
    body A hlvl tlvl hk tk
  | Only_orange {hlvl tlvl : nat} {hk tk : kind} :
    storage' (stored_triple A hlvl) hk Not_end orange ->
    body A (S hlvl) tlvl Only tk ->
    body A hlvl tlvl hk tk
  | Pair_yellow {hlvl tlvl : nat} {hk tk : kind} {C : color} :
    storage' (stored_triple A hlvl) hk Not_end yellow ->
    body A (S hlvl) tlvl Left tk ->
    chain A (S hlvl) Single Right Not_end C C ->
    body A hlvl tlvl hk tk
  | Pair_orange {hlvl tlvl : nat} {hk tk : kind} :
    storage' (stored_triple A hlvl) hk Not_end orange ->
    chain A (S hlvl) Single Left Not_end green green ->
    body A (S hlvl) tlvl Right tk ->
    body A hlvl tlvl hk tk

with packet (A : Type) : nat -> nat -> kind -> ending -> color -> Type :=
  | Packet {hlvl tlvl : nat} {hk tk : kind} {e : ending} {G : green_hue} {R : red_hue} :
    body A hlvl tlvl hk tk ->
    storage' (stored_triple A tlvl) tk e (Mix G NoYellow NoOrange R) ->
    packet A hlvl tlvl hk e (Mix G NoYellow NoOrange R)

with chain (A : Type) : nat -> pkind -> kind -> ending -> color -> color -> Type :=
  | Empty {lvl : nat} : chain A lvl Single Only Is_end green green
  | Single_chain {hlvl tlvl : nat} {k : kind} {pk : pkind}
               {e : ending} {C Cl Cr : color} :
    chain_regularity C Cl Cr ->
    packet A hlvl tlvl k e C ->
    chain A (S tlvl) pk Only e Cl Cr ->
    chain A hlvl Single k Not_end C C
  | Pair_chain {lvl : nat} {Cl Cr : color} :
    chain A lvl Single Left Not_end Cl Cl ->
    chain A lvl Single Right Not_end Cr Cr ->
    chain A lvl Pair Only Not_end Cl Cr.

Arguments Ground {A} a.
Arguments Small {A lvl q} s.
Arguments Big {A lvl qp qs pk e Cl Cr} p child s.

Arguments Hole {A lvl k}.
Arguments Only_yellow {A hlvl tlvl hk tk} hd bd.
Arguments Only_orange {A hlvl tlvl hk tk} hd bd.
Arguments Pair_yellow {A hlvl tlvl hk tk C} hd bd cr.
Arguments Pair_orange {A hlvl tlvl hk tk} hd cl bd.

Arguments Packet {A hlvl tlvl hk tk e G R} bd tl.

Arguments Empty {A lvl}.
Arguments Single_chain {A hlvl tlvl k pk e C Cl Cr} reg pkt c.
Arguments Pair_chain {A lvl Cl Cr} cl cr.

Definition prefix (A : Type) (lvl : nat) := prefix' (stored_triple A lvl).
Definition suffix (A : Type) (lvl : nat) := suffix' (stored_triple A lvl).

Inductive green_buffer (A : Type) (lvl : nat) : Type :=
  | Gbuf {q : nat} :
    buffer.t (stored_triple A lvl) (8 + q) -> green_buffer A lvl.
Arguments Gbuf {A lvl q}.

Inductive stored_buffer (A : Type) (lvl : nat) : Type :=
  | Sbuf {q : nat} :
    buffer.t (stored_triple A lvl) (3 + q) -> stored_buffer A lvl.
Arguments Sbuf {A lvl q}.

Definition storage (A : Type) (lvl : nat) := storage' (stored_triple A lvl).

Inductive non_ending_chain :
  Type -> nat -> pkind -> kind -> color -> color -> Type :=
  | NE_chain {A lvl pk k e Cl Cr} :
    chain A lvl pk k e Cl Cr -> non_ending_chain A lvl pk k Cl Cr.

Inductive regularity : color -> pkind -> ending -> color -> color -> color -> Type :=
  | Green {pk e Cl Cr} : regularity green pk e Cl Cr green
  | Yellow {pk Cl Cr} : regularity yellow pk Not_end Cl Cr Cl
  | OrangeS {C} : regularity orange Single Not_end C C C
  | OrangeP {Cr} : regularity orange Pair Not_end green Cr Cr
  | Red {pk e} : regularity red pk e green green red.

Inductive triple : Type -> nat -> kind -> color -> Type :=
  | Triple {A : Type} {lvl : nat} {pk : pkind}
           {k : kind} {e : ending} {C Cl Cr Cpkt : color} :
    regularity C pk e Cl Cr Cpkt ->
    storage A lvl k e C ->
    chain A (S lvl) pk Only e Cl Cr ->
    triple A lvl k Cpkt.

Inductive left_right_triple : Type -> nat -> kind -> color -> Type :=
  | Not_enough {A : Type} {lvl : nat} {k : kind} :
    vector (stored_triple A lvl) 6 ->
    left_right_triple A lvl k green
  | Ok_lrt {A : Type} {lvl : nat} {k : kind} {Cpkt : color} :
    triple A lvl k Cpkt -> left_right_triple A lvl k Cpkt.

Definition six_stored_triple (A : Type) (lvl : nat) : Type :=
  stored_triple A lvl * stored_triple A lvl * stored_triple A lvl *
  stored_triple A lvl * stored_triple A lvl * stored_triple A lvl.

Inductive partial_triple : Type -> nat -> pkind -> kind -> Type :=
  | Zero_element {A : Type} {lvl : nat} {k : kind} :
    partial_triple A lvl Single k
  | Six_elements {A : Type} {lvl : nat} {k : kind} :
    six_stored_triple A lvl ->
    partial_triple A lvl Pair k
  | Ok_pt {A : Type} {lvl : nat} {pk : pkind} {k : kind} {C : color} :
    triple A lvl k C -> partial_triple A lvl pk k.

Inductive sandwich : Type -> Type -> Type :=
  | Alone {A B : Type} : A -> sandwich A B
  | Sandwich {A B : Type} : A -> B -> A -> sandwich A B.

Inductive semi_deque : Type -> nat -> Type :=
  | Semi {A : Type} {lvl : nat} {pk : pkind} {e : ending} {Cl Cr : color} :
    chain A lvl pk Only e Cl Cr -> semi_deque A lvl.

Inductive deque : Type -> Type :=
  | T {A : Type} {pk : pkind} {e : ending} :
    chain A 0 pk Only e green green -> deque A.