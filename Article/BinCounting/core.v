From Coq Require Import Lia.
From Equations Require Import Equations.

From Color Require Import color.
Import GYR.

(* Types *)

Inductive packet : color -> Type :=
  | Hole : packet uncolored
  | GDigit {Y} : packet (Mix NoGreen Y NoRed) -> packet green
  | YDigit {Y} : packet (Mix NoGreen Y NoRed) -> packet yellow
  | RDigit {Y} : packet (Mix NoGreen Y NoRed) -> packet red.

Inductive regularity : color -> color -> Type :=
  | G {G R} : regularity green (Mix G NoYellow R)
  | Y : regularity yellow green
  | R : regularity red    green.

Inductive chain : color -> Type :=
  | Empty : chain green
  | Chain {C1 C2 : color} :
    regularity C1 C2 -> packet C1 -> chain C2 -> chain C1.

Inductive number : Type :=
  | T {G Y} : chain (Mix G Y NoRed) -> number.

(* Models *)

Set Equations Transparent.

Equations packet_nat {C : color} : packet C -> nat -> nat :=
packet_nat Hole n := n;
packet_nat (GDigit  pkt) n := 0 + 2 * packet_nat pkt n;
packet_nat (YDigit pkt) n := 1 + 2 * packet_nat pkt n;
packet_nat (RDigit    pkt) n := 2 + 2 * packet_nat pkt n.

Equations chain_nat {C : color} : chain C -> nat :=
chain_nat Empty := 0;
chain_nat (Chain _ pkt c) := packet_nat pkt (chain_nat c).

Equations number_nat : number -> nat :=
number_nat (T c) := chain_nat c.

Unset Equations Transparent.

(* Functions *)

Notation "? x" := (@exist _ _ x _) (at level 100).

(* Definition green_of_red (c : chain red) : chain green :=
  match c with
  | Chain R (RDigit Hole) Empty =>
      Chain G (GDigit (YDigit Hole)) Empty
  | Chain R (RDigit Hole) (Chain G (GDigit pkt) c) =>
      Chain G (GDigit (YDigit pkt)) c
  | Chain R (RDigit (YDigit pkt)) c =>
      Chain G (GDigit Hole) (Chain R (RDigit pkt) c)
  end. *)

Equations green_of_red' : chain red -> chain green :=
green_of_red' (Chain R (RDigit Hole) Empty) :=
  Chain G (GDigit (YDigit Hole)) Empty;
green_of_red' (Chain R (RDigit Hole) (Chain G (GDigit pkt) c)) :=
  Chain G (GDigit (YDigit pkt)) c;
green_of_red' (Chain R (RDigit (YDigit pkt)) c) :=
  Chain G (GDigit Hole) (Chain R (RDigit pkt) c).

Require Import Coq.Program.Equality.
Lemma green_of_red_correct (c : chain red) :
    chain_nat (green_of_red' c) = chain_nat c.
Proof.
  dependent destruction c.
  dependent destruction r.
  dependent destruction p.
  dependent destruction p.
  - dependent destruction c.
    + simp green_of_red'.
      reflexivity.
    + dependent destruction r.
      dependent destruction p.
      simp green_of_red'. simpl.
      remember (packet_nat p (chain_nat c)) as numb.
      lia.
  - simp green_of_red'.
    simpl.
    remember (packet_nat p (chain_nat c)) as numb.
    lia.
Qed.

Equations green_of_red (c : chain red) :
  { c' : chain green | chain_nat c' = chain_nat c} :=
green_of_red (Chain R (RDigit Hole) Empty) :=
  ? Chain G (GDigit (YDigit Hole)) Empty;
green_of_red (Chain R (RDigit Hole) (Chain G (GDigit pkt) c)) :=
  ? Chain G (GDigit (YDigit pkt)) c;
green_of_red (Chain R (RDigit (YDigit pkt)) c) :=
  ? Chain G (GDigit Hole) (Chain R (RDigit pkt) c).

Equations ensure_green {G R} (c : chain (Mix G NoYellow R)) :
  { c' : chain green | chain_nat c' = chain_nat c } :=
ensure_green Empty := ? Empty;
ensure_green (Chain G pkt c) := ? Chain G pkt c;
ensure_green (Chain R (RDigit Hole) Empty) :=
  ? Chain G (GDigit (YDigit Hole)) Empty;
ensure_green (Chain R (RDigit Hole) (Chain G (GDigit pkt) c)) :=
  ? Chain G (GDigit (YDigit pkt)) c;
ensure_green (Chain R (RDigit (YDigit pkt)) c) :=
  ? Chain G (GDigit Hole) (Chain R (RDigit pkt) c).

Equations succ (n : number) :
  { n' : number | number_nat n' = S (number_nat n) } :=
succ (T Empty) := ? T (Chain Y (YDigit Hole) Empty);
succ (T (Chain G (GDigit pkt) c)) with ensure_green c => {
  | ? c' := ? T (Chain Y (YDigit pkt) c') };
succ (T (Chain Y (YDigit pkt) c))
  with ensure_green (Chain R (RDigit pkt) c) => { | ? c' := ? T c' }.