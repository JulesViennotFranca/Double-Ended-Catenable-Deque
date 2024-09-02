From Coq Require Import Lia.
From Equations Require Import Equations.

From Color Require Import color.
Import GYR.

(* +------------------------------------------------------------------------+ *)
(* |                                 Types                                  | *)
(* +------------------------------------------------------------------------+ *)

(* A type for packets. *)
Inductive packet : color -> Type :=
  | Hole       : packet uncolored
  | GDigit {y} : packet (Mix NoGreen y NoRed) -> packet green
  | YDigit {y} : packet (Mix NoGreen y NoRed) -> packet yellow
  | RDigit {y} : packet (Mix NoGreen y NoRed) -> packet red.

(* A type for the regularity relation. *)
Inductive regularity : color -> color -> Type :=
  | G {g r} : regularity green  (Mix g NoYellow r)
  | Y       : regularity yellow green
  | R       : regularity red    green.

(* A type for chains. *)
Inductive chain : color -> Type :=
  | Empty : chain green
  | Chain {C1 C2 : color} :
    regularity C1 C2 -> packet C1 -> chain C2 -> chain C1.

(* A type for numbers. *)
Inductive number : Type :=
  | T {g y} : chain (Mix g y NoRed) -> number.

(* +------------------------------------------------------------------------+ *)
(* |                                 Models                                 | *)
(* +------------------------------------------------------------------------+ *)

(* Model functions are transparent. *)
Set Equations Transparent.

(* Returns the natural number associated to a packet, provided the natural
   number associated to its hole. *)
Equations packet_nat {C : color} : packet C -> nat -> nat :=
packet_nat Hole n := n;
packet_nat (GDigit pkt) n := 0 + 2 * packet_nat pkt n;
packet_nat (YDigit pkt) n := 1 + 2 * packet_nat pkt n;
packet_nat (RDigit pkt) n := 2 + 2 * packet_nat pkt n.

(* Returns the natural number associated to a chain. *)
Equations chain_nat {C : color} : chain C -> nat :=
chain_nat Empty := 0;
chain_nat (Chain _ pkt c) := packet_nat pkt (chain_nat c).

(* Returns the natural number associated to a number. *)
Equations number_nat : number -> nat :=
number_nat (T c) := chain_nat c.

Unset Equations Transparent.

(* +------------------------------------------------------------------------+ *)
(* |                                  Core                                  | *)
(* +------------------------------------------------------------------------+ *)

(* Notation for dependent types hiding the property on [x]. *)
Notation "? x" := (@exist _ _ x _) (at level 100).

(*
Wrong definition :
------------------
Definition green_of_red (c : chain red) : chain green :=
  match c with
  | Chain R (RDigit Hole) Empty =>
      Chain G (GDigit (YDigit Hole)) Empty
  | Chain R (RDigit Hole) (Chain G (GDigit body) c) =>
      Chain G (GDigit (YDigit body)) c
  | Chain R (RDigit (YDigit body)) c =>
      Chain G (GDigit Hole) (Chain R (RDigit body) c)
  end.


Error :
-------
Non exhaustive pattern-matching: no clause found for pattern Chain G _ _
*)

(*
Definition without dependent types :
--------------------------------------
Equations green_of_red : chain red -> chain green :=
green_of_red (Chain R (RDigit Hole) Empty) :=
  Chain G (GDigit (YDigit Hole)) Empty;
green_of_red (Chain R (RDigit Hole) (Chain G (GDigit body) c)) :=
  Chain G (GDigit (YDigit body)) c;
green_of_red (Chain R (RDigit (YDigit body)) c) :=
  Chain G (GDigit Hole) (Chain R (RDigit body) c).

Verification of correctness :
-----------------------------
Require Import Coq.Program.Equality.
Lemma green_of_red_correct (c : chain red) :
    chain_nat (green_of_red c) = chain_nat c.
Proof.
  dependent destruction c.
  dependent destruction r.
  dependent destruction p.
  dependent destruction p.
  - dependent destruction c.
    + simp green_of_red.
      reflexivity.
    + dependent destruction r.
      dependent destruction p.
      simp green_of_red. simpl.
      remember (packet_nat p (chain_nat c)) as numb.
      lia.
  - simp green_of_red.
    simpl.
    remember (packet_nat p (chain_nat c)) as numb.
    lia.
Qed.
*)

(* Makes a red chain green. *)
Equations green_of_red (c : chain red) :
  { c' : chain green | chain_nat c' = chain_nat c} :=
green_of_red (Chain R (RDigit Hole) Empty) :=
  ? Chain G (GDigit (YDigit Hole)) Empty;
green_of_red (Chain R (RDigit Hole) (Chain G (GDigit body) c)) :=
  ? Chain G (GDigit (YDigit body)) c;
green_of_red (Chain R (RDigit (YDigit body)) c) :=
  ? Chain G (GDigit Hole) (Chain R (RDigit body) c).

(* Makes a green or red chain green. *)
Equations ensure_green {g r} (c : chain (Mix g NoYellow r)) :
  { c' : chain green | chain_nat c' = chain_nat c } :=
ensure_green Empty := ? Empty;
ensure_green (Chain G pkt c) := ? Chain G pkt c;
ensure_green (Chain R pkt c) with green_of_red (Chain R pkt c) => {
  | ? c' := ? c' }.

(* +------------------------------------------------------------------------+ *)
(* |                               Operation                                | *)
(* +------------------------------------------------------------------------+ *)

(* Adds one to a number. *)
Equations succ (n : number) :
  { n' : number | number_nat n' = S (number_nat n) } :=
succ (T Empty) := ? T (Chain Y (YDigit Hole) Empty);
succ (T (Chain G (GDigit body) c)) with ensure_green c => {
  | ? c' := ? T (Chain Y (YDigit body) c') };
succ (T (Chain Y (YDigit body) c))
  with ensure_green (Chain R (RDigit body) c) => { | ? c' := ? T c' }.