From Coq Require Import Lia.
From Equations Require Import Equations.

(* Types *)

Inductive green_hue  : Type := SomeGreen  | NoGreen.
Inductive yellow_hue : Type := SomeYellow | NoYellow.
Inductive red_hue    : Type := SomeRed    | NoRed.

Inductive color : Type :=
  Mix : green_hue -> yellow_hue -> red_hue -> color.

Derive NoConfusion for green_hue.
Derive NoConfusion for yellow_hue.
Derive NoConfusion for red_hue.
Derive NoConfusion for color.

Notation green  := (Mix SomeGreen NoYellow NoRed).
Notation yellow := (Mix NoGreen SomeYellow NoRed).
Notation red    := (Mix NoGreen NoYellow SomeRed).
Notation uncolored := (Mix NoGreen NoYellow NoRed).

Inductive packet : color -> Type :=
  | Hole        : packet uncolored
  | PGreen  {Y} : packet (Mix NoGreen Y NoRed) -> packet green
  | PYellow {Y} : packet (Mix NoGreen Y NoRed) -> packet yellow
  | PRed    {Y} : packet (Mix NoGreen Y NoRed) -> packet red.

Inductive chain : color -> Type :=
  | Ending       : chain green
  | CGreen {G R} : packet green  -> chain (Mix G NoYellow R) -> chain green
  | CYellow      : packet yellow -> chain green -> chain yellow
  | CRed         : packet red    -> chain green -> chain red.

Inductive number : Type :=
  | T {G Y} : chain (Mix G Y NoRed) -> number.

(* Models *)

Set Equations Transparent.

Equations packet_nat {C : color} : packet C -> nat -> nat :=
packet_nat Hole n := n;
packet_nat (PGreen  pkt) n := 0 + 2 * packet_nat pkt n;
packet_nat (PYellow pkt) n := 1 + 2 * packet_nat pkt n;
packet_nat (PRed    pkt) n := 2 + 2 * packet_nat pkt n.

Equations chain_nat {C : color} : chain C -> nat :=
chain_nat Ending := 0;
chain_nat (CGreen  pkt c) := packet_nat pkt (chain_nat c);
chain_nat (CYellow pkt c) := packet_nat pkt (chain_nat c);
chain_nat (CRed    pkt c) := packet_nat pkt (chain_nat c).

Equations number_nat : number -> nat :=
number_nat (T c) := chain_nat c.

Unset Equations Transparent.

(* Functions *)

Notation "? x" := (@exist _ _ x _) (at level 100).

Equations ensure_green {G R} (c : chain (Mix G NoYellow R)) :
  { c' : chain green | chain_nat c' = chain_nat c } :=
ensure_green Ending := ? Ending;
ensure_green (CGreen pkt c) := ? CGreen pkt c;
ensure_green (CRed (PRed Hole) Ending) :=
  ? CGreen (PGreen (PYellow Hole)) Ending;
ensure_green (CRed (PRed Hole) (CGreen (PGreen pkt) c)) :=
  ? CGreen (PGreen (PYellow pkt)) c;
ensure_green (CRed (PRed (PYellow pkt)) c) :=
  ? CGreen (PGreen Hole) (CRed (PRed pkt) c).

Equations incr (n : number) :
  { n' : number | number_nat n' = S (number_nat n) } :=
incr (T Ending) := ? T (CYellow (PYellow Hole) Ending);
incr (T (CGreen (PGreen pkt) c)) with ensure_green c => {
  | ? c' := ? T (CYellow (PYellow pkt) c') };
incr (T (CYellow (PYellow pkt) c)) with ensure_green (CRed (PRed pkt) c) => {
    | ? c' := ? T c' }.