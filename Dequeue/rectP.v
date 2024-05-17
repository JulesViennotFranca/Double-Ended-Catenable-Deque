From Dequeue Require Import lvlproof.

Section rectP.
  
  Variable A : Type.
  Variable P : A -> Type.
  Variable f : forall (a : A), P a.

  Variable PprodN : forall {lvl}, prodN A lvl -> Type.
  Variable Pbuffer : forall {lvl C}, buffer A lvl C -> Type.
  Variable Ppacket : forall {lvl len C}, lvl_packet A lvl len C -> Type.
  Variable Pcdeque : forall {lvl C}, lvl_cdeque A lvl C -> Type.
  Variable Pdeque : deque A -> Type.

  Variable P_prodZ : forall {a : A}, 
    P a -> PprodN (prodZ a).
  Variable P_prodS : forall {lvl : nat} {p1 p2 : prodN A lvl},
    PprodN p1 -> PprodN p2 -> PprodN (prodS p1 p2).

  Variable P_B0 : forall {lvl : nat}, Pbuffer (lvl := lvl) B0.
  Variable P_B1 : forall {lvl : nat} {a : prodN A lvl}, 
    PprodN a -> Pbuffer (lvl := lvl) (B1 a).
  Variable P_B2 : forall {lvl : nat} {G Y} {a b : prodN A lvl}, 
    PprodN a -> PprodN b -> Pbuffer (lvl := lvl) (C := Mix G Y NoRed) (B2 a b).
  Variable P_B3 : forall {lvl : nat} {G Y} {a b c : prodN A lvl}, 
    PprodN a -> PprodN b -> PprodN c -> Pbuffer (lvl := lvl) (C := Mix G Y NoRed) (B3 a b c).
  Variable P_B4 : forall {lvl : nat} {a b c d : prodN A lvl}, 
    PprodN a -> PprodN b -> PprodN c -> PprodN d -> Pbuffer (lvl := lvl) (B4 a b c d).
  Variable P_B5 : forall {lvl : nat} {a b c d e : prodN A lvl}, 
    PprodN a -> PprodN b -> PprodN c -> PprodN d -> PprodN e -> Pbuffer (lvl := lvl) (B5 a b c d e).

  Variable P_Hole : forall {lvl : nat}, Ppacket (lvl := lvl) Hole.
  Variable P_Triple : forall {lvl len : nat} {Y : yellow_hue} {C1 C2 C3 : color}
      {p : buffer A lvl C1} {pkt : lvl_packet A (S lvl) len (Mix NoGreen Y NoRed)} 
      {s : buffer A lvl C2} {pc : packet_color C1 C2 C3},
    Pbuffer p -> Ppacket pkt -> Pbuffer s -> Ppacket (Triple p pkt s pc).

  Variable P_Small : forall {lvl : nat} {C : color} {b : buffer A lvl C},
    Pbuffer b -> Pcdeque (Small b).
  Variable P_Big : forall {lvl len nlvl : nat} {C1 C2 : color} 
      {pkt : lvl_packet A lvl len C1} {cd : lvl_cdeque A nlvl C2} {eq : nlvl = len + lvl} {cc : cdeque_color C1 C2},
    Ppacket pkt -> Pcdeque cd -> Pcdeque (Big pkt cd eq cc).

  Variable P_T : forall {G : green_hue} {Y : yellow_hue} {cd : lvl_cdeque A 0 (Mix G Y NoRed)},
    Pcdeque cd -> Pdeque (T cd).

  Fixpoint prodN_rectP {lvl} (p : prodN A lvl) : PprodN p :=
    match p with 
    | prodZ a => P_prodZ (f a)
    | prodS p1 p2 => P_prodS (prodN_rectP p1) (prodN_rectP p2)
    end.

  Definition buffer_rectP {lvl C} (b : buffer A lvl C) : Pbuffer b := 
    match b with
    | B0 => P_B0
    | B1 a => P_B1 (prodN_rectP a)
    | B2 a b => P_B2 (prodN_rectP a) (prodN_rectP b)
    | B3 a b c => P_B3 (prodN_rectP a) (prodN_rectP b) (prodN_rectP c)
    | B4 a b c d => P_B4 (prodN_rectP a) (prodN_rectP b) (prodN_rectP c) (prodN_rectP d)
    | B5 a b c d e => P_B5 (prodN_rectP a) (prodN_rectP b) (prodN_rectP c) (prodN_rectP d) (prodN_rectP e)
    end.

  Fixpoint packet_rectP {lvl len C} (pkt : lvl_packet A lvl len C) : Ppacket pkt :=
    match pkt with 
    | Hole => P_Hole
    | Triple p pkt s pc => P_Triple (buffer_rectP p) (packet_rectP pkt) (buffer_rectP s)
    end.

  Fixpoint cdeque_rectP {lvl C} (cd : lvl_cdeque A lvl C) : Pcdeque cd :=
    match cd with
    | Small b => P_Small (buffer_rectP b)
    | Big pkt cd eq cc => P_Big (packet_rectP pkt) (cdeque_rectP cd)
    end.

  Definition deque_rectP (d : deque A) : Pdeque d :=
    match d with
    | T cd => P_T (cdeque_rectP cd)
    end.

End rectP.