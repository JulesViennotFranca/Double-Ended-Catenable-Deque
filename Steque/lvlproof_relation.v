From Coq Require Import ssreflect.
From Coq Require Import Program List Lia.
Import ListNotations.
From Equations Require Import Equations.
From Hammer Require Import Tactics.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Lists.

From Dequeue Require Import lvlproof.

(* Types *)

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
Notation orange := (Mix NoGreen SomeYellow SomeRed).
Notation red := (Mix NoGreen NoYellow SomeRed).
Notation uncolored := (Mix NoGreen NoYellow NoRed).

(* A type for suffixes, simply the final type of the previous structure. *)

Inductive suffix' (A : Type) : Type := 
  | Suff : deque A -> suffix' A.
Arguments Suff {A}.

(* A type for prefixes, possibly of length 2, 3 or 4 and more. The color will
   be given by the number of elements. *)

Inductive prefix' (A : Type) : color -> Type := 
  | Pre2 : A -> A -> prefix' A red
  | Pre3 : A -> A -> A -> prefix' A yellow
  | Pre4 : A -> A -> A -> A -> deque A -> prefix' A green.
Arguments Pre2 {A}.
Arguments Pre3 {A}.
Arguments Pre4 {A}.

(* A relation between the packet, the following steque and the current steque 
   colors. *)

Inductive csteque_color : color -> color -> color -> Type := 
  | CCGreen {G R} : csteque_color green (Mix G NoYellow R) green
  | CCYellow : csteque_color yellow green yellow 
  | CCOrange : csteque_color yellow red orange
  | CCRed : csteque_color red green red.

(* The mutally recursive definition of elements, packets and colored steque. 
   
   Elements represents the types of elements stored. At level 0, elements of 
   type A are stored. When the level increase, elements of the new level are 
   made of a prefix of elements of the previous level and a colored steque of 
   the new level. *)
      
Inductive element (A : Type) : nat -> Type := 
  | ZElt : A -> element A 0
  | SElt {lvl : nat} {C1 C2 : color} : 
      prefix' (element A lvl) C1 -> 
      lvl_csteque A (S lvl) C2 -> 
      element A (S lvl)
 
   (* Packets represents the same concept as before : either a Hole, the end of 
   the packet, or a triple prefix - next packet - suffix, with the next packet
   being of one level higher, and yellow or uncolored. *)

with lvl_packet (A : Type) : nat -> nat -> color -> Type := 
  | Hole {lvl : nat} : lvl_packet A lvl 0 uncolored 
  | Triple {lvl len : nat} {Y : yellow_hue} {C : color} : 
      prefix' (element A lvl) C -> 
      lvl_packet A (S lvl) len (Mix NoGreen Y NoRed) ->
      suffix' (element A lvl) ->
      lvl_packet A lvl (S len) C

   (* Colored steques also look similar to colored deque in our previous structure,
   it is either Small, only made of a suffix, or big, made of one packet and a 
   following colored steque. *)

with lvl_csteque (A : Type) : nat -> color -> Type := 
  | Small {lvl : nat} : 
      suffix' (element A lvl) -> 
      lvl_csteque A lvl green 
  | Big {lvl len nlvl : nat} {C1 C2 C3 : color} :
      lvl_packet A lvl len C1 ->
      lvl_csteque A nlvl C2 ->
      nlvl = len + lvl ->
      csteque_color C1 C2 C3 ->
      lvl_csteque A lvl C3.
    
Arguments ZElt {A}.
Arguments SElt {A lvl C1 C2}.
Arguments Hole {A lvl}.
Arguments Triple {A lvl len Y C}.
Arguments Small {A lvl}.
Arguments Big {A lvl len nlvl C1 C2 C3}.

Definition suffix A lvl := suffix' (element A lvl).
Definition prefix A lvl := prefix' (element A lvl).

(* A type for colored steque. *)

Definition csteque (A : Type) := lvl_csteque A 0.

(* A type for steque. *)

Inductive steque (A : Type) : Type := 
  T : forall (G : green_hue) (Y : yellow_hue), 
      csteque A (Mix G Y NoRed) -> 
      steque A.
Arguments T {A G Y}.

(* Models *)

Set Equations Transparent.

Opaque app.
Definition singleton {A : Type} (x : A) : list A := [x].
Opaque singleton.

Equations in_prodN {A lvl} : A -> prodN A lvl -> Prop :=
in_prodN a (prodZ b) := a = b;
in_prodN a (prodS (p1, p2)) := in_prodN a p1 \/ in_prodN a p2.

Equations in_buffer {A lvl C} : A -> buffer A lvl C -> Prop :=
in_buffer _ B0 := False;
in_buffer a (B1 p1) := in_prodN a p1;
in_buffer a (B2 p1 p2) := in_prodN a p1 \/ in_prodN a p2;
in_buffer a (B3 p1 p2 p3) := in_prodN a p1 \/ in_prodN a p2 \/ in_prodN a p3;
in_buffer a (B4 p1 p2 p3 p4) := in_prodN a p1 \/ in_prodN a p2 \/ in_prodN a p3 \/ in_prodN a p4;
in_buffer a (B5 p1 p2 p3 p4 p5) := in_prodN a p1 \/ in_prodN a p2 \/ in_prodN a p3 \/ in_prodN a p4 \/ in_prodN a p5.

Equations in_dpacket {A lvl len C} : A -> lvlproof.lvl_packet A lvl len C -> Prop :=
in_dpacket _ lvlproof.Hole := False;
in_dpacket a (lvlproof.Triple p pkt s _) := in_buffer a p \/ in_dpacket a pkt \/ in_buffer a s.

Equations in_cdeque {A lvl C} : A -> lvl_cdeque A lvl C -> Prop :=
in_cdeque a (lvlproof.Small b) := in_buffer a b;
in_cdeque a (lvlproof.Big pkt cd eq_refl _) := in_dpacket a pkt \/ in_cdeque a cd.

Equations in_deque {A} : A -> deque A -> Prop :=
in_deque a (lvlproof.T cd) := in_cdeque a cd.

Equations in_suffix {A} : A -> suffix' A -> Prop := 
in_suffix a (Suff d) := in_deque a d.

Equations in_prefix {A C} : A -> prefix' A C -> Prop :=
in_prefix a (Pre2 b c) := a = b \/ a = c;
in_prefix a (Pre3 b c d) := a = b \/ a = c \/ a = d;
in_prefix a (Pre4 b c d e) := a = b \/ a = c \/ a = d \/ in_deque a e.

Inductive imp_and (P : Prop) : (P -> Prop) -> Prop := 
| imp_conj : forall (p : P) (q : P -> Prop), imp_and P q.

Equations in_prefix_eq {A lvl1 lvl2 C} : element A lvl1 -> prefix A lvl2 C -> lvl1 = lvl2 -> Prop := 
in_prefix_eq e p eq_refl := in_prefix e p.

Equations in_suffix_eq {A lvl1 lvl2} : element A lvl1 -> suffix A lvl2 -> lvl1 = lvl2 -> Prop :=
in_suffix_eq e s eq_refl := in_suffix e s.

Equations in_prefix_suffix_eq {A lvl1 lvl2 C} : element A lvl1 -> prefix A lvl2 C -> suffix A lvl2 -> lvl1 = lvl2 -> Prop :=
in_prefix_suffix_eq e p s eq_refl := in_prefix e p \/ in_suffix e s.

Equations csteque_eq {A lvl1 lvl2 C1 C2} : lvl_csteque A lvl1 C1 -> lvl_csteque A lvl2 C2 -> (lvl1 = lvl2) /\ (C1 = C2) -> Prop :=
csteque_eq cs1 cs2 (conj eq_refl eq_refl) := cs1 = cs2.

(* Equations csteque_length {A lvl C} :  *)

Equations R' {A} k1 lvl1 len1 C1 (s1 : structure A k1 lvl1 len1 C1) k2 lvl2 len2 C2 (s2 : structure A k2 lvl2 len2 C2) : Prop :=
R' Element lvl1 0 uncolored e Element (S lvl2) 0 uncolored (SElt _ _ p _) := imp_and (lvl1 = lvl2) (in_prefix_eq e p);
R' Element lvl1 0 uncolored e Csteque lvl2 0 C (Small s) := imp_and (lvl1 = lvl2) (in_suffix_eq e s);
R' Element lvl1 0 uncolored e Csteque lvl2 0 C (Big (Triple p _ s) _ _ _) := imp_and (lvl1 = lvl2) (in_prefix_suffix_eq e p s);
R' Csteque lvl1 0 C1 cs1 Element (S lvl2) 0 uncolored (SElt C C2 p cs2) := imp_and (lvl1 = S lvl2 /\ C1 = C2) (csteque_eq cs1 cs2);
R' Csteque lvl1 0 C1 cs1 Csteque lvl2 0 _ (Big (Triple _ Hole _) cs2 eq_refl _) := imp_and (lvl1 = S lvl2 /\ C1 = _) (csteque_eq cs1 cs2);
R' Csteque lvl1 0 yellow cs1 Csteque lvl2 0 _ (Big (Triple _ pkt _) cs2 eq_refl CCRed) := imp_and (lvl1 = S lvl2 /\ yellow = yellow) (csteque_eq cs1 (Big pkt cs2 _ _));
R' Csteque lvl1 0 orange cs1 Csteque lvl2 0 _ (Big (Triple _ pkt _) cs2 eq_refl CCOrange) := imp_and (lvl1 = S lvl2 /\ orange = orange) (csteque_eq cs1 (Big pkt cs2 _ _));
R' Csteque lvl1 0 yellow cs1 Csteque lvl2 0 _ (Big (Triple _ pkt _) cs2 eq_refl CCYellow) := imp_and (lvl1 = S lvl2 /\ yellow = yellow) (csteque_eq cs1 (Big pkt cs2 _ _));
R' Csteque lvl1 0 yellow cs1 Csteque lvl2 0 _ (Big (Triple _ pkt _) cs2 eq_refl (CCGreen (G := SomeGreen) (R := NoRed))) := imp_and (lvl1 = S lvl2 /\ yellow = yellow) (csteque_eq cs1 (Big pkt cs2 _ _));
R' Csteque lvl1 0 orange cs1 Csteque lvl2 0 _ (Big (Triple _ pkt _) cs2 eq_refl (CCGreen (G := NoGreen) (R := SomeRed))) := imp_and (lvl1 = S lvl2 /\ orange = orange) (csteque_eq cs1 (Big pkt cs2 _ _));
R' _ _ _ _ _ _ _ _ _ _ := False.
Next Obligation.
  dependent destruction p1. constructor.
Qed.
Next Obligation.
  dependent destruction p1. constructor.
Qed.
Next Obligation.
  dependent destruction p1. constructor.
Qed.
Next Obligation.
  dependent destruction p1. constructor.
Qed.
Next Obligation.
  dependent destruction p1. constructor.
Qed.

Arguments SElt {A lvl C1 C2}.

Definition R {A} (p1 p2 : { '(k, lvl, len, C) : struct_kind * nat * nat * color & structure A k lvl len C }) :=
    match p1, p2 with 
    | existT _ (k1, lvl1, len1, C1) s1, existT _ (k2, lvl2, len2, C2) s2 => R' k1 lvl1 len1 C1 s1 k2 lvl2 len2 C2 s2 
    end.

Lemma wf_element0 {A : Type} {a : A} : Acc R (existT _ (Element, 0, 0, uncolored) (ZElt a)).
Proof.
  constructor. intros y r.
  destruct y as [[[k lvl] C] s].
  destruct k; unfold R in r.
  - destruct C as [G Y R]; destruct G, Y, R; try dependent destruction s; try destruct r.
Qed.

Lemma wf_R {A k lvl len C} {s : structure A k lvl len C} : Acc R (existT _ (k, lvl, len, C) s).
Proof.
  induction s.
  - apply wf_element0.
  - constructor; intros y r.
    destruct y as [[[[k' lvl'] len'] C'] s'].
    destruct k'; unfold R in r; try destruct r.
    + induction lvl'; dependent destruction s'.
      -- apply wf_element0.
      -- unfold R' in r; cbn in r. inversion r. subst.
         constructor; intros y r'.
         destruct y as [[[[k'' lvl''] len''] C''] s''].

Equations suffix'_seq {A} : suffix' A -> list A := 
suffix'_seq (Suff d) := deque_seq d.

Equations prefix'_seq {A C} : prefix' A C -> list A := 
prefix'_seq (Pre2 a b) := [a] ++ [b];
prefix'_seq (Pre3 a b c) := [a] ++ [b] ++ [c];
prefix'_seq (Pre4 a b c d e) := [a] ++ [b] ++ [c] ++ [d] ++ deque_seq e.

Equations max_list {A : Type} (f : A -> nat) (l : list A) : nat := 
max_list _ [] := 0;
max_list f (a :: l) := max (f a) (max_list f l).

Print WellFounded.
Print well_founded.
Print Acc.

Inductive kind : Type := Element | Packet | Csteque.

Equations R : (kind * nat * nat) -> (kind * nat * nat) -> Prop :=  
(* R (Element, lvl1, _) (Element, lvl2, _) := lvl1 < lvl2; *)
R (Element, lvl1, len1) (Packet, lvl2, len2) := lvl1 <= lvl2 /\ len1 <= len2;
R (Element, lvl1, len1) (Csteque, lvl2, len2) := lvl1 <= lvl2 /\ len1 <= S len2;
R (Packet, _, _) (Element, _, _) := False;
R (Packet, lvl1, len1) (Packet, lvl2, len2) := lvl1 <= S lvl2 /\ len1 < len2;
R (Packet, lvl1, len1) (Csteque, lvl2, len2) := lvl1 <= lvl2;
(* R (Csteque, lvl1, len1) (Element, lvl2, len2) := lvl1 <= lvl2 /\ len1 <= len2; *)
R (Csteque, _, _) (Packet, _ , _) := False;
(* R (Csteque, _, nbr1) (Csteque, _, nbr2) := nbr1 < nbr2; *)
R (_, lvl1, len1) (_, lvl2, len2) := (lvl1 < lvl2 /\ len1 <= len2) \/ (lvl1 <= lvl2 /\ len1 < len2).

(* Lemma double_le_0_r {n m : nat} : n <= 0 /\ m <= 0 -> n = 0 /\ m = 0.
Proof.
  intros [llvl llen]. 
  apply (PeanoNat.Nat.le_0_r _) in llvl;
  apply (PeanoNat.Nat.le_0_r _) in llen. 
  auto.
Qed.

Lemma double_nle_succ_0 {n m : nat} {P : Prop} : (n < 0 /\ m <= 0) \/ (n <= 0 /\ m < 0) -> P.
Proof.
  intros [[sineq ineq] | [ineq sineq]]; 
  exfalso;
  unfold lt in sineq; apply (PeanoNat.Nat.nle_succ_0 _ sineq).
Qed.

Theorem strong_induction:
    forall P : nat -> Prop,
    P 0 ->
    (forall m : nat, (forall k : nat, (k < m -> P k)) -> P m) ->
    forall n : nat, P n.
Proof.
  intros P P0 Psind.
  assert (forall n : nat, forall k : nat, k <= n -> P k) as big_ind.
  {
    induction n; intros k e.
    - apply (PeanoNat.Nat.le_0_r _) in e; subst. assumption.
    - apply (Lt.le_lt_or_eq_stt _ _) in e;
      destruct e as [neq%(le_S_n _ _) | eq].
      + apply IHn. assumption.
      + subst. apply Psind. intros k neq%(le_S_n _ _).
        apply IHn. assumption.
  }
  intro n. apply (big_ind n _). constructor.
Qed.

(* Local Ltac strong_induction n := 
  match goal with 
  | |- ?P n => apply (strong_induction P _ _ n)
  end. *)

Lemma wf_element00 : Acc R (Element, 0, 0).
Proof.
  constructor. intros [[k lvl] len] r.
  destruct k; unfold R in r.
  - apply (double_nle_succ_0 r). 
  - destruct r.
  - apply (double_nle_succ_0 r).
Qed.

Lemma wf_packet00 : Acc R (Packet, 0, 0).
Proof.
  constructor. intros [[k lvl] len] r.
  destruct k; unfold R in r.
  - apply double_le_0_r in r. destruct r; subst.
    apply wf_element00.
  - apply (double_nle_succ_0 r).
  - destruct r.
Qed.

Lemma wf_csteque00 : Acc R (Csteque, 0, 0).
Proof.
  constructor. intros [[k lvl] len] r.
  destruct k; unfold R in r.
  - apply double_le_0_r in r. destruct r; subst.
    apply wf_element00.
  - apply double_le_0_r in r. destruct r; subst.
    apply wf_packet00.
  - apply (double_nle_succ_0 r).
Qed.

Lemma wf_element0n : forall n, (forall k kind, k < n -> Acc R (kind, 0, k)) -> Acc R (Element, 0, n).
Proof.
  intros n IH; constructor; intros [[k lvl] len] r.
  destruct k; unfold R in r.
  - destruct r as [[sineq%(PeanoNat.Nat.nle_succ_0 _) ?] | [ineq%(PeanoNat.Nat.le_0_r _) sineq]].
    + destruct sineq.
    + subst. apply IH. assumption.
  - destruct r.
  - destruct r as [[sineq%(PeanoNat.Nat.nle_succ_0 _) ?] | [ineq%(PeanoNat.Nat.le_0_r _) sineq]].
    + destruct sineq.
    + subst. apply IH. assumption.
Qed.

Lemma wf_packet0n : forall n, (forall k kind, k < n -> Acc R (kind, 0, k)) -> Acc R (Packet, 0, n).
Proof.
  intros n IH; constructor; intros [[k lvl] len] r.
  destruct k; unfold R in r.
  - destruct r as [ineq%(PeanoNat.Nat.le_0_r _) ?]; subst.
    apply wf_element0n.
    intros k kind e. apply IH. eapply PeanoNat.Nat.lt_le_trans. exact e. assumption.
  - destruct r as [[sineq%(PeanoNat.Nat.nle_succ_0 _) ?] | [ineq%(PeanoNat.Nat.le_0_r _) sineq]].
    + destruct sineq.
    + subst. apply IH. assumption.
  - destruct r.
Qed.

Lemma wf_csteque0n : forall n, (forall k kind, k < n -> Acc R (kind, 0, k)) -> Acc R (Csteque, 0, n).
Proof.
  intros n IH; constructor; intros [[k lvl] len] r.
  destruct k; unfold R in r.
  - destruct r as [ineq%(PeanoNat.Nat.le_0_r _) ?]; subst.
    apply wf_element0n.
    intros k kind e. apply IH. eapply PeanoNat.Nat.lt_le_trans. exact e. assumption.
  - destruct r as [ineq%(PeanoNat.Nat.le_0_r _) ?]; subst.
    apply wf_packet0n.
    intros k kind e. apply IH. eapply PeanoNat.Nat.lt_le_trans. exact e. assumption.
  - destruct r as [[sineq%(PeanoNat.Nat.nle_succ_0 _) ?] | [ineq%(PeanoNat.Nat.le_0_r _) sineq]].
    + destruct sineq.
    + subst. apply IH. assumption.
Qed.

Lemma wfR : WellFounded R.
Proof.
  unfold WellFounded, well_founded. intros [[ka lvla] lena]. 
  induction lvla using strong_induction.
  - revert ka.
    induction lena using strong_induction.
    + destruct ka; [apply wf_element00 | apply wf_packet00 | apply wf_csteque00].
    + intros []; [apply wf_element0n | apply wf_packet0n | apply wf_csteque0n]; auto.
  - revert H. revert ka.
    induction lena using strong_induction; intros ka IH.
    + admit.
    + admit.
Admitted. *)
    
Inductive seq_kind : Type := SElement | FPacket | RPacket | SCsteque.
Definition seq_kind_to_kind (sk : seq_kind) : kind := 
  match sk with 
  | SElement => Element
  | FPacket | RPacket => Packet 
  | SCsteque => Csteque
  end.

Definition structure (k : kind) A lvl len C : Type := 
  match k with 
  | Element => element A lvl 
  | Packet => lvl_packet A lvl len C 
  | Csteque => lvl_csteque A lvl C 
  end.

Equations to_seq (sk : seq_kind) {A} lvl len {C} :
  structure (seq_kind_to_kind sk) A lvl len C -> list A := 
to_seq SElement 0 _ (ZElt a) := [a];
to_seq SElement _ len (SElt p cs) := 
    concat (map (to_seq SElement _ len) (prefix'_seq p)) ++
    to_seq SCsteque _ len cs;
to_seq FPacket _ 0 Hole := [];
to_seq FPacket lvl (S len) (Triple p pkt _) := 
    concat (map (to_seq SElement lvl (S len)) (prefix'_seq p)) ++
    to_seq FPacket (S lvl) len pkt;
to_seq RPacket _ 0 Hole := [];
to_seq RPacket lvl (S len) (Triple _ pkt s) :=
    to_seq RPacket (S lvl) len pkt ++
    concat (map (to_seq SElement lvl 0) (suffix'_seq s));
to_seq SCsteque lvl len (Small s) := 
    concat (map (to_seq SElement lvl (1 - len)) (suffix'_seq s));
to_seq SCsteque lvl (S len) (Big pkt cs eq_refl _) :=
    to_seq FPacket lvl _ pkt ++
    to_seq SCsteque _ len cs ++
    to_seq RPacket lvl _ pkt.


(* A essayer : faire un well formed order comme sur ma feuille ou 
   faire la fueled version. *)

Fixpoint element_fuel {A lvl} (elt : element A lvl) : nat := 
  let fix list_fuel {A lvl} (l : list (element A lvl)) {struct l} : nat := match l with 
    | [] => 0 
    | e :: l => max (element_fuel e) (list_fuel l) 
  end in 
  let fix packet_fuel {A lvl len C} (pkt : lvl_packet A lvl len C) {struct pkt} : nat := match pkt with 
    | Hole => 0
    | Triple p pkt s => 1 + max (max 
        (list_fuel (prefix'_seq p))
        (packet_fuel pkt))
        (list_fuel (suffix'_seq s))
  end in
  let fix csteque_fuel {A lvl C} (cs : lvl_csteque A lvl C) {struct cs} : nat := match cs with 
    | Small s => 1 + list_fuel (suffix'_seq s)
    | Big pkt cs _ _ => 1 + max (packet_fuel pkt) (csteque_fuel cs)
  end in match elt with 
  | ZElt _ => 1
  | SElt p cs => 1 + max 
      (list_fuel (prefix'_seq p))
      (csteque_fuel cs)
  end.

Equations csteque_get_fuel {A lvl C} : lvl_csteque A lvl C -> nat := 
csteque_get_fuel (Small s) := max_list element_get_fuel (suffix'_seq s);
csteque_get_fuel (Big pkt cs eq_refl _) := 1 + max (packet_get_fuel pkt) (csteque_get_fuel cs)

with packet_get_fuel {A lvl len C} : lvl_packet A lvl len C -> nat := 
packet_get_fuel Hole := 0;
packet_get_fuel (Triple p pkt s) := 1 + 
    max (max_list element_get_fuel (prefix'_seq p)) 
    (max (packet_get_fuel pkt)
    (max_list element_get_fuel (suffix'_seq s)))

with element_get_fuel {A lvl} : element A lvl -> nat :=
element_get_fuel (ZElt _) := 1;
element_get_fuel (SElt p cs) := 1 + max (max_list element_get_fuel (prefix'_seq p)) (csteque_get_fuel cs).

#[local] Obligation Tactic := try first [assumption | exact uncolored | lia].

Equations fueled_element_seq {A lvl} (fuel : nat) : element A lvl -> list A := 
fueled_element_seq 0 _ := [];
fueled_element_seq (S _) (ZElt a) := [a];
fueled_element_seq (S fuel) (SElt p cs) := 
    concat (map (fueled_element_seq fuel) (prefix'_seq p)) ++
    fueled_csteque_seq fuel cs

with fueled_packet_front_seq {A lvl len C} (fuel : nat) : lvl_packet A lvl len C -> list A := 
fueled_packet_front_seq 0 _ := [];
fueled_packet_front_seq (S _) Hole := [];
fueled_packet_front_seq (S fuel) (Triple p pkt _) := 
    concat (map (fueled_element_seq fuel) (prefix'_seq p)) ++
    fueled_packet_front_seq fuel pkt 

with fueled_packet_rear_seq {A lvl len C} (fuel : nat) : lvl_packet A lvl len C -> list A :=
fueled_packet_rear_seq 0 _ := [];
fueled_packet_rear_seq (S _) Hole := [];
fueled_packet_rear_seq (S fuel) (Triple _ pkt s) :=
    fueled_packet_rear_seq fuel pkt ++
    concat (map (fueled_element_seq fuel) (suffix'_seq s))

with fueled_csteque_seq {A lvl C} (fuel : nat) : lvl_csteque A lvl C -> list A :=
fueled_csteque_seq 0 _ := [];
fueled_csteque_seq (S fuel) (Small s) := 
    concat (map (fueled_element_seq fuel) (suffix'_seq s));
fueled_csteque_seq (S fuel) (Big pkt cs eq_refl _) :=
    fueled_packet_front_seq fuel pkt ++
    fueled_csteque_seq fuel cs ++
    fueled_packet_rear_seq fuel pkt.

Definition element_seq {A lvl dpt} := 
    structure_seq Element (A := A) (C := uncolored) (lvl := lvl) (len := 0) (dpt := dpt).
Definition csteque_seq {A C lvl dpt} := 
    structure_seq CSteque (A := A) (C := C) (lvl := lvl) (len := 0) (dpt := dpt).

Definition suffix_seq {A lvl dpt} (s : suffix A lvl dpt) := 
    map_concat element_seq (suffix'_seq s).
Definition prefix_seq {A lvl dpt C} (p : prefix A lvl dpt C) :=
    map_concat element_seq (prefix'_seq p).

Equations steque_seq {A} : steque A -> list A :=
steque_seq (T cs) := csteque_seq cs.

Unset Equations Transparent.

(* Elements *)

Notation "? x" := (@exist _ _ x _) (at level 100).

(* The empty colored steque. *)

Equations cempty {A lvl dpt} : { cs : lvl_csteque A lvl (S dpt) green | csteque_seq cs = [] } :=
cempty with dempty => { | ? d := ? Small (Suff d) }.
Next Obligation.
  intros * e. cbn beta in *.
  cbn. rewrite e. reflexivity.
Qed.

(* Functions *)  

Equations make_green {A lvl dpt C}
    (p : prefix A lvl dpt green)
    (cs : lvl_csteque A (S lvl) (S dpt) C)
    (s : suffix A lvl dpt) :
    { cs' : lvl_csteque A lvl (S (S dpt)) green | csteque_seq cs' = prefix_seq p ++
                                                                csteque_seq cs ++
                                                                suffix_seq s } :=
make_green p (Small s') s := ? Big (Triple p Hole s) (Small s') _ _;
make_green p (Big pkt cs eq_refl CCGreen) s :=
    ? Big (Triple p Hole s) (Big pkt cs _ CCGreen) _ CCGreen;
make_green p (Big pkt cs eq_refl CCYellow) s :=
    ? Big (Triple p pkt s) cs _ CCGreen;
make_green p (Big pkt cs eq_refl CCOrange) s :=
    ? Big (Triple p pkt s) cs _ CCGreen;
make_green p (Big pkt cs eq_refl CCRed) s :=
    ? Big (Triple p Hole s) (Big pkt cs _ CCRed) _ CCGreen.

(* let green
: type a c.
  (a, [`green]) prefix -> (a pair, c) csteque -> a suffix -> (a, [`green]) csteque
= fun p csteque s ->
  match csteque with
  | Suffix small -> G (Triple (p, HOLE, s), Suffix small)
  | Y (triple, k) -> G (Triple (p, triple, s), k)
  | Yr (triple, k) -> G (Triple (p, triple, s), k)
  | G (triple, k) -> G (Triple (p, HOLE, s), G (triple, k))
  | R (triple, k) -> G (Triple (p, HOLE, s), R (triple, k)) *)