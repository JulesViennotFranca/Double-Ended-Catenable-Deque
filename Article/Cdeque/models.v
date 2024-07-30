From Coq Require Import List.
Import ListNotations.
From Equations Require Import Equations.
Require Import Coq.Program.Equality.

From Deque Require Import ncdeque.
From Cdeque Require Import buffer types.

Fixpoint stored_triple_seq {A : Type} {lvl : nat} (strd : stored_triple A lvl) {struct strd} : list A :=
  let buffer_seq {B lvl q} (b : buffer.t (stored_triple B lvl) q) : list B :=
    map_buffer (@stored_triple_seq B) b in
  let storage_left_seq {B lvl k e C} (st : storage B lvl k e C) : list B :=
    match st with
    | Only_end p     => buffer_seq p
    | Left_end p _   => buffer_seq p
    | Right_end p _  => buffer_seq p
    | Only_st _ p _  => buffer_seq p
    | Left_st _ p _  => buffer_seq p
    | Right_st _ p _ => buffer_seq p
    end in
  let storage_right_seq {B lvl k e C} (st : storage B lvl k e C) : list B :=
    match st with
    | Only_end _     => []
    | Left_end _ s   => buffer_seq s
    | Right_end _ s  => buffer_seq s
    | Only_st _ _ s  => buffer_seq s
    | Left_st _ _ s  => buffer_seq s
    | Right_st _ _ s => buffer_seq s
    end in
  let fix chain_seq {B lvl pk k e Cl Cr} (c : chain B lvl pk k e Cl Cr) {struct c} : list B :=
    let fix body_left_seq {B hlvl tlvl hk tk} (bd : body B hlvl tlvl hk tk) {struct bd} : list B :=
      match bd with
      | Hole => []
      | Only_yellow hd bd => storage_left_seq hd ++ body_left_seq bd
      | Only_orange hd bd => storage_left_seq hd ++ body_left_seq bd
      | Pair_yellow hd bd _ => storage_left_seq hd ++ body_left_seq bd
      | Pair_orange hd cl bd =>
        storage_left_seq hd ++ chain_seq cl ++ body_left_seq bd
      end in
    let fix body_right_seq {B hlvl tlvl hk tk} (bd : body B hlvl tlvl hk tk) {struct bd} : list B :=
      match bd with
      | Hole => []
      | Only_yellow hd bd => body_right_seq bd ++ storage_right_seq hd
      | Only_orange hd bd => body_right_seq bd ++ storage_right_seq hd
      | Pair_yellow hd bd cr =>
        body_right_seq bd ++ chain_seq cr ++ storage_right_seq hd
      | Pair_orange hd _ bd => body_right_seq bd ++ storage_right_seq hd
      end in
    let packet_left_seq {B hlvl tlvl k e C} (pkt : packet B hlvl tlvl k e C) : list B :=
      let '(Packet bd tl) := pkt in body_left_seq bd ++ storage_left_seq tl in
    let packet_right_seq {B hlvl tlvl k e C} (pkt : packet B hlvl tlvl k e C) : list B :=
      let '(Packet bd tl) := pkt in storage_right_seq tl ++ body_right_seq bd in
    match c with
    | Empty => []
    | Only_chain _ pkt rest =>
      packet_left_seq pkt ++ chain_seq rest ++ packet_right_seq pkt
    | Pair_chain cl cr => chain_seq cl ++ chain_seq cr
    end in
  match strd with
  | Ground a => [a]
  | Small s => buffer_seq s
  | Big p child s => buffer_seq p ++ chain_seq child ++ buffer_seq s
  end.

Set Equations Transparent.

Definition strd_buffer_seq {A lvl q} (b : buffer.t (stored_triple A lvl) q) : list A :=
  map_buffer (@stored_triple_seq A) b.

Definition strd_storage_left_seq {A lvl k e C} (st : storage A lvl k e C) : list A :=
  match st with
  | Only_end p     => strd_buffer_seq p
  | Left_end p _   => strd_buffer_seq p
  | Right_end p _  => strd_buffer_seq p
  | Only_st _ p _  => strd_buffer_seq p
  | Left_st _ p _  => strd_buffer_seq p
  | Right_st _ p _ => strd_buffer_seq p
  end.

Definition strd_storage_right_seq {A lvl k e C} (st : storage A lvl k e C) : list A :=
  match st with
  | Only_end _     => []
  | Left_end _ s   => strd_buffer_seq s
  | Right_end _ s  => strd_buffer_seq s
  | Only_st _ _ s  => strd_buffer_seq s
  | Left_st _ _ s  => strd_buffer_seq s
  | Right_st _ _ s => strd_buffer_seq s
  end.

Fixpoint chain_seq {A : Type} {lvl : nat} {pk k : kind} {e : ending} {Cl Cr : color}
  (c : chain A lvl pk k e Cl Cr) {struct c} : list A :=
  let fix body_left_seq {B hlvl tlvl hk tk} (bd : body B hlvl tlvl hk tk) {struct bd} : list B :=
    match bd with
    | Hole => []
    | Only_yellow hd bd => strd_storage_left_seq hd ++ body_left_seq bd
    | Only_orange hd bd => strd_storage_left_seq hd ++ body_left_seq bd
    | Pair_yellow hd bd _ => strd_storage_left_seq hd ++ body_left_seq bd
    | Pair_orange hd cl bd =>
      strd_storage_left_seq hd ++ chain_seq cl ++ body_left_seq bd
    end in
  let fix body_right_seq {B hlvl tlvl hk tk} (bd : body B hlvl tlvl hk tk) {struct bd} : list B :=
    match bd with
    | Hole => []
    | Only_yellow hd bd => body_right_seq bd ++ strd_storage_right_seq hd
    | Only_orange hd bd => body_right_seq bd ++ strd_storage_right_seq hd
    | Pair_yellow hd bd cr =>
      body_right_seq bd ++ chain_seq cr ++ strd_storage_right_seq hd
    | Pair_orange hd _ bd => body_right_seq bd ++ strd_storage_right_seq hd
    end in
  let packet_left_seq {B hlvl tlvl k e C} (pkt : packet B hlvl tlvl k e C) : list B :=
    let '(Packet bd tl) := pkt in
    body_left_seq bd ++ strd_storage_left_seq tl
  in
  let packet_right_seq {B hlvl tlvl k e C} (pkt : packet B hlvl tlvl k e C) : list B :=
    let '(Packet bd tl) := pkt in
    strd_storage_right_seq tl ++ body_right_seq bd
  in
  match c with
  | Empty => []
  | Only_chain _ pkt rest =>
    packet_left_seq pkt ++ chain_seq rest ++ packet_right_seq pkt
  | Pair_chain cl cr => chain_seq cl ++ chain_seq cr
  end.

Equations buffer_seq {A lvl q} : buffer.t (stored_triple A lvl) q -> list A :=
buffer_seq b := concat (map stored_triple_seq (buffer.seq b)).

Lemma correct_buffer_seq {A lvl q} (b : buffer.t (stored_triple A lvl) q) :
  strd_buffer_seq b = buffer_seq b.
Proof.
  unfold strd_buffer_seq.
  rewrite buffer.correct_mapping.
  reflexivity.
Qed.

Definition prefix_seq {A lvl q} : prefix A lvl q -> list A := buffer_seq.
Definition suffix_seq {A lvl q} : suffix A lvl q -> list A := buffer_seq.

Equations green_buffer_seq {A lvl} : green_buffer A lvl -> list A :=
green_buffer_seq (Gbuf b) := buffer_seq b.

Equations stored_buffer_seq {A lvl} : stored_buffer A lvl -> list A :=
stored_buffer_seq (Sbuf b) := buffer_seq b.

Equations storage_left_seq {A lvl k e C} : storage A lvl k e C -> list A :=
storage_left_seq (Only_end p)     := prefix_seq p;
storage_left_seq (Left_end p _)   := prefix_seq p;
storage_left_seq (Right_end p _)  := prefix_seq p;
storage_left_seq (Only_st _ p _)  := prefix_seq p;
storage_left_seq (Left_st _ p _)  := prefix_seq p;
storage_left_seq (Right_st _ p _) := prefix_seq p.

Equations storage_right_seq {A lvl k e C} : storage A lvl k e C -> list A :=
storage_right_seq (Only_end _)      := [];
storage_right_seq (Left_end _ s)    := suffix_seq s;
storage_right_seq (Right_end _ s)   := suffix_seq s;
storage_right_seq (Only_st _ _ s)   := suffix_seq s;
storage_right_seq (Left_st _ _ s)   := suffix_seq s;
storage_right_seq (Right_st _ _ s)  := suffix_seq s.

Lemma correct_storage_left_seq {A lvl k e C} (st : storage A lvl k e C) :
  strd_storage_left_seq st = storage_left_seq st.
Proof. destruct st; cbn; apply correct_buffer_seq. Qed.

Lemma correct_storage_right_seq {A lvl k e C} (st : storage A lvl k e C) :
  strd_storage_right_seq st = storage_right_seq st.
Proof. destruct st; cbn; try reflexivity; apply correct_buffer_seq. Qed.

Equations body_left_seq {A : Type} {hlvl tlvl : nat} {hk tk : kind} :
  body A hlvl tlvl hk tk -> list A :=
body_left_seq Hole := [];
body_left_seq (Only_yellow hd bd) :=
  storage_left_seq hd ++ body_left_seq bd;
body_left_seq (Only_orange hd bd) :=
  storage_left_seq hd ++ body_left_seq bd;
body_left_seq (Pair_yellow hd bd _) :=
  storage_left_seq hd ++ body_left_seq bd;
body_left_seq (Pair_orange hd cl bd) :=
  storage_left_seq hd ++ chain_seq cl ++ body_left_seq bd.

Equations body_right_seq {A : Type} {hlvl tlvl : nat} {hk tk : kind} :
  body A hlvl tlvl hk tk -> list A :=
body_right_seq Hole := [];
body_right_seq (Only_yellow hd bd) :=
  body_right_seq bd ++ storage_right_seq hd;
body_right_seq (Only_orange hd bd) :=
  body_right_seq bd ++ storage_right_seq hd;
body_right_seq (Pair_yellow hd bd cr) :=
  body_right_seq bd ++ chain_seq cr ++ storage_right_seq hd;
body_right_seq (Pair_orange hd _ bd) :=
  body_right_seq bd ++ storage_right_seq hd.

Equations packet_left_seq {A : Type} {hlvl tlvl : nat} {k e C} :
  packet A hlvl tlvl k e C -> list A :=
packet_left_seq (Packet bd tl) := body_left_seq bd ++ storage_left_seq tl.

Equations packet_right_seq {A : Type} {hlvl tlvl : nat} {k e C} :
  packet A hlvl tlvl k e C -> list A :=
packet_right_seq (Packet bd tl) := storage_right_seq tl ++ body_right_seq bd.

Equations ne_chain_seq {A lvl pk k Cl Cr} :
  non_ending_chain A lvl pk k Cl Cr -> list A :=
ne_chain_seq (NE_chain c) := chain_seq c.

Equations triple_seq {A lvl k C} : triple A lvl k C -> list A :=
triple_seq (Triple _ hd child) :=
  storage_left_seq hd ++ chain_seq child ++ storage_right_seq hd.

Equations lr_triple_seq {A lvl k C} : left_right_triple A lvl k C -> list A :=
lr_triple_seq (Not_enough v) := concat (map stored_triple_seq (vector_seq v));
lr_triple_seq (Ok_lrt t) := triple_seq t.

Equations six_stored_triple_seq {A lvl} : six_stored_triple A lvl -> list A :=
six_stored_triple_seq (a1, a2, a3, a4, a5, a6) :=
  stored_triple_seq a1 ++ stored_triple_seq a2 ++ stored_triple_seq a3 ++
  stored_triple_seq a4 ++ stored_triple_seq a5 ++ stored_triple_seq a6.

Equations pt_triple_seq {A lvl pk k} : partial_triple A lvl pk k -> list A :=
pt_triple_seq Zero_element := [];
pt_triple_seq (Six_elements six) := six_stored_triple_seq six;
pt_triple_seq (Ok_pt t) := triple_seq t.

Equations sandwich_seq {A B C : Type} :
  (A -> list C) -> (B -> list C) -> sandwich A B -> list C :=
sandwich_seq A_seq _ (Alone a) := A_seq a;
sandwich_seq A_seq B_seq (Sandwich a m z) := A_seq a ++ B_seq m ++ A_seq z.

Equations semi_deque_seq {A lvl} : semi_deque A lvl -> list A :=
semi_deque_seq (Semi c) := chain_seq c.

Equations deque_seq {A : Type} : deque A -> list A :=
deque_seq (T c) := chain_seq c.

Unset Equations Transparent.

Lemma stored_triple_ground [A] (a : A) :
  stored_triple_seq (Ground a) = [a].
Proof. reflexivity. Qed.

Lemma stored_triple_small [A lvl q] (s : suffix A lvl (3 + q)) :
  stored_triple_seq (Small s) = suffix_seq s.
Proof. cbn. apply correct_buffer_seq. Qed.

Lemma stored_triple_big [A lvl qp qs pk e Cl Cr]
  (p : prefix A lvl (3 + qp))
  (child : chain A (S lvl) pk Only e Cl Cr)
  (s : suffix A lvl (3 + qs)) :
  stored_triple_seq (Big p child s) =
    prefix_seq p ++ chain_seq child ++ suffix_seq s.
Proof.
  cbn. repeat apply div_app2;
  try apply correct_buffer_seq.
  reflexivity.
Qed.

Lemma chain_empty (A : Type) (lvl : nat) :
  chain_seq (A := A) (lvl := lvl) Empty = [].
Proof. reflexivity. Qed.

Lemma empty_chain_seq [A lvl pk Cl Cr] (c : chain A lvl pk Only Is_end Cl Cr) :
  chain_seq c = [].
Proof.
  dependent destruction c. apply chain_empty.
Qed.

Lemma correct_body_left_seq {A hlvl tlvl hk tk} (bd : body A hlvl tlvl hk tk) :
  (fix body_left_seq (B : Type) (hlvl0 tlvl0 : nat) (hk0 tk0 : kind) (bd0 : body B hlvl0 tlvl0 hk0 tk0) {struct bd0} : list B := match bd0 with
  | Hole => []
  | @Only_yellow _ hlvl1 tlvl1 hk1 tk1 hd bd1 => strd_storage_left_seq hd ++ body_left_seq B (S hlvl1) tlvl1 Only tk1 bd1
  | @Only_orange _ hlvl1 tlvl1 hk1 tk1 hd bd1 => strd_storage_left_seq hd ++ body_left_seq B (S hlvl1) tlvl1 Only tk1 bd1
  | @Pair_yellow _ hlvl1 tlvl1 hk1 tk1 _ hd bd1 _ => strd_storage_left_seq hd ++ body_left_seq B (S hlvl1) tlvl1 Left tk1 bd1
  | @Pair_orange _ hlvl1 tlvl1 hk1 tk1 hd cl bd1 => strd_storage_left_seq hd ++ chain_seq cl ++ body_left_seq B (S hlvl1) tlvl1 Right tk1 bd1
  end) A hlvl tlvl hk tk bd = body_left_seq bd.
Proof.
  induction bd;
  repeat apply div_app2;
  try reflexivity;
  try apply correct_storage_left_seq;
  apply IHbd.
Qed.

Lemma correct_body_right_seq {A hlvl tlvl hk tk} (bd : body A hlvl tlvl hk tk) :
  (fix body_right_seq (B : Type) (hlvl0 tlvl0 : nat) (hk0 tk0 : kind) (bd0 : body B hlvl0 tlvl0 hk0 tk0) {struct bd0} : list B := match bd0 with
  | Hole => []
  | @Only_yellow _ hlvl1 tlvl1 hk1 tk1 hd bd1 => body_right_seq B (S hlvl1) tlvl1 Only tk1 bd1 ++ strd_storage_right_seq hd
  | @Only_orange _ hlvl1 tlvl1 hk1 tk1 hd bd1 => body_right_seq B (S hlvl1) tlvl1 Only tk1 bd1 ++ strd_storage_right_seq hd
  | @Pair_yellow _ hlvl1 tlvl1 hk1 tk1 _ hd bd1 cr => body_right_seq B (S hlvl1) tlvl1 Left tk1 bd1 ++ chain_seq cr ++ strd_storage_right_seq hd
  | @Pair_orange _ hlvl1 tlvl1 hk1 tk1 hd _ bd1 => body_right_seq B (S hlvl1) tlvl1 Right tk1 bd1 ++ strd_storage_right_seq hd
  end) A hlvl tlvl hk tk bd = body_right_seq bd.
Proof.
  induction bd;
  repeat apply div_app2;
  try reflexivity;
  try apply correct_storage_right_seq;
  apply IHbd.
Qed.

Lemma chain_only [A hlvl tlvl k pk e C Cl Cr]
  (reg : chain_regularity C Cl Cr)
  (pkt : packet A hlvl tlvl k e C)
  (c : chain A (S tlvl) pk Only e Cl Cr) :
  chain_seq (Only_chain reg pkt c) =
    packet_left_seq pkt ++ chain_seq c ++ packet_right_seq pkt.
Proof.
  cbn. repeat apply div_app2;
  try reflexivity;
  destruct pkt as [??????? bd tl];
  apply div_app2.
  - apply correct_body_left_seq.
  - apply correct_storage_left_seq.
  - apply correct_storage_right_seq.
  - apply correct_body_right_seq.
Qed.

Lemma chain_pair [A lvl Cl Cr]
  (cl : chain A lvl Only Left  Not_end Cl Cl)
  (cr : chain A lvl Only Right Not_end Cr Cr) :
  chain_seq (Pair_chain cl cr) = chain_seq cl ++ chain_seq cr.
Proof. reflexivity. Qed.