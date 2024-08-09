From Coq Require Import List.
Import ListNotations.
From Equations Require Import Equations.

From Deque Require Import ncdeque buffer types.

Set Equations Transparent.

Fixpoint path_seq {A lvl K C} (p : path A lvl K C) {struct p} : list A :=
  let ne_cdeque_seq {B lvl C} (cd : non_empty_cdeque B lvl C) : list B :=
    match cd with
    | Only_path p => path_seq p
    | Pair_green pl pr => path_seq pl ++ path_seq pr
    | Pair_red pl pr => path_seq pl ++ path_seq pr
    end in
  let cdeque_seq {B lvl C} (cd : cdeque B lvl C) : list B :=
    match cd with
    | Empty => []
    | NonEmpty necd => ne_cdeque_seq necd
    end in
  let fix stored_triple_seq {B lvl} (st : stored_triple B lvl) {struct st} : list B :=
    let buffer_seq {B lvl q} (b : buffer.t (stored_triple B lvl) q) : list B :=
      map_buffer (@stored_triple_seq B) b in
    match st with
    | ST_ground b => [b]
    | ST_small p => buffer_seq p
    | ST_triple p cd s => buffer_seq p ++ cdeque_seq cd ++ buffer_seq s
    end in
  let buffer_seq {B lvl q} (b : buffer.t (stored_triple B lvl) q) : list B :=
    map_buffer (@stored_triple_seq B) b in
  let fix triple_left_seq {B lvl len is_hole K1 K2 C} (t : triple B lvl len is_hole K1 K2 C) {struct t} : list B :=
    let packet_left_seq {B lvl len pc K} (pkt : packet B lvl len pc K) : list B :=
      match pkt with
      | Only_child t => triple_left_seq t
      | Left_child t _ => triple_left_seq t
      | Right_child p t => path_seq p ++ triple_left_seq t
      end in
    match t with
    | Hole => []
    | Small p _ _ => buffer_seq p
    | Green p cd _ _ => buffer_seq p ++ ne_cdeque_seq cd
    | Yellow p pkt _ _ => buffer_seq p ++ packet_left_seq pkt
    | Orange p pkt _ _ => buffer_seq p ++ packet_left_seq pkt
    | Red p cd _ _ => buffer_seq p ++ ne_cdeque_seq cd
    end in
  let fix triple_right_seq {B lvl len is_hole K1 K2 C} (t : triple B lvl len is_hole K1 K2 C) {struct t} : list B :=
    let packet_right_seq {B lvl len pc K} (pkt : packet B lvl len pc K) : list B :=
      match pkt with
      | Only_child t => triple_right_seq t
      | Left_child t p => triple_right_seq t ++ path_seq p
      | Right_child _ t => triple_right_seq t
      end in
    match t with
    | Hole => []
    | Small _ s _ => buffer_seq s
    | Green _ _ s _ => buffer_seq s
    | Yellow _ pkt s _ => packet_right_seq pkt ++ buffer_seq s
    | Orange _ pkt s _ => packet_right_seq pkt ++ buffer_seq s
    | Red _ _ s _ => buffer_seq s
    end in
  match p with
  | Children natur adopt _ =>
    triple_left_seq natur ++ triple_left_seq adopt ++
    triple_right_seq adopt ++ triple_right_seq natur
  end.

Equations ne_cdeque_seq {A lvl C} : non_empty_cdeque A lvl C -> list A :=
ne_cdeque_seq (Only_path p) := path_seq p;
ne_cdeque_seq (Pair_green pl pd) := path_seq pl ++ path_seq pd;
ne_cdeque_seq (Pair_red pl pd) := path_seq pl ++ path_seq pd.

Equations cdeque_seq {A lvl C} : cdeque A lvl C -> list A :=
cdeque_seq Empty := [];
cdeque_seq (NonEmpty cd) := ne_cdeque_seq cd.

Fixpoint stored_triple_seq {A} {lvl : nat} (st : stored_triple A lvl) {struct st} : list A :=
  let buffer_seq {lvl q} (b : buffer.t (stored_triple A lvl) q) : list A :=
    map_buffer (@stored_triple_seq A) b in
  match st with
  | ST_ground a => [a]
  | ST_small p => buffer_seq p
  | ST_triple p cd s => buffer_seq p ++ cdeque_seq cd ++ buffer_seq s
  end.

Equations buffer_seq {A lvl q} : buffer.t (stored_triple A lvl) q -> list A :=
buffer_seq p := concat (map stored_triple_seq (buffer.seq p)).

Definition path_buffer_seq {A lvl q} (b : buffer.t (stored_triple A lvl) q) : list A :=
  map_buffer ((fix stored_triple_seq (B : Type) (lvl : nat) (st : stored_triple B lvl) {struct st} : list B := match st with
  | ST_ground b => [b]
  | @ST_small _ lvl' q p => map_buffer (stored_triple_seq B) p
  | @ST_triple _ lvl' qp qs _ p cd s =>
    map_buffer (stored_triple_seq B) p ++
    cdeque_seq cd ++
    map_buffer (stored_triple_seq B) s
  end) A) b.

Lemma correct_path_buffer_seq {A lvl q} (b : buffer.t (stored_triple A lvl) q) :
  path_buffer_seq b = buffer_seq b.
Proof.
  unfold path_buffer_seq; simp buffer_seq.
  rewrite buffer.correct_mapping. reflexivity.
Qed.

Fixpoint triple_left_seq {A lvl len is_hole K1 K2 C} (t : triple A lvl len is_hole K1 K2 C) : list A :=
  let packet_left_seq {lvl len pc K} (pkt : packet A lvl len pc K) : list A :=
    match pkt with
    | Only_child t => triple_left_seq t
    | Left_child t _ => triple_left_seq t
    | Right_child p t => path_seq p ++ triple_left_seq t
    end in
  match t with
  | Hole => []
  | Small p _ _ => path_buffer_seq p
  | Green p cd _ _ => path_buffer_seq p ++ ne_cdeque_seq cd
  | Yellow p pkt _ _ => path_buffer_seq p ++ packet_left_seq pkt
  | Orange p pkt _ _ => path_buffer_seq p ++ packet_left_seq pkt
  | Red p cd _ _ => path_buffer_seq p ++ ne_cdeque_seq cd
  end.

Equations packet_left_seq {A lvl len pc K} : packet A lvl len pc K -> list A :=
packet_left_seq (Only_child t) := triple_left_seq t;
packet_left_seq (Left_child t _) := triple_left_seq t;
packet_left_seq (Right_child p t) := path_seq p ++ triple_left_seq t.

Fixpoint triple_right_seq {A lvl len is_hole K1 K2 C} (t : triple A lvl len is_hole K1 K2 C) : list A :=
  let packet_right_seq {lvl len pc K} (pkt : packet A lvl len pc K) : list A :=
    match pkt with
    | Only_child t => triple_right_seq t
    | Left_child t p => triple_right_seq t ++ path_seq p
    | Right_child _ t => triple_right_seq t
    end in
  match t with
  | Hole => []
  | Small _ s _ => path_buffer_seq s
  | Green _ _ s _ => path_buffer_seq s
  | Yellow _ pkt s _ => packet_right_seq pkt ++ path_buffer_seq s
  | Orange _ pkt s _ => packet_right_seq pkt ++ path_buffer_seq s
  | Red _ _ s _ => path_buffer_seq s
  end.

Equations packet_right_seq {A lvl len pc K} : packet A lvl len pc K -> list A :=
packet_right_seq (Only_child t) := triple_right_seq t;
packet_right_seq (Left_child t p) := triple_right_seq t ++ path_seq p;
packet_right_seq (Right_child _ t) := triple_right_seq t.

Equations triple_seq {A lvl len is_hole K1 K2 C} :
  triple A lvl len is_hole K1 K2 C -> list A :=
triple_seq t := triple_left_seq t ++ triple_right_seq t.

Equations pref_left_seq {A lvl} : pref_left A lvl -> list A :=
pref_left_seq (Pref_left pkt t eq_refl) := packet_left_seq pkt ++ triple_seq t ++ packet_right_seq pkt.

Equations pref_right_seq {A lvl} : pref_right A lvl -> list A :=
pref_right_seq (Pref_right pkt t eq_refl) := packet_left_seq pkt ++ triple_seq t ++ packet_right_seq pkt.

Equations buffer_12_seq {A lvl} : buffer_12 A lvl -> list A :=
buffer_12_seq (x, v) := stored_triple_seq x ++ concat (map stored_triple_seq (vector_seq v)).

Equations path_attempt_seq {A lvl K C} : path_attempt A lvl K C -> list A :=
path_attempt_seq (ZeroSix v) := concat (map stored_triple_seq (vector_seq v));
path_attempt_seq (Ok p) := path_seq p;
path_attempt_seq (Any p) := path_seq p.

Equations path_uncolored_seq {A lvl K} : path_uncolored A lvl K -> list A :=
path_uncolored_seq (Six x1 x2 x3 x4 x5 x6) :=
  stored_triple_seq x1 ++ stored_triple_seq x2 ++ stored_triple_seq x3 ++
  stored_triple_seq x4 ++ stored_triple_seq x5 ++ stored_triple_seq x6;
path_uncolored_seq (AnyColor p) := path_seq p.

Equations sdeque_seq {A lvl} : sdeque A lvl -> list A :=
sdeque_seq (Sd cd) := cdeque_seq cd.

Equations unstored_left_seq {A lvl} : unstored A lvl -> list A :=
unstored_left_seq (Unstored p _) := buffer_seq p.

Equations unstored_right_seq {A lvl} : unstored A lvl -> list A :=
unstored_right_seq (Unstored _ sd) := sdeque_seq sd.

Equations sandwich_seq {A lvl} : sandwich A lvl -> list A :=
sandwich_seq (Alone x) := stored_triple_seq x;
sandwich_seq (Sandwich xl sd xr) :=
  stored_triple_seq xl ++ sdeque_seq sd ++ stored_triple_seq xr.

Equations unstored_sandwich_seq {A lvl} : unstored_sandwich A lvl -> list A :=
unstored_sandwich_seq (Unstored_alone p) := buffer_seq p;
unstored_sandwich_seq (Unstored_sandwich p sd s) :=
  buffer_seq p ++ sdeque_seq sd ++ buffer_seq s.

Equations deque_seq {A} : deque A -> list A :=
deque_seq (T cd) := cdeque_seq cd.

Unset Equations Transparent.

Lemma path_children [A lvl nlvl len is_hole K1 K2 G Y O R]
  (natur : triple A lvl len is_hole K1 K2 (Mix NoGreen Y O NoRed))
  (adopt : triple A nlvl 0 false K2 K2 (Mix G NoYellow NoOrange R))
  (e : nlvl = len + lvl) :
  path_seq (Children natur adopt e) =
    triple_left_seq natur ++ triple_seq adopt ++ triple_right_seq natur.
Proof. subst; simp triple_seq; autorewrite with rlist; reflexivity. Qed.

Lemma stored_triple_ground [A] (a : A) : stored_triple_seq (ST_ground a) = [a].
Proof. simpl; reflexivity. Qed.

Lemma stored_triple_small [A lvl q] (p : prefix A lvl (3 + q)) :
  stored_triple_seq (ST_small p) = buffer_seq p.
Proof. apply buffer.correct_mapping. Qed.

Lemma stored_triple_triple [A lvl qp qs C]
  (p : prefix A lvl (3 + qp))
  (cd : cdeque A (S lvl) C)
  (s : suffix A lvl (3 + qs)) :
  stored_triple_seq (ST_triple p cd s) =
    buffer_seq p ++ cdeque_seq cd ++ buffer_seq s.
Proof.
  simpl stored_triple_seq;
  (* Separate prefix, child and suffix cases. *)
  repeat apply div_app2;
(* Handle the simple child case. *)
  try reflexivity;
  (* Finish with the buffers. *)
  apply buffer.correct_mapping.
Qed.

Lemma triple_front_hole (A : Type) (lvl : nat) (K : kind) :
  triple_left_seq (A := A) (lvl := lvl) (K1 := K) Hole = [].
Proof. reflexivity. Qed.

Lemma triple_rear_hole (A : Type) (lvl : nat) (K : kind) :
  triple_right_seq (A := A) (lvl := lvl) (K1 := K) Hole = [].
Proof. reflexivity. Qed.

Lemma triple_front_small [A lvl qp qs K]
  (p : prefix A lvl qp) (s : suffix A lvl qs)
  (ss : small_triple_sizes K qp qs) :
  triple_left_seq (Small p s ss) = buffer_seq p.
Proof. cbn; apply correct_path_buffer_seq. Qed.

Lemma triple_rear_small [A lvl qp qs K]
  (p : prefix A lvl qp) (s : suffix A lvl qs)
  (ss : small_triple_sizes K qp qs) :
  triple_right_seq (Small p s ss) = buffer_seq s.
Proof. cbn; apply correct_path_buffer_seq. Qed.

Lemma triple_front_green [A lvl qp qs K G R]
  (p : prefix A lvl qp)
  (cd : non_empty_cdeque A (S lvl) (Mix G NoYellow NoOrange R))
  (s : suffix A lvl qs)
  (bs : big_triple_sizes 8 K qp qs) :
  triple_left_seq (Green p cd s bs) = buffer_seq p ++ ne_cdeque_seq cd.
Proof.
  cbn; apply div_app2.
  - apply correct_path_buffer_seq.
  - reflexivity.
Qed.

Lemma triple_rear_green [A lvl qp qs K G R]
  (p : prefix A lvl qp)
  (cd : non_empty_cdeque A (S lvl) (Mix G NoYellow NoOrange R))
  (s : suffix A lvl qs)
  (bs : big_triple_sizes 8 K qp qs) :
  triple_right_seq (Green p cd s bs) = buffer_seq s.
Proof. cbn; apply correct_path_buffer_seq. Qed.

Lemma triple_front_yellow [A lvl len qp qs K1 K2]
  (p : prefix A lvl qp)
  (pkt : packet A (S lvl) len Preferred_left K2)
  (s : suffix A lvl qs)
  (bs : big_triple_sizes 7 K1 qp qs) :
  triple_left_seq (Yellow p pkt s bs) = buffer_seq p ++ packet_left_seq pkt.
Proof.
  cbn; apply div_app2.
  - apply correct_path_buffer_seq.
  - reflexivity.
Qed.

Lemma triple_rear_yellow [A lvl len qp qs K1 K2]
  (p : prefix A lvl qp)
  (pkt : packet A (S lvl) len Preferred_left K2)
  (s : suffix A lvl qs)
  (bs : big_triple_sizes 7 K1 qp qs) :
  triple_right_seq (Yellow p pkt s bs) = packet_right_seq pkt ++ buffer_seq s.
Proof.
  cbn; apply div_app2.
  - reflexivity.
  - apply correct_path_buffer_seq.
Qed.

Lemma triple_front_orange [A lvl len qp qs K1 K2]
  (p : prefix A lvl qp)
  (pkt : packet A (S lvl) len Preferred_right K2)
  (s : suffix A lvl qs)
  (bs : big_triple_sizes 6 K1 qp qs) :
  triple_left_seq (Orange p pkt s bs) = buffer_seq p ++ packet_left_seq pkt.
Proof.
  cbn; apply div_app2.
  - apply correct_path_buffer_seq.
  - reflexivity.
Qed.

Lemma triple_rear_orange [A lvl len qp qs K1 K2]
  (p : prefix A lvl qp)
  (pkt : packet A (S lvl) len Preferred_right K2)
  (s : suffix A lvl qs)
  (bs : big_triple_sizes 6 K1 qp qs) :
  triple_right_seq (Orange p pkt s bs) = packet_right_seq pkt ++ buffer_seq s.
Proof.
  cbn; apply div_app2.
  - reflexivity.
  - apply correct_path_buffer_seq.
Qed.

Lemma triple_front_red [A lvl qp qs K]
  (p : prefix A lvl qp)
  (cd : non_empty_cdeque A (S lvl) green)
  (s : suffix A lvl qs)
  (bs : big_triple_sizes 5 K qp qs) :
  triple_left_seq (Red p cd s bs) = buffer_seq p ++ ne_cdeque_seq cd.
Proof.
  cbn; apply div_app2.
  - apply correct_path_buffer_seq.
  - reflexivity.
Qed.

Lemma triple_rear_red [A lvl qp qs K]
  (p : prefix A lvl qp)
  (cd : non_empty_cdeque A (S lvl) green)
  (s : suffix A lvl qs)
  (bs : big_triple_sizes 5 K qp qs) :
  triple_right_seq (Red p cd s bs) = buffer_seq s.
Proof. cbn; apply correct_path_buffer_seq. Qed.

