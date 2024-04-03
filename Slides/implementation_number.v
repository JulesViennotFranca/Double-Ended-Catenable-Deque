From Coq Require Import ZArith Lia.
From Equations Require Import Equations.

Inductive phantom : Type :=
  | PGreen
  | PNotGreen
  | PYellow
  | PNotYellow
  | PRed 
  | PNotRed
  | PColor : phantom -> phantom -> phantom -> phantom.

Derive NoConfusion for phantom.

Notation is_green := (PColor PGreen PNotYellow PNotRed).
Notation is_yellow := (PColor PNotGreen PYellow PNotRed).
Notation is_red := (PColor PNotGreen PNotYellow PRed).

Inductive seq : phantom -> Type :=
  | Hole : seq (PColor PNotGreen PNotYellow PNotRed)
  | Zero : forall {Y}, seq (PColor PNotGreen Y PNotRed) -> seq is_green
  | One  : forall {Y}, seq (PColor PNotGreen Y PNotRed) -> seq is_yellow
  | Two  : forall {Y}, seq (PColor PNotGreen Y PNotRed) -> seq is_red.

Inductive tree : phantom -> Type :=
  | Null   : tree is_green
  | Green  : forall {G R}, seq is_green  -> tree (PColor G PNotYellow R) -> tree is_green
  | Yellow : forall {G R}, seq is_yellow -> tree (PColor G PNotYellow R) -> tree is_yellow 
  | Red    :               seq is_red    -> tree is_green                -> tree is_red.

Inductive nbr : Type :=
  | T : forall {G Y}, tree (PColor G Y PNotRed) -> nbr.

Equations ensure_green {G R} (t : tree (PColor G PNotYellow R)) : tree is_green :=
ensure_green Null := Null;
ensure_green (Green zero t) := Green zero t;
ensure_green (Red (Two Hole) Null) := Green (Zero (One Hole)) Null;
ensure_green (Red (Two Hole) (Green (Zero ones) t)) := Green (Zero (One ones)) t;
ensure_green (Red (Two (One ones)) t) := Green (Zero Hole) (Red (Two ones) t).

Equations succ (n : nbr) : nbr :=
succ (T Null) := T (Yellow (One Hole) Null);
succ (T (Green (Zero ones) t)) := T (Yellow (One ones) t);
succ (T (Yellow (One ones) t)) := T (ensure_green (Red (Two ones) (ensure_green t))).

Fixpoint seq_to_nat_pow {C} (s : seq C) : nat * nat :=
  match s with
  | Hole => (0, 1)
  | Zero ones => 
      let (n, pow) := seq_to_nat_pow ones in 
      (2 * n, 2 * pow)
  | One  ones => 
      let (n, pow) := seq_to_nat_pow ones in 
      (1 + 2 * n, 2 * pow)
  | Two  ones => 
      let (n, pow) := seq_to_nat_pow ones in 
      (2 + 2 * n, 2 * pow)
  end.

Fixpoint tree_to_nat_pow {C} (t : tree C) : nat * nat :=
  match t with 
  | Null => (0, 1)
  | Green s t | Yellow s t | Red s t => 
    let (n1, pow1) := seq_to_nat_pow s in 
    let (n2, pow2) := tree_to_nat_pow t in 
    (n1 + pow1 * n2, pow1 * pow2)
  end.

Definition nbr_to_nat (n : nbr) : nat := 
  match n with 
  | T t => fst (tree_to_nat_pow t)
  end.

Lemma valid_ensure_green_red_hole_green {G Y R} (ones : seq (PColor PNotGreen Y PNotRed)) (t : tree (PColor G PNotYellow R)) : fst (tree_to_nat_pow (Green (Zero (One ones)) t)) = fst (tree_to_nat_pow (Red (Two Hole) (Green (Zero ones) t))).
Proof.
  simpl.
  remember (seq_to_nat_pow ones) as res_ones; destruct res_ones as [n1 pow1].
  remember (tree_to_nat_pow t) as res_t; destruct res_t as [n2 pow2].
  f_equal. f_equal; lia.
Qed.

Lemma valid_ensure_green_red_ones {Y} (ones : seq (PColor PNotGreen Y PNotRed)) (t : tree is_green) : fst (tree_to_nat_pow (Green (Zero Hole) (Red (Two ones) t))) = fst (tree_to_nat_pow (Red (Two (One ones)) t)).
Proof.
  simpl. 
  remember (seq_to_nat_pow ones) as res_ones; destruct res_ones as [n1 pow1].
  remember (tree_to_nat_pow t) as res_t; destruct res_t as [n2 pow2].
  f_equal. f_equal; lia.
Qed.    

Equations valid_ensure_green {G R} (t : tree (PColor G PNotYellow R)) : fst (tree_to_nat_pow (ensure_green t)) = fst (tree_to_nat_pow t) :=
valid_ensure_green Null := eq_refl;
valid_ensure_green (Green zero t) := eq_refl;
valid_ensure_green (Red (Two Hole) Null) := eq_refl;
valid_ensure_green (Red (Two Hole) (Green (Zero ones) t)) := valid_ensure_green_red_hole_green ones t;
valid_ensure_green (Red (Two (One ones)) t) := valid_ensure_green_red_ones ones t.

Lemma valid_succ_green {G Y R} (ones : seq (PColor PNotGreen Y PNotRed)) (t : tree (PColor G PNotYellow R)) : 
  nbr_to_nat (T (Yellow (One ones) t)) = S (nbr_to_nat (T (Green (Zero ones) t))).
Proof.
  simpl. 
  remember (seq_to_nat_pow ones) as res_ones; destruct res_ones as [n1 pow1].
  remember (tree_to_nat_pow t) as res_t; destruct res_t as [n2 pow2].
  reflexivity.
Qed.

Lemma succ_fst (n m : nat) : S (fst (n, m)) = fst (S n, m).
Proof.
  destruct n; reflexivity.
Qed.

Lemma valid_succ_yellow {G Y R} (ones : seq (PColor PNotGreen Y PNotRed)) (t : tree (PColor G PNotYellow R)) : 
  nbr_to_nat (T (ensure_green (Red (Two ones) (ensure_green t)))) = S (nbr_to_nat (T (Yellow (One ones) t))).
Proof.
  simpl.
  rewrite valid_ensure_green.
  simpl.
  remember (seq_to_nat_pow ones) as res_ones; destruct res_ones as [n1 pow1].
  remember (tree_to_nat_pow t) as res_t; destruct res_t as [n2 pow2].
  remember (tree_to_nat_pow (ensure_green t)) as res_eg_t; destruct res_eg_t as [n2' pow2'].
  rewrite succ_fst. simpl. do 4 f_equal. 
  apply (f_equal fst) in Heqres_t; simpl in Heqres_t.
  apply (f_equal fst) in Heqres_eg_t; simpl in Heqres_eg_t.
  rewrite Heqres_t. rewrite Heqres_eg_t.
  apply valid_ensure_green.
Qed.

Equations valid_succ (n : nbr) : nbr_to_nat (succ n) = S (nbr_to_nat n) :=
valid_succ (T Null) := eq_refl;
valid_succ (T (Green (Zero ones) t)) := valid_succ_green ones t;
valid_succ (T (Yellow (One ones) t)) := valid_succ_yellow ones t.