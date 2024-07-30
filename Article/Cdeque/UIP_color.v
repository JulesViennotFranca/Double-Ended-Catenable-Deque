From Equations Require Import Equations.
Require Import Coq.Program.Equality.

From Cdeque Require Import types.

Instance UIP_color : UIP color.
Proof.
  intros C1 C2 p q.
  destruct C1 as [G1 Y1 O1 R1].
  destruct C2 as [G2 Y2 O2 R2].
  pose (projg := fun '(Mix g _ _ _) => g).
  pose (projy := fun '(Mix _ y _ _) => y).
  pose (projo := fun '(Mix _ _ o _) => o).
  pose (projr := fun '(Mix _ _ _ r) => r).
  assert (G1 = G2) as Hg. { apply (f_equal projg p). }
  assert (Y1 = Y2) as Hy. { apply (f_equal projy p). }
  assert (O1 = O2) as Ho. { apply (f_equal projo p). }
  assert (R1 = R2) as Hr. { apply (f_equal projr p). }
  destruct Hg. destruct Hy. destruct Ho. destruct Hr.
  dependent destruction p.
  dependent destruction q.
  reflexivity.
Qed.


