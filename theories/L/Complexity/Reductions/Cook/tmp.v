Require Import Lia.

Goal forall n, n < 5 -> exists X, n + X = 5.
  intros.
  eexists; split.
  - unfold "<". reflexivity.
  - auto.
Qed.
